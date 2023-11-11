// Just to shut up rust-analyzer for the time being
#![allow(dead_code, unused_variables)]

use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::thread;
use std::time::Duration;
use std::{
	collections::HashMap,
	ptr,
	sync::{Arc, RwLock, Weak},
};

use super::types::{FnPrototype, GenericArgs, GenericParam, Generics};
use super::Attribute;
use super::{
	module::{Identifier, Name},
	types::Type,
};

use lazy_static::lazy_static;

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum LangTrait {
	Sized,
	Copy,
	Send,
	Sync,
}

#[derive(Debug, Clone, Default)]
pub struct TraitRef {
	pub def: Option<Weak<RwLock<TraitInterface>>>,
	pub name: Identifier,
	pub scope: Arc<Identifier>,
	pub args: GenericArgs,
}

#[derive(Debug)]
pub struct TraitInterface {
	pub items: HashMap<Name, Vec<Arc<FnPrototype>>>,
	pub generics: Generics,
	pub supers: Vec<Identifier>,
	pub attributes: Vec<Attribute>,
}

#[derive(Debug, Clone)]
pub struct ImplBlockInterface {
	pub implements: Option<TraitRef>,
	pub functions: HashMap<Name, Vec<Arc<FnPrototype>>>,
	pub types: HashMap<Name, Type>,
	pub scope: Arc<Identifier>, // The scope used for name resolution within the impl
	pub canonical_root: Identifier, // The root of the canonical names used by items in this impl
	pub params: Generics,
}

impl TraitRef {
	pub fn unwrap_def(&self) -> Arc<RwLock<TraitInterface>> {
		self.def.as_ref().unwrap().upgrade().unwrap()
	}

	pub fn is_resolved(&self) -> bool {
		self.def.is_some()
	}
}

impl PartialEq for TraitRef {
	fn eq(&self, other: &Self) -> bool {
		Arc::ptr_eq(&self.unwrap_def(), &other.unwrap_def())
			&& self.name == other.name
			&& self.args == other.args
	}
}

impl Eq for TraitRef {}

impl Hash for TraitRef {
	fn hash<H: Hasher>(&self, state: &mut H) {
		if self.is_resolved() {
			"y".hash(state);
			ptr::hash(&*self.unwrap_def().read().unwrap(), state);
		} else {
			"n".hash(state);
			self.name.hash(state);
			self.scope.hash(state);
		}

		"a".hash(state);
		self.args.hash(state);
	}
}

impl Display for TraitRef {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if self.def.is_some() {
			write!(f, "{}", self.name)
		} else {
			write!(f, "`\'{}\'", self.name)
		}
	}
}

// The result of a trait obligation resolution
#[derive(Clone, Debug, Default)]
pub enum TraitDeduction {
	Impl(Arc<RwLock<ImplBlockInterface>>),
	Inherent,
	Opaque,

	#[default]
	None,
}

lazy_static! {
	static ref LANG_TRAITS: RwLock<HashMap<LangTrait, TraitRef>> = RwLock::new(HashMap::new());
}

pub struct ImplDatabase {
	pub impls: Vec<(Type, Arc<RwLock<ImplBlockInterface>>)>,
}

impl ImplDatabase {
	fn new() -> Self {
		ImplDatabase { impls: vec![] }
	}
}

#[derive(Clone, Debug, Default)]
pub struct ImplSolver {
	answer_cache: HashMap<Type, HashMap<TraitRef, TraitDeduction>>,
	pub impls: Vec<(Arc<RwLock<Type>>, Arc<RwLock<ImplBlockInterface>>)>,
}

impl ImplSolver {
	pub fn new() -> Self {
		Self {
			answer_cache: HashMap::new(),
			impls: vec![],
		}
	}

	pub fn register_impl(&mut self, ty: Type, im: ImplBlockInterface) {
		self.impls
			.push((Arc::new(RwLock::new(ty)), Arc::new(RwLock::new(im))));
	}

	pub fn register_lang_trait(&mut self, lang: LangTrait, tr: TraitRef) {
		assert!(
			!LANG_TRAITS.read().unwrap().contains_key(&lang),
			"language trait {lang:?} already registered!"
		);

		LANG_TRAITS.write().unwrap().insert(lang, tr);
	}

	pub fn get_lang_trait(&self, lang_trait: LangTrait) -> TraitRef {
		while !LANG_TRAITS.read().unwrap().contains_key(&lang_trait) {
			thread::sleep(Duration::from_millis(1));
		}

		LANG_TRAITS.write().unwrap()[&lang_trait].clone()
	}

	pub fn is_trait_implemented(&self, ty: &Type, tr: &TraitRef, generics: &Generics) -> bool {
		if let Type::TypeParam(idx) = ty {
			// Type parameter, check if it has the trait bound

			let Some((_, GenericParam::Type { arg, bounds })) = generics.params.get(*idx) else { panic!() };

			if let Some(concrete) = arg {
				if self.is_trait_implemented(concrete, tr, generics) {
					return true;
				}
			}

			if bounds.iter().any(|param_trait| {
				if param_trait == tr {
					return true;
				}
			
				false
			}) {
				// Type parameter has trait bound, easy result
				return true;
			}

			// Type param doesn't have trait bound, do the normal lookup
		}

		if let Some(lang_trait) = self.get_lang_trait_from_ref(tr) {
			if self.check_lang_trait_impl(lang_trait, ty) {
				return true
			}
		}

		for (im_ty, im) in self.impls.iter() {
			let im_ty = &*im_ty.read().unwrap();
			let im = im.read().unwrap();

			let Some(implements) = &im.implements else {
				continue
			};

			if implements != tr || !ty.fits_generic(im_ty) {
				continue;
			}

			if ty == im_ty {
				return true;
			}

			todo!()
		}

		false
	}

	pub fn get_lang_trait_from_ref(&self, tr: &TraitRef) -> Option<LangTrait> {
		let lang_traits = LANG_TRAITS.read().unwrap();
		
		for (lang, def) in lang_traits.iter() {
			if Arc::ptr_eq(&tr.unwrap_def(), &def.unwrap_def()) {
				return Some(*lang)
			}
		}

		None
	}

	pub fn check_lang_trait_impl(
		&self,
		tr: LangTrait,
		ty: &Type
	) -> bool {
		match ty {
			Type::Basic(_) | Type::Pointer(..) => true,
			
			Type::TypeRef { def, args } => {
				let def = def.upgrade().unwrap();
				let def = def.read().unwrap();
				
				match tr {
					LangTrait::Send | LangTrait::Sync => {
						for (_, member, _) in &def.members {
							if !self.check_lang_trait_impl(tr, member) {
								return false
							}
						}

						for (_, variant) in &def.variants {
							// TODO: check variants
						}

						true
					}

					_ => false,
				}
			}
			
			_ => false,
		}		
	}

	pub fn is_impl_applicable(
		&self,
		im: &ImplBlockInterface,
		ty: Type,
		generics: &Generics,
	) -> Option<TraitDeduction> {
		// for a given impl, test if it applies

		None
	}
}
