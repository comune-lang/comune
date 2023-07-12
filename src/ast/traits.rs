// Just to shut up rust-analyzer for the time being
#![allow(dead_code, unused_variables)]

use std::hash::{Hash, Hasher};
use std::thread;
use std::time::Duration;
use std::{
	collections::HashMap,
	ptr,
	sync::{Arc, RwLock, Weak},
};

use super::module::ItemRef;
use super::types::{FnPrototype, GenericArgs, GenericParam, Generics};
use super::Attribute;
use super::{
	module::{Identifier, Name},
	types::Type,
};

use lazy_static::lazy_static;

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum LangTrait {
	Sized,
	Copy,
	Send,
	Sync,
}

#[derive(Debug, Clone, Default)]
pub struct TraitRef {
	pub def: Weak<RwLock<TraitInterface>>,
	pub name: Identifier,
	pub args: GenericArgs,
}

#[derive(Debug)]
pub struct TraitInterface {
	pub items: HashMap<Name, Vec<Arc<FnPrototype>>>,
	pub types: HashMap<Name, GenericParam>, // Associated types
	pub supers: Vec<Identifier>,
	pub attributes: Vec<Attribute>,
}

#[derive(Debug, Clone)]
pub struct ImplBlockInterface {
	pub implements: Option<ItemRef<TraitRef>>,
	pub functions: HashMap<Name, Vec<Arc<FnPrototype>>>,
	pub types: HashMap<Name, Type>,
	pub scope: Arc<Identifier>, // The scope used for name resolution within the impl
	pub canonical_root: Identifier, // The root of the canonical names used by items in this impl
	pub params: Generics,
}

impl PartialEq for TraitRef {
	fn eq(&self, other: &Self) -> bool {
		Arc::ptr_eq(&self.def.upgrade().unwrap(), &other.def.upgrade().unwrap())
			&& self.name == other.name
			&& self.args == other.args
	}
}

impl Eq for TraitRef {}

impl Hash for TraitRef {
	fn hash<H: Hasher>(&self, state: &mut H) {
		ptr::hash(self.def.upgrade().unwrap().as_ref(), state);

		self.name.hash(state);

		for arg in &self.args {
			arg.hash(state);
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
	finalized: bool,
	pub impls: Vec<(Arc<RwLock<Type>>, Arc<RwLock<ImplBlockInterface>>)>,
}

impl ImplSolver {
	pub fn new() -> Self {
		Self {
			answer_cache: HashMap::new(),
			finalized: false,
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
		if !self.finalized {
			panic!("finalize the ImplSolver before querying it!");
		}

		if let Type::TypeParam(idx) = ty {
			// Type parameter, check if it has the trait bound

			let Some((_, GenericParam::Type { arg, bounds })) = generics.params.get(*idx) else { panic!() };

			if let Some(concrete) = arg {
				if self.is_trait_implemented(concrete, tr, generics) {
					return true;
				}
			}

			if bounds.iter().any(|param_trait| {
				if let ItemRef::Resolved(param_trait) = param_trait {
					if param_trait == tr {
						return true;
					}
				}
				false
			}) {
				// Type parameter has trait bound, easy result
				return true;
			}

			// Type param doesn't have trait bound, do the normal lookup
		}

		for (im_ty, im) in self.impls.iter() {
			let im_ty = &*im_ty.read().unwrap();
			let im = im.read().unwrap();

			let Some(ItemRef::Resolved(implements)) = &im.implements else {
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
