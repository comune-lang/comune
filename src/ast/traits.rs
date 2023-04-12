// Just to shut up rust-analyzer for the time being
#![allow(dead_code, unused_variables)]

use std::hash::{Hash, Hasher};
use std::{
	collections::HashMap,
	ptr,
	sync::{Arc, RwLock, Weak},
};

use crate::parser::ComuneResult;

use super::module::ItemRef;
use super::types::{FnPrototype, GenericParam, Generics};
use super::Attribute;
use super::{
	module::{Identifier, Name},
	types::Type,
};

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum LangTrait {
	Sized,
	Copy,
	Clone,
	Drop,
	Send,
	Sync,
}

#[derive(Debug, Clone, Default)]
pub struct TraitRef {
	pub def: Weak<RwLock<TraitInterface>>,
	pub name: Identifier,
	pub args: Vec<Type>,
}

#[derive(Debug)]
pub struct TraitInterface {
	pub items: HashMap<Name, Vec<Arc<RwLock<FnPrototype>>>>,
	pub types: HashMap<Name, GenericParam>, // Associated types
	pub supers: Vec<Identifier>,
	pub attributes: Vec<Attribute>,
}

#[derive(Debug, Clone)]
pub struct ImplBlockInterface {
	pub implements: Option<ItemRef<TraitRef>>,
	pub functions: HashMap<Name, Vec<Arc<RwLock<FnPrototype>>>>,
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

#[derive(Clone, Debug, Default)]
pub struct ImplSolver {
	lang_traits: HashMap<LangTrait, TraitRef>,
	impls: Vec<(Type, Arc<RwLock<ImplBlockInterface>>)>,
	answer_cache: HashMap<Type, HashMap<TraitRef, TraitDeduction>>,
	pub local_impls: Vec<(Arc<RwLock<Type>>, Arc<RwLock<ImplBlockInterface>>)>,
}

impl ImplSolver {
	pub fn new() -> Self {
		Self {
			lang_traits: HashMap::new(),
			impls: vec![],
			local_impls: vec![],
			answer_cache: HashMap::new(),
		}
	}

	pub fn join_imported_solver(&mut self, imported: &ImplSolver) -> ComuneResult<()> {
		for (key, lang_trait) in &imported.lang_traits {
			if !self.lang_traits.contains_key(key) {
				self.lang_traits.insert(key.clone(), lang_trait.clone());
			}
		}

		Ok(())
	}

	pub fn finalize(&mut self) {
		// Move local_impls into impls
		self.impls.extend(
			self.local_impls
				.iter()
				.map(|(ty, im)| (ty.read().unwrap().clone(), im.clone())),
		);
	}

	pub fn register_impl(&mut self, ty: Type, im: ImplBlockInterface) {
		self.local_impls
			.push((Arc::new(RwLock::new(ty)), Arc::new(RwLock::new(im))));
	}

	pub fn register_lang_trait(&mut self, lang: LangTrait, tr: TraitRef) {
		assert!(
			!self.lang_traits.contains_key(&lang),
			"language trait {lang:?} already registered!"
		);

		self.lang_traits.insert(lang, tr);
	}

	pub fn get_lang_trait(&self, lang_trait: LangTrait) -> TraitRef {
		self.lang_traits[&lang_trait].clone()
	}

	pub fn is_trait_implemented(&self, ty: &Type, tr: &TraitRef, generics: &Generics) -> bool {
		if !self.local_impls.is_empty() {
			panic!("finalize the ImplSolver before querying it!");
		}

		match ty {
			Type::TypeParam(idx) => {
				let Some((_, param, concrete)) = generics.get(*idx) else { panic!() };

				if let Some(concrete) = concrete {
					if self.is_trait_implemented(concrete, tr, generics) {
						return true;
					}
				}

				param.iter().any(|param_trait| {
					if let ItemRef::Resolved(param_trait) = param_trait {
						if param_trait == tr {
							return true;
						}
					}
					false
				})
			}

			_ => {
				for (im_ty, im) in self.impls.iter() {}

				false
			}
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
