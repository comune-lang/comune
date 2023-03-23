use std::hash::{Hash, Hasher};
use std::{
	collections::HashMap,
	ptr,
	sync::{Arc, RwLock, Weak},
};

use super::module::{ItemRef, ModuleImpl};
use super::types::{FnPrototype, GenericParamList, TypeParam};
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
	pub types: HashMap<Name, TypeParam>, // Associated types
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
	pub params: GenericParamList,
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
	pub local_impls: Vec<(Arc<RwLock<Type>>, Arc<RwLock<ImplBlockInterface>>)>,
	answer_cache: HashMap<Type, HashMap<TraitRef, TraitDeduction>>,
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

	pub fn type_implements_trait(
		&self,
		ty: &Type,
		tr: &TraitRef,
		type_params: &GenericParamList,
	) -> bool {
		match ty {
			Type::TypeParam(idx) => {
				let Some((_, param, concrete)) = type_params.get(*idx) else { panic!() };

				if let Some(concrete) = concrete {
					if self.type_implements_trait(concrete, tr, type_params) {
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

			_ => todo!(),
		}
	}

	pub fn is_impl_applicable(
		&mut self,
		im: &ImplBlockInterface,
		ty: Type,
		type_params: &GenericParamList,
		root: &ModuleImpl,
	) -> Option<TraitDeduction> {
		// for a given impl, test if it applies

		None
	}
}
