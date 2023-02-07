use std::hash::{Hash, Hasher};
use std::{
	collections::HashMap,
	ptr,
	sync::{Arc, RwLock, Weak},
};

use super::namespace::{FnOverloadList, ItemRef, Namespace};
use super::types::{TypeParam, TypeParamList};
use super::{
	namespace::{Identifier, Name},
	types::Type,
};

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
	pub def: Weak<RwLock<TraitDef>>,
	pub name: Identifier,
	pub args: Vec<Type>,
}

#[derive(Debug)]
pub struct TraitDef {
	pub items: HashMap<Name, FnOverloadList>,
	pub types: HashMap<Name, TypeParam>, // Associated types
	pub supers: Vec<Identifier>,
}

#[derive(Debug, Clone)]
pub struct Impl {
	pub implements: Option<ItemRef<TraitRef>>,
	pub items: HashMap<Name, FnOverloadList>,
	pub types: HashMap<Name, Type>,
	pub scope: Identifier, // The scope used for name resolution within the impl
	pub canonical_root: Identifier, // The root of the canonical names used by items in this impl
}

// Safety: see super::namespace.
unsafe impl Send for TraitRef {}
unsafe impl Sync for TraitRef {}

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
	Impl(Arc<RwLock<Impl>>),
	Inherent,
	Opaque,

	#[default]
	None,
}

#[derive(Debug, Default)]
pub struct TraitSolver {
	impls: Vec<(Type, Arc<RwLock<Impl>>)>,
	local_impls: Vec<(RwLock<Type>, Arc<RwLock<Impl>>)>,
	answer_cache: HashMap<Type, HashMap<TraitRef, TraitDeduction>>,
}

impl Clone for TraitSolver {
	fn clone(&self) -> Self {
		let mut result = TraitSolver {
			local_impls: vec![],
			impls: self.impls.clone(),
			answer_cache: self.answer_cache.clone(),
		};

		// Move local_impls into impls
		result.impls.extend(
			self.local_impls
				.iter()
				.map(|(ty, im)| (ty.read().unwrap().clone(), im.clone())),
		);

		result
	}
}

impl TraitSolver {
	pub fn new() -> Self {
		Self {
			impls: vec![],
			local_impls: vec![],
			answer_cache: HashMap::new(),
		}
	}

	pub fn get_local_impls(&self) -> &Vec<(RwLock<Type>, Arc<RwLock<Impl>>)> {
		&self.local_impls
	}

	pub fn register_impl(&mut self, ty: Type, im: Arc<RwLock<Impl>>) {
		self.local_impls.push((RwLock::new(ty), im));
	}

	pub fn type_implements_trait(
		&self,
		ty: &Type,
		tr: &TraitRef,
		type_params: &TypeParamList,
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
		im: &Impl,
		ty: Type,
		type_params: &TypeParamList,
		root: &Namespace,
	) -> Option<TraitDeduction> {
		// for a given impl, test if it applies

		None
	}
}
