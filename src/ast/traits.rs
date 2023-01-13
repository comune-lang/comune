use std::hash::{Hash, Hasher};
use std::{
	collections::HashMap,
	ptr,
	sync::{Arc, RwLock, Weak},
};

use super::namespace::{Namespace, ItemRef, FnOverloadList};
use super::types::{TypeRef, TypeParam, TypeParamList};
use super::{
	namespace::{Identifier, Name, NamespaceEntry},
	types::Type,
};

#[derive(Debug, Clone, Default)]
pub struct TraitRef {
	pub def: Weak<RwLock<TraitDef>>,
	pub name: Identifier,
	pub args: Vec<(Name, Type)>,
}

#[derive(Debug)]
pub struct TraitDef {
	pub items: HashMap<Name, FnOverloadList>,
	pub types: HashMap<Name, TypeParam>,		// Associated types
	pub supers: Vec<Identifier>,
}

#[derive(Debug, Clone)]
pub struct Impl {
	pub implements: Option<ItemRef<TraitRef>>,
	pub items: HashMap<Name, FnOverloadList>,
	pub types: HashMap<Name, Type>,
	pub scope: Identifier,
}

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

		for (name, arg) in &self.args {
			name.hash(state);
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

#[derive(Clone, Debug, Default)]
pub struct TraitSolver {
	impls: Vec<(Type, Arc<RwLock<Impl>>)>,
	answer_cache: HashMap<Type, HashMap<TraitRef, TraitDeduction>>,
}

impl TraitSolver {
	pub fn new() -> Self {
		Self {
			impls: vec![],
			answer_cache: HashMap::new(),
		}
	}

	pub fn get_impls(&self) -> &Vec<(Type, Arc<RwLock<Impl>>)> {
		&self.impls
	}

	pub fn register_impl(&mut self, ty: Type, im: Arc<RwLock<Impl>>) {
		if let Some(cache) = self.answer_cache.get_mut(&ty) {
			cache.clear();
		}

		self.impls.push((ty, im));
	}

	pub fn type_implements_trait(&self, ty: &Type, tr: &TraitRef, type_params: &TypeParamList) -> bool {
		match ty {
			Type::TypeParam(idx) => {
				let Some((_, param)) = type_params.get(*idx) else { panic!() };

				param.iter().any(|param_trait| {
					if let ItemRef::Resolved(param_trait) = param_trait {
						if param_trait == tr {
							return true
						}
					}
					false
				})
			}

			_ => todo!()
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