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

#[derive(Default, Debug, Clone)]
pub struct TraitImpl {
	pub implements: TraitRef,
	pub items: HashMap<Name, NamespaceEntry>,
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
	Impl(Arc<RwLock<TraitImpl>>),
	Inherent,
	Opaque,

	#[default]
	None,
}
#[derive(Clone, Debug)]
pub enum ImplRule {
	Implements(TraitRef),
	Equivalent(Type), 		// Equivalence, aka equality with subtyping and aliases permitted
}

#[derive(Clone, Debug, Default)]
pub struct TraitSolver {
	rules: HashMap<TraitRef, Vec<(Vec<ImplRule>, Arc<RwLock<TraitImpl>>)>>,
	answers: HashMap<Type, TraitDeduction>,
}

impl TraitSolver {
	pub fn new() -> Self {
		Self {
			rules: HashMap::new(),
			answers: HashMap::new(),
		}
	}

	pub fn register_impl(&mut self, tr: Arc<RwLock<TraitImpl>>) {

	}
	
	pub fn resolve_obligation(
		&mut self,
		ty: &Type,
		tr: &TraitRef,
		type_params: &TypeParamList,
		root: &Namespace,
	) -> Option<TraitDeduction> {
		// trait solver - deduce whether a trait implementation exists and is visible
		if let Some(answer) = self.answers.get(ty) {
			return Some(answer.clone())
		}
		
		None
	}

}