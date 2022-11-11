use std::hash::{Hash, Hasher};
use std::{
	collections::HashMap,
	ptr,
	sync::{Arc, RwLock, Weak},
};

use super::namespace::Namespace;
use super::types::TypeRef;
use super::{
	namespace::{Identifier, Name, NamespaceEntry},
	types::Type,
};

#[derive(Debug, Clone)]
pub struct TraitRef {
	pub def: Weak<RwLock<TraitDef>>,
	pub name: Identifier,
	pub args: Vec<(Name, Type)>,
}

#[derive(Debug)]
pub struct TraitDef {
	pub items: HashMap<Name, NamespaceEntry>,
	pub supers: Vec<Identifier>,
}

#[derive(Default, Debug, Clone)]
pub struct TraitImpl {
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

pub fn resolve_obligation<'ctx>(
	ty: &TypeRef,
	tr: &TraitRef,
	namespace: &'ctx Namespace,
	root_namespace: &'ctx Namespace,
) -> Option<&'ctx TraitImpl> {
	None
}
