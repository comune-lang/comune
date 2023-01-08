use std::{
	cell::RefCell,
	collections::{HashMap, HashSet},
	fmt::{Debug, Display},
	hash::Hash,
	sync::{Arc, RwLock},
};

use crate::{
	errors::{CMNError, CMNErrorCode},
	parser::ParseResult,
};

use super::{
	expression::Expr,
	traits::{TraitDef, TraitImpl, TraitSolver},
	types::{FnDef, Type, TypeDef},
	Attribute,
};

pub type Name = Arc<str>;

#[derive(Default, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier {
	pub path: Vec<Name>,
	pub absolute: bool,
}

impl Identifier {
	pub fn new(absolute: bool) -> Self {
		Identifier {
			path: vec![],
			absolute,
		}
	}

	pub fn from_name(name: Name, absolute: bool) -> Self {
		Identifier {
			path: vec![name],
			absolute,
		}
	}

	pub fn from_parent(parent: &Identifier, name: Name) -> Self {
		let mut result = parent.clone();
		result.path.push(name);
		result
	}

	pub fn name(&self) -> &Name {
		self.path.last().unwrap()
	}

	pub fn is_qualified(&self) -> bool {
		self.path.len() > 1
	}

	pub fn expect_scopeless(&self) -> ParseResult<&Name> {
		if self.path.len() == 1 && !self.absolute {
			Ok(self.path.last().unwrap())
		} else {
			Err(CMNError::new(CMNErrorCode::ExpectedIdentifier)) // TODO: Give appropriate error
		}
	}
}

impl Display for Identifier {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut result = String::new();

		for scope in &self.path {
			result.push_str(scope);
			if scope != self.path.last().unwrap() {
				result.push_str("::");
			}
		}

		write!(f, "{result}")
	}
}

#[derive(Clone, Debug, PartialEq)]
pub enum NamespaceASTElem {
	Parsed(Expr),
	Unparsed(usize), // Token index
	NoElem,
}

pub type FnOverloadList = Vec<(Arc<RwLock<FnDef>>, RefCell<NamespaceASTElem>)>;

#[derive(Clone, Debug)]
pub enum NamespaceItem {
	Type(Arc<RwLock<TypeDef>>),
	Trait(Arc<RwLock<TraitDef>>),
	// Plural in order to support function overloads
	Functions(FnOverloadList),
	Variable(Type, RefCell<NamespaceASTElem>),
	Alias(Identifier),
}

pub type NamespaceEntry = (NamespaceItem, Vec<Attribute>, Option<String>); // Option<String> is the item's mangled name

#[derive(Default, Clone, Debug)]
pub struct Namespace {
	pub path: Identifier,
	pub referenced_modules: HashSet<Identifier>,
	pub imported: HashMap<Identifier, Namespace>,
	pub children: HashMap<Identifier, NamespaceEntry>,
	pub impls: HashMap<Identifier, HashMap<Name, FnOverloadList>>, // Impls defined in this namespace
	pub trait_impls: HashMap<Identifier, HashMap<Identifier, TraitImpl>>,
	pub trait_solver: TraitSolver,
}

#[derive(Clone)]
pub enum ItemRef<T: Clone> {
	Unresolved { name: Identifier, scope: Identifier },
	Resolved(T),
}

impl<T: Clone> Eq for ItemRef<T> where T: PartialEq + Eq {}

impl<T: Clone> PartialEq for ItemRef<T>
where
	T: PartialEq,
{
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(
				Self::Unresolved {
					name: l0,
					scope: l1,
				},
				Self::Unresolved {
					name: r0,
					scope: r1,
				},
			) => l0 == r0 && l1 == r1,
			(Self::Resolved(l0), Self::Resolved(r0)) => l0 == r0,
			_ => false,
		}
	}
}

impl<T: Clone> Hash for ItemRef<T>
where
	T: Hash,
{
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		match self {
			Self::Unresolved { name, scope } => {
				name.hash(state);
				scope.hash(state);
			}

			Self::Resolved(t) => t.hash(state),
		}
	}
}

impl<T: Clone> Debug for ItemRef<T>
where
	T: Debug,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Unresolved {
				name: arg0,
				scope: arg1,
			} => f.debug_tuple("Unresolved").field(arg0).field(arg1).finish(),
			Self::Resolved(arg0) => f.debug_tuple("Resolved").field(arg0).finish(),
		}
	}
}

impl Namespace {
	pub fn new(path: Identifier) -> Self {
		Namespace {
			// Initialize root namespace with basic types
			path,
			children: HashMap::new(),
			referenced_modules: HashSet::new(),
			imported: HashMap::new(),
			impls: HashMap::new(),
			trait_impls: HashMap::new(),
			trait_solver: TraitSolver::new(),
		}
	}

	pub fn get_interface(&self) -> Self {
		self.clone() // TODO: Actually implement
	}

	pub fn get_item(&self, id: &Identifier) -> Option<&NamespaceItem> {
		match self.children.get(id) {
			Some((NamespaceItem::Alias(alias), ..)) => self.get_item(alias),
			
			Some((item, ..)) => Some(item),
			
			None => {
				if let Some(import) = self.imported.get(&Identifier::from_name(id.path[0].clone(), true)) {
					if id.path.len() > 1 {
						let mut id_sub = id.clone();
						id_sub.path.remove(0);

						return import.get_item(&id_sub)
					}
				}

				None
			}
		}
	}

	pub fn with_item<Ret>(
		&self,
		id: &Identifier,
		scope: &Identifier,
		mut closure: impl FnMut(&NamespaceEntry, &Identifier) -> Ret,
	) -> Option<Ret> {
		if !id.absolute {
			let mut scope_unwind = scope.clone();

			// We "unwind" the scope, iterating through parent scopes and looking for a match
			while !scope_unwind.path.is_empty() {
				let mut scope_lookup_path = scope_unwind.clone();

				scope_lookup_path.path.append(&mut id.clone().path);

				scope_unwind.path.pop();

				if let Some(found_path) = self
					.children
					.keys()
					.find(|item| item.path == scope_lookup_path.path)
				{
					let found_item = &self.children[found_path];

					if let (NamespaceItem::Alias(alias), ..) = found_item {
						return self.with_item(alias, scope, closure);
					} else {
						return Some(closure(found_item, found_path));
					}
				}
			}

			// Didn't find it, fall back to absolute lookup below
		}

		let mut id = id.clone();
		id.absolute = true;

		if let Some(absolute_lookup) = self.children.get(&id) {
			// Found a match for the absolute path in this namespace!

			if let (NamespaceItem::Alias(alias), ..) = absolute_lookup {
				self.with_item(alias, scope, closure)
			} else {
				Some(closure(absolute_lookup, &id))
			}
		} else if let Some(imported) = self.imported.iter().find(|(item, _imported)| {
			id.path.len() > item.path.len() && &id.path[0..item.path.len()] == item.path.as_slice()
		}) {
			// Found an imported namespace that's a prefix of `id`!
			// TODO: Figure out how this works for submodules
			let mut id_relative = id.clone();
			id_relative.path = id_relative.path[imported.0.path.len()..].to_vec();

			imported.1.with_item(&id_relative, scope, closure)
		} else {
			// Nada
			None
		}
	}
}

impl Display for Namespace {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for (name, (item, attribs, mangled)) in &self.children {
			match item {
				NamespaceItem::Alias(id) => writeln!(f, "\t[alias] {}", id)?,
				NamespaceItem::Type(t) => writeln!(f, "\t[type] {}: {}", name, t.read().unwrap())?,
				NamespaceItem::Trait(t) => writeln!(f, "\t[trait] {}: {:?}", name, t.read().unwrap())?,
				
				NamespaceItem::Functions(fs) => {
					for (t, _) in fs {
						writeln!(f, "\t[func] {}: {}", name, t.read().unwrap())?
					}
				}
				
				NamespaceItem::Variable(_, _) => todo!(),
			}
		}
		Ok(())
	}
}
