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
	ast::ASTElem,
	traits::{TraitDef, TraitImpl},
	types::{FnDef, Type, TypeDef},
	Attribute,
};

pub type Name = Arc<str>;

#[derive(Default, Debug, Clone, PartialEq, Eq)]
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

impl Hash for Identifier {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		// Absolute Identifiers are used to definitively and uniquely identify NamespaceItems in HashMaps.
		// A relative Identifier can't be meaningfully hashed, and doing so indicates a logic error in the code.
		self.path.hash(state);
		self.absolute.hash(state);
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
	Parsed(ASTElem),
	Unparsed(usize), // Token index
	NoElem,
}

// refcell hell
#[derive(Clone, Debug)]
pub enum NamespaceItem {
	Type(Arc<RwLock<TypeDef>>),
	Trait(Arc<RwLock<TraitDef>>),
	Function(Arc<RwLock<FnDef>>, RefCell<NamespaceASTElem>),
	Variable(Type, RefCell<NamespaceASTElem>),
	//Namespace(Box<RefCell<Namespace>>),
	Alias(Identifier),
}

pub type NamespaceEntry = (NamespaceItem, Vec<Attribute>, Option<String>); // Option<String> is the item's mangled name

#[derive(Default, Clone, Debug)]
pub struct Namespace {
	pub path: Identifier,
	pub referenced_modules: HashSet<Identifier>,
	pub imported: HashMap<Identifier, Namespace>,
	pub children: HashMap<Identifier, NamespaceEntry>,
	pub impls: HashMap<Identifier, HashMap<Name, NamespaceEntry>>, // Impls defined in this namespace
	pub trait_impls: HashMap<Identifier, HashMap<Identifier, TraitImpl>>,
}

#[derive(Clone)]
pub enum ItemRef<T: Clone> {
	Unresolved{ name: Identifier, scope: Identifier },
	Resolved(T),
}

impl<T: Clone> Eq for ItemRef<T> where T: PartialEq + Eq {}
impl<T: Clone> PartialEq for ItemRef<T>
where
	T: PartialEq + Eq,
{
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(Self::Unresolved { name: l0, scope: l1 }, Self::Unresolved { name: r0, scope: r1 }) => l0 == r0 && l1 == r1,
			(Self::Resolved(l0), Self::Resolved(r0)) => l0 == r0,
			_ => false,
		}
	}
}

impl<T: Clone> Debug for ItemRef<T>
where
	T: Debug,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Unresolved { name: arg0, scope: arg1 } => f.debug_tuple("Unresolved").field(arg0).field(arg1).finish(),
			Self::Resolved(arg0) => f.debug_tuple("Resolved").field(arg0).finish(),
		}
	}
}

impl<T> ItemRef<T>
where
	T: Clone,
{
	fn resolved(&self) -> Option<&T> {
		if let ItemRef::Resolved(item) = self {
			Some(item)
		} else {
			None
		}
	}

	fn resolved_mut(&mut self) -> Option<&mut T> {
		if let ItemRef::Resolved(item) = self {
			Some(item)
		} else {
			None
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
		}
	}

	pub fn get_interface(&self) -> Self {
		self.clone() // TODO: Actually implement
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

					if let NamespaceItem::Alias(alias) = &found_item.0 {
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

			if let NamespaceItem::Alias(alias) = &absolute_lookup.0 {
				self.with_item(alias, scope, closure)
			} else {
				Some(closure(absolute_lookup, &id))
			}
		} else if let Some(imported) = self.imported.iter().find(|(item, imported)| {
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

	// Children take temporary ownership of their parent to avoid lifetime hell
	/*pub fn from_parent(parent: &Identifier, name: Name) -> Self {
		Namespace {
			children: HashMap::new(),
			path: Identifier::from_parent(parent, name),
			referenced_modules: HashSet::new(),
			imported: HashMap::new(),
			impls: HashMap::new(),
			trait_impls: HashMap::new(),
		}
	}

	pub fn with_item<Ret>(
		&self,
		name: &Identifier,
		root: &Namespace,
		mut closure: impl FnMut(&NamespaceEntry, &Identifier) -> Ret,
	) -> Option<Ret> {
		let self_is_root = root as *const _ == self as *const _;

		// If name is an absolute path, look in root
		if name.absolute && !self_is_root {
			return root.with_item(name, root, closure);
		}

		if !name.is_qualified() {
			if self.children.contains_key(name.name()) {
				// It's one of this namespace's children!

				if let NamespaceItem::Alias(id) = &self.children.get(name.name()).unwrap().0 {
					// It's an alias, so look up the actual item
					return self.with_item(&id, root, closure);
				} else {
					// Generate absolute identifier
					let id = Identifier::from_parent(&self.path, name.name().clone());

					return Some(closure(&self.children.get(name.name()).unwrap(), &id));
				}
			}
		} else {
			if let Some(child) = self.children.get(&name.path[0]) {
				match &child.0 {
					NamespaceItem::Namespace(child) => {
						// Found child namespace matching first scope path member

						let mut name_clone = name.clone();
						name_clone.path.remove(0);

						return child
							.as_ref()
							.borrow()
							.with_item(&name_clone, root, closure);
					}

					NamespaceItem::Type(ty) => match &*ty.read().unwrap() {
						TypeDef::Algebraic(alg) => {
							let mut name_clone = name.clone();
							name_clone.path.remove(0);

							return alg.with_item(&name_clone, self, root, closure);
						}

						_ => panic!(),
					},

					NamespaceItem::Alias(alias_id) => {
						let mut merged_path = alias_id.path.clone();

						merged_path.append(&mut name.path.clone());

						return self.with_item(
							&Identifier {
								path: merged_path,
								absolute: alias_id.absolute,
							},
							root,
							closure,
						);
					}

					_ => panic!(), // TODO: Proper error
				}
			} else if let Some(imported) = self
				.imported
				.get(&Identifier::from_name(name.path[0].clone(), false))
			{
				// Found imported namespace matching scope path

				let mut name_clone = name.clone();
				name_clone.path.remove(0);

				return imported.with_item(&name_clone, imported, closure);
			}
		}

		// Didn't find it in our own namespace

		if !self_is_root {
			root.with_item(name, root, closure)
		} else {
			None
		}
	}*/
}

impl Display for Namespace {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for c in &self.children {
			match &c.1 .0 {
				NamespaceItem::Alias(id) => write!(f, "\t[alias] {}\n", id)?,
				NamespaceItem::Type(t) => write!(f, "\t[type] {}: {}\n", c.0, t.read().unwrap())?,
				NamespaceItem::Trait(t) => {
					write!(f, "\t[trait] {}: {:?}\n", c.0, t.read().unwrap())?
				}
				NamespaceItem::Function(t, _) => {
					write!(f, "\t[func] {}: {}\n", c.0, t.read().unwrap())?
				}
				NamespaceItem::Variable(_, _) => todo!(),
			}
		}
		Ok(())
	}
}
