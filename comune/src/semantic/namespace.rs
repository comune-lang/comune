use std::{
	cell::RefCell,
	collections::{HashMap, HashSet},
	fmt::Display,
	hash::Hash,
	sync::{Arc, RwLock},
};

use mangling::mangle;

use crate::{
	errors::{CMNError, CMNErrorCode},
	parser::ParseResult,
};

use super::{
	ast::ASTElem,
	types::{Type, TypeDef},
	Attribute,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier {
	pub name: String,
	pub path: ScopePath,
	pub mem_idx: u32,
}

impl Identifier {
	pub fn from_name(name: String) -> Self {
		Identifier {
			name,
			path: ScopePath::new(false),
			mem_idx: 0,
		}
	}

	pub fn expect_scopeless(&self) -> ParseResult<String> {
		if self.path.scopes.is_empty() && !self.path.absolute {
			Ok(self.name.clone())
		} else {
			Err(CMNError::new(CMNErrorCode::ExpectedIdentifier)) // TODO: Give appropriate error
		}
	}
}

impl Hash for Identifier {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		// Absolute Identifiers are used to definitively and uniquely identify NamespaceItems in HashMaps.
		// A relative Identifier can't be meaningfully hashed, and doing so indicates a logic error in the code.
		self.name.hash(state);
		self.path.hash(state);
		self.mem_idx.hash(state);
	}
}

impl Display for Identifier {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", {
			let mut result = self.path.to_string();
			result.push_str(&self.name);
			result
		})
	}
}

#[derive(Default, Debug, Clone, PartialEq, Eq, Hash)]
pub struct ScopePath {
	pub scopes: Vec<String>,
	pub absolute: bool,
}

impl ScopePath {
	pub fn new(absolute: bool) -> Self {
		ScopePath {
			scopes: vec![],
			absolute,
		}
	}

	pub fn from_parent(parent: &ScopePath, name: String) -> Self {
		let mut result = ScopePath {
			scopes: parent.scopes.clone(),
			absolute: parent.absolute,
		};
		result.scopes.push(name);
		result
	}
}

impl Display for ScopePath {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut result = if self.absolute {
			"::".to_string()
		} else {
			String::new()
		};

		if !self.scopes.is_empty() {
			for scope in &self.scopes {
				result.push_str(scope);
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
	Function(Arc<RwLock<TypeDef>>, RefCell<NamespaceASTElem>),
	Variable(Type, RefCell<NamespaceASTElem>),
	Namespace(Box<RefCell<Namespace>>),
	Alias(Identifier),
}

pub type NamespaceEntry = (NamespaceItem, Vec<Attribute>, Option<String>); // Option<String> is the item's mangled name

#[derive(Default, Clone, Debug)]
pub struct Namespace {
	pub path: ScopePath,
	pub referenced_modules: HashSet<Identifier>,
	pub imported: HashMap<Identifier, Namespace>,
	pub children: HashMap<String, NamespaceEntry>,
	pub impls: HashMap<
		Identifier,
		Vec<(
			String,
			Arc<RwLock<TypeDef>>,
			RefCell<NamespaceASTElem>,
			Option<String>,
		)>,
	>, // Impls defined in this namespace
}

impl Namespace {
	pub fn new() -> Self {
		Namespace {
			// Initialize root namespace with basic types
			path: ScopePath::new(true),
			children: HashMap::new(),
			referenced_modules: HashSet::new(),
			imported: HashMap::new(),
			impls: HashMap::new(),
		}
	}

	// Children take temporary ownership of their parent to avoid lifetime hell
	pub fn from_parent(parent: &ScopePath, name: String) -> Self {
		Namespace {
			children: HashMap::new(),
			path: ScopePath::from_parent(parent, name),
			referenced_modules: HashSet::new(),
			imported: HashMap::new(),
			impls: HashMap::new(),
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
		if name.path.absolute && !self_is_root {
			return root.with_item(name, root, closure);
		}

		if name.path.scopes.is_empty() {
			if self.children.contains_key(&name.name) {
				// It's one of this namespace's children!

				if let NamespaceItem::Alias(id) = &self.children.get(&name.name).unwrap().0 {
					// It's an alias, so look up the actual item
					return self.with_item(&id, root, closure);
				} else {
					// Generate absolute identifier
					let id = Identifier {
						name: name.name.clone(),
						path: self.path.clone(),
						mem_idx: 0,
					};

					return Some(closure(&self.children.get(&name.name).unwrap(), &id));
				}
			}
		} else {
			if let Some(child) = self.children.get(&name.path.scopes[0]) {
				match &child.0 {
					NamespaceItem::Namespace(child) => {
						// Found child namespace matching first scope path member

						let mut name_clone = name.clone();
						name_clone.path.scopes.remove(0);

						return child
							.as_ref()
							.borrow()
							.with_item(&name_clone, root, closure);
					}

					NamespaceItem::Type(ty) => match &*ty.read().unwrap() {
						TypeDef::Algebraic(alg) => {
							let mut name_clone = name.clone();
							name_clone.path.scopes.remove(0);

							return alg.with_item(&name_clone, self, root, closure);
						}

						_ => panic!(),
					},

					NamespaceItem::Alias(alias_id) => {
						let mut merged_path = alias_id.path.scopes.clone();

						merged_path.append(&mut name.path.scopes.clone());

						return self.with_item(
							&Identifier {
								name: name.name.clone(),
								path: ScopePath {
									scopes: merged_path,
									absolute: alias_id.path.absolute,
								},
								mem_idx: 0,
							},
							root,
							closure,
						);
					}

					_ => panic!(), // TODO: Proper error
				}
			} else if let Some(imported) = self
				.imported
				.get(&Identifier::from_name(name.path.scopes[0].clone()))
			{
				// Found imported namespace matching scope path

				let mut name_clone = name.clone();
				name_clone.path.scopes.remove(0);

				return imported.with_item(&name_clone, imported, closure);
			}
		}

		// Didn't find it in our own namespace

		if !self_is_root {
			root.with_item(name, root, closure)
		} else {
			None
		}
	}
}

impl Display for Namespace {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for c in &self.children {
			match &c.1 .0 {
				NamespaceItem::Alias(id) => write!(f, "\t[alias] {}", id)?,
				NamespaceItem::Type(t) => write!(f, "\t[type] {}: {}\n", c.0, t.read().unwrap())?,
				NamespaceItem::Function(t, _) => {
					write!(f, "\t[func] {}: {}\n", c.0, t.read().unwrap())?
				}
				NamespaceItem::Variable(_, _) => todo!(),
				NamespaceItem::Namespace(ns) => write!(
					f,
					"\n[[sub-namespace]]\n\n{}\n[[end sub-namespace]]\n\n",
					&ns.as_ref().borrow()
				)?,
			}
		}
		Ok(())
	}
}
