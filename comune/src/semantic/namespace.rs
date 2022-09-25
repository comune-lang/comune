use std::{collections::{HashMap, HashSet}, fmt::Display, cell::RefCell, hash::Hash, sync::{Arc, RwLock}};

use mangling::mangle;

use crate::{parser::ParseResult, errors::CMNError};

use super::{types::{Type, TypeDef}, ast::ASTElem, Attribute};



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier {
	pub name: String,
	pub path: ScopePath,
	pub mem_idx: u32,
	pub resolved: Option<String> // Mangled name, resolved during semantic analysis
}

impl Identifier {
	pub fn from_name(name: String) -> Self {
		Identifier {
			name,
			path: ScopePath::new(false),
			mem_idx: 0,
			resolved: None,
		}
	}

	pub fn expect_scopeless(&self) -> ParseResult<String> {
		if self.path.scopes.is_empty() && !self.path.absolute {
			Ok(self.name.clone())
		} else {
			Err(CMNError::ExpectedIdentifier) // TODO: Give appropriate error
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
        self.resolved.hash(state);
    }
}


impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", if self.path.scopes.is_empty() {
			self.name.clone()
		} else {
			let mut result = self.path.to_string();
			result.push_str("::");
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
		ScopePath { scopes: vec![], absolute }
	}

	pub fn from_parent(parent: &ScopePath, name: String) -> Self {
		let mut result = ScopePath { scopes: parent.scopes.clone(), absolute: parent.absolute };
		result.scopes.push(name);
		result
	}
}


impl ToString for ScopePath {
    fn to_string(&self) -> String {
		if self.scopes.is_empty() { return String::new(); }
		let mut iter = self.scopes.iter();
        let mut result = iter.next().unwrap().clone();
		for scope in iter {
			result.push_str("::");
			result.push_str(scope);
		}
		result
    }
}


#[derive(Clone, Debug, PartialEq)]
pub enum NamespaceASTElem {
	Parsed(ASTElem),
	Unparsed(usize), // Token index
	NoElem,
}

// refcell hell
#[derive(Clone)]
pub enum NamespaceItem {
	Type(Arc<RwLock<TypeDef>>),
	Function(Arc<RwLock<TypeDef>>, RefCell<NamespaceASTElem>),
	Variable(Type, RefCell<NamespaceASTElem>),
	Namespace(Box<RefCell<Namespace>>),
	Alias(Identifier),
}

type NamespaceEntry = (NamespaceItem, Vec<Attribute>, Option<String>); // Option<String> is the item's mangled name


#[derive(Default, Clone)]
pub struct Namespace {
	pub path: ScopePath,
	pub referenced_modules: HashSet<Identifier>,
	pub imported: HashMap<Identifier, Namespace>,
	pub children: HashMap<String, NamespaceEntry>,
	pub impls: HashMap<Identifier, Vec<(String, Arc<RwLock<TypeDef>>, RefCell<NamespaceASTElem>, Option<String>)>>, // Impls defined in this namespace
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


	pub fn mangle_name(path: &ScopePath, name: &str, ty: &TypeDef) -> String {
		mangle(format!("{}::{}({})", path.to_string(), name, ty.serialize()).as_bytes())
	}


	pub fn with_item<Ret>(&self, name: &Identifier, root: &Namespace, mut closure: impl FnMut(&NamespaceEntry, &Namespace, &Identifier) -> Ret) -> Option<Ret> {
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
					let id = Identifier {name: name.name.clone(), path: self.path.clone(), mem_idx: 0, resolved: None };
				
					return Some(closure(&self.children.get(&name.name).unwrap(), &self, &id));
				}
			}
		} else {
			if let Some((NamespaceItem::Namespace(child), _, _)) = self.children.get(&name.path.scopes[0]) {

				// Found child namespace matching first scope path member

				let mut name_clone = name.clone();
				name_clone.path.scopes.remove(0);

				return child.as_ref().borrow().with_item(&name_clone, root, closure);

			} else if let Some(imported) = self.imported.get(&Identifier::from_name(name.path.scopes[0].clone()))  {

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
			match &c.1.0 {
				NamespaceItem::Alias(id) => write!(f, "\t[alias] {}", id)?,
				NamespaceItem::Type(t) => write!(f, "\t[type] {}: {}\n", c.0, t.read().unwrap())?,
				NamespaceItem::Function(t, _) => write!(f, "\t[func] {}: {}\n", c.0, t.read().unwrap())?,
				NamespaceItem::Variable(_, _) => todo!(),
				NamespaceItem::Namespace(ns) => write!(f, "\n[[sub-namespace]]\n\n{}\n[[end sub-namespace]]\n\n", &ns.as_ref().borrow())?,
			}
		}
		Ok(())
	}
}

