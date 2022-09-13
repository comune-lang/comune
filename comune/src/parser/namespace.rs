use std::{collections::{HashMap, HashSet}, fmt::Display, cell::RefCell};

use mangling::mangle;

use super::{semantic::{Attribute, get_attribute}, errors::CMNError, ParseResult};
use super::{types::{Type, Basic}, ast::ASTElem};



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier {
	pub name: String,
	pub path: ScopePath,
	pub mem_idx: u32,
	pub resolved: Option<String> // Mangled name, resolved during semantic analysis
}

impl Identifier {
	pub fn expect_scopeless(&self) -> ParseResult<String> {
		if self.path.scopes.is_empty() && !self.path.absolute {
			Ok(self.name.clone())
		} else {
			Err(CMNError::ExpectedIdentifier) // TODO: Give appropriate error
		}
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


#[derive(Default, Debug, Clone, PartialEq, Eq)]
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
pub enum NamespaceItem {
	Type(RefCell<Type>),
	Function(RefCell<Type>, RefCell<NamespaceASTElem>),
	Variable(RefCell<Type>, RefCell<NamespaceASTElem>),
	Namespace(Box<RefCell<Namespace>>),
}

type NamespaceEntry = (NamespaceItem, Vec<Attribute>, Option<String>);


#[derive(Default)]
pub struct Namespace {
	pub path: ScopePath,
	pub referenced_modules: HashSet<String>,
	pub imported: Box<Option<Namespace>>,
	pub children: HashMap<String, NamespaceEntry>,
}

impl<'root: 'this, 'this> Namespace {
	
	pub fn new() -> Self {
		let mangle_path = ScopePath::new(true);
		Namespace { 
			// Initialize root namespace with basic types
			path: ScopePath::new(true),
			children: Basic::hashmap().into_iter().map(|(key, val)| 
			(
				key.clone(), 
				(
					NamespaceItem::Type(RefCell::new(val.clone())), 
					vec![], 
					Some(Self::mangle_name(&mangle_path, &key, &val))
				)
			)).collect(),

			referenced_modules: HashSet::new(),
			imported: Box::new(None),
		}
	}


	// Children take temporary ownership of their parent to avoid lifetime hell
	pub fn from_parent(parent: &ScopePath, name: String) -> Self {
		Namespace { 
			children: HashMap::new(),
			path: ScopePath::from_parent(parent, name),

			referenced_modules: HashSet::new(),
			imported: Box::new(None),
		}
	}


	pub fn mangle_name(path: &ScopePath, name: &str, ty: &Type) -> String {
		mangle(format!("{}::{}({})", path.to_string(), name, ty.serialize()).as_bytes())
	}


	// TODO: Replace &'this self with &'this RefCell<Namespace>?
	pub fn with_item(&'this self, name: &Identifier, root: &'root Namespace, mut closure: impl FnMut(&NamespaceEntry, &Namespace) -> ()) -> bool {
		let self_is_root = root as *const _ == self as *const _;

		// If name is an absolute path, look in root
		if name.path.absolute && !self_is_root {
			return root.with_item(name, root, closure);
		}
		
		
		if name.path.scopes.is_empty() {
			if self.children.contains_key(&name.name) {
				closure(&self.children.get(&name.name).unwrap(), &self);
				return true;
			}
		} else {
			if let Some((NamespaceItem::Namespace(child), _, _)) = self.children.get(&name.path.scopes[0]) {
				let mut name_clone = name.clone();
				name_clone.path.scopes.remove(0);
				return child.as_ref().borrow().with_item(&name_clone, root, closure);
			}
		}

		// Didn't find it in our own namespace

		if !self_is_root {
			// We're not root, so search there
			root.with_item(name, root, closure)
		} else {
			false
		}
	}
}


impl Display for Namespace {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {		
		for c in &self.children {
			match &c.1.0 {
				NamespaceItem::Type(t) => write!(f, "\t[type] {}: {}\n", c.0, t.borrow())?,
				NamespaceItem::Function(t, _) => write!(f, "\t[func] {}: {}\n", c.0, t.borrow())?,
				NamespaceItem::Variable(_, _) => todo!(),
				NamespaceItem::Namespace(ns) => write!(f, "\n[[sub-namespace]]\n\n{}\n[[end sub-namespace]]\n\n", &ns.as_ref().borrow())?
				,
			}
		}

		Ok(())
	}
}

