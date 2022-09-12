use std::{collections::{HashMap, HashSet}, fmt::Display, cell::RefCell, ops::Deref};

use inkwell::attributes;
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


pub enum NamespaceItem {
	Type(RefCell<Type>),
	Function(RefCell<Type>, Option<ASTElem>),
	Variable(RefCell<Type>, Option<ASTElem>),
	Namespace(Box<RefCell<Namespace>>),
}

#[derive(Default)]
pub struct Namespace {
	//pub parent_temp: Option<Box<Namespace>>,
	pub path: ScopePath,

	pub referenced_modules: HashSet<String>,
	pub imported: Box<Option<Namespace>>,

	pub children: HashMap<String, (NamespaceItem, Vec<Attribute>)>,
	
	// Deprecated
	//pub types: HashMap<String, Type>,
	//pub symbols: HashMap<String, (Type, Option<ASTElem>, Vec<Attribute>)>,
	//pub parsed_children: HashMap<String, Namespace>,
}

impl<'root: 'this, 'this> Namespace {
	pub fn new() -> Self {
		Namespace { 
			// Initialize root namespace with basic types
			children: Basic::hashmap().into_iter().map(|(key, val)| (key, (NamespaceItem::Type(RefCell::new(val)), vec![]))).collect(),
			path: ScopePath::new(true),

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

	pub fn get_mangled_name(&self, symbol_name: &str) -> String {
		if let Some((NamespaceItem::Function(symbol_type, _), attributes)) = self.children.get(symbol_name) {
			// Don't mangle if function is root main(), or if it has a no_mangle attribute
			if symbol_name == "main" && self.path.scopes.is_empty() || get_attribute(attributes, "no_mangle").is_some() {
				return symbol_name.to_string();
			}

			mangle(format!("{}::{}({})", self.path.to_string(), symbol_name, symbol_type.borrow().serialize()).as_bytes())
		} else {
			panic!("Invalid symbol name");
		}
	}

	// Try to find a namespace item based on the current namespace visibility 
	pub fn find_item_namespace(&'this self, name: &Identifier, root: &'root Namespace) -> Option<impl Deref<Target = Namespace> + 'this> {
		let self_is_root = root as *const _ == self as *const _;

		// If name is an absolute path, look in root
		if name.path.absolute && !self_is_root {
			return root.find_item_namespace(name, root);
		}
		
		
		if name.path.scopes.is_empty() {
			if self.children.contains_key(&name.name) {
				return Some(self);
			}
		} else {
			//if let Some((NamespaceItem::Namespace(child), _)) = self.children.get(&name.path.scopes[0]) {
			//	return child.borrow().find_item_namespace(name, root);
			//}
		}

		// Didn't find it in our own namespace

		if !self_is_root {
			// We're not root, so search there
			root.find_item_namespace(name, root)
		} else {
			None
		}
	}

	//pub fn find_item(&'this self, name: &Identifier, root: &'root Namespace) -> Option<&'this (NamespaceItem, Vec<Attribute>)> {
	//	self.find_item_namespace(name, root)?.children.get(&name.name)
	//}


	// Get namespace that contains the symbol identified by `name`
	/*pub fn get_symbol_namespace<'a>(&'a self, name: &Identifier, root_namespace: Option<&'a Namespace>) -> Option<&'a Namespace> {
		if name.path.absolute && root_namespace.is_some() {
			return root_namespace.unwrap().get_symbol_namespace(name, None);
		}
		
		if name.path.scopes.is_empty() {
			if self.symbols.contains_key(&name.name) {
				Some(self)
			} else if root_namespace.is_some() && root_namespace.unwrap().symbols.contains_key(&name.name) {
				root_namespace
			} else {
				None
			}
		} else if let Some(child) = self.parsed_children.get(&name.path.scopes[0]) {
			let mut child_path = name.clone();
			child_path.path.scopes.remove(0);
			child.get_symbol_namespace(&child_path, root_namespace)
		} else {
			None
		}
	}

	pub fn get_type_namespace<'a>(&'a self, name: &Identifier, root_namespace: Option<&'a Namespace>) -> Option<&'a Namespace> {
		if name.path.absolute && root_namespace.is_some() {
			return root_namespace.unwrap().get_type_namespace(name, None);
		}
		
		if name.path.scopes.is_empty() {
			if self.types.contains_key(&name.name) {
				Some(self)
			} else if root_namespace.is_some() && root_namespace.unwrap().types.contains_key(&name.name) {
				root_namespace
			} else {
				None
			}
		} else if let Some(child) = self.parsed_children.get(&name.path.scopes[0]) {
			let mut child_path = name.clone();
			child_path.path.scopes.remove(0);
			child.get_type_namespace(&child_path, root_namespace)
		} else {
			None
		}
	}*/

}


impl Display for Namespace {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "children:\n")?;
		
		for c in &self.children {
			match &c.1.0 {
				NamespaceItem::Type(t) => write!(f, "\t[type] {}: {}\n", c.0, t.borrow())?,
				NamespaceItem::Function(t, _) => write!(f, "\t[func] {}: {}\n", c.0, t.borrow())?,
				NamespaceItem::Variable(_, _) => todo!(),
				NamespaceItem::Namespace(_) => todo!(),
			}
		}

		Ok(())
	}
}

