use std::{collections::{HashMap, HashSet}, fmt::Display};

use mangling::mangle;
use super::semantic::{Attribute, get_attribute};
use super::{types::{Type, Basic}, ast::ASTElem};



#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Identifier {
	pub name: String,
	pub path: ScopePath,
	pub mem_idx: u32,
	pub resolved: Option<String> // Mangled name, resolved during semantic analysis
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

#[derive(Default)]
pub struct Namespace {
	pub types: HashMap<String, Type>,
	pub symbols: HashMap<String, (Type, Option<ASTElem>, Vec<Attribute>)>,
	pub parsed_children: HashMap<String, Namespace>,
	pub parent_temp: Option<Box<Namespace>>,
	pub path: ScopePath,

	pub referenced_modules: HashSet<String>,
	pub imported: Box<Option<Namespace>>,
}

impl Namespace {
	pub fn new() -> Self {
		Namespace { 
			types: HashMap::new(), 
			symbols: HashMap::new(),
			parsed_children: HashMap::new(),
			parent_temp: None,
			path: ScopePath::new(true),

			referenced_modules: HashSet::new(),
			imported: Box::new(None),
		}
	}

	// Children take temporary ownership of their parent to avoid lifetime hell
	pub fn from_parent(parent: Box<Namespace>, name: String) -> Self {
		Namespace { 
			types: HashMap::new(), 
			symbols: HashMap::new(),
			parsed_children: HashMap::new(),
			path: ScopePath::from_parent(&parent.path.clone(), name),
			parent_temp: Some(parent),

			referenced_modules: HashSet::new(),
			imported: Box::new(None),
		}
	}


	pub fn get_type(&self, name: &str) -> Option<Type> {
		if let Some(basic) = Basic::get_basic_type(name) {
			Some(Type::from_basic(basic))
		} else if self.types.contains_key(name) {
			self.types.get(name).cloned()
		} else {
			let scope_op_idx = name.find("::");
			
			if let Some(idx) = scope_op_idx {
				if self.parsed_children.contains_key(&name[..idx]) {
					return self.parsed_children.get(&name[..idx]).unwrap().get_type(&name[idx+2..]);
				}
			}

			None
		}
	}

	pub fn get_mangled_name(&self, symbol_name: &str, attributes: &Vec<Attribute>) -> String {
		if let Some(symbol) = self.symbols.get(symbol_name) {
			// Don't mangle if function is root main(), or if it has a no_mangle attribute
			if symbol_name == "main" && self.path.scopes.is_empty() || get_attribute(attributes, "no_mangle").is_some() {
				return symbol_name.to_string();
			}

			mangle(format!("{}::{}({})", self.path.to_string(), symbol_name, symbol.0.serialize()).as_bytes())
		} else {
			panic!("Invalid symbol name");
		}
	}


	pub fn get_symbol(&self, name: &str) -> Option<&(Type, Option<ASTElem>, Vec<Attribute>)> {
		if self.symbols.contains_key(name) {
			self.symbols.get(name)
		} else {
			let scope_op_idx = name.find("::");
			
			if let Some(idx) = scope_op_idx {
				if self.parsed_children.contains_key(&name[..idx]) {
					return self.parsed_children.get(&name[..idx]).unwrap().get_symbol(&name[idx+2..]);
				}
			}

			None
		}
	}
}


impl Display for Namespace {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "types:\n")?;
		
		for t in &self.types {
			write!(f, "\t{}: {}\n", t.0, t.1)?;
		}
		
		write!(f, "\nsymbols:\n")?;
		
		for t in &self.symbols {
			write!(f, "\t{}: {}\n", t.0, t.1.0)?;
		}

		Ok(())
	}
}

