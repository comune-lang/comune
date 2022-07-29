use std::{cell::RefCell, collections::HashMap};

use super::{NamespaceInfo, types::{Type, InnerType, Typed}, ParserError, ASTResult};


// Did i do it. did i do lifetime annotations right
pub struct Scope<'ctx> {
	context: &'ctx RefCell<NamespaceInfo>,
	parent: Option<&'ctx Scope<'ctx>>,
	fn_return_type: Type,

	variables: HashMap<String, Type>
}


impl<'ctx> Scope<'ctx> {

	pub fn from_parent(parent: &'ctx Scope) -> Self {
		Scope { 
			context: parent.context.clone(), 
			parent: Some(parent), 
			fn_return_type: parent.fn_return_type.clone(), 
			variables: HashMap::new() 
		}
	}

	pub fn new(context: &'ctx RefCell<NamespaceInfo>, return_type: Type) -> Self {
		Scope {
			context, 
			parent: None,
			fn_return_type: return_type,
			variables: HashMap::new(),
		}
	}

	pub fn get_identifier_type(&self, name: &str) -> Option<Type> {
		if self.variables.contains_key(name) {
			self.variables.get(name).cloned()
		} else if let Some(parent) = self.parent {
			parent.get_identifier_type(name)
		} else {
			match self.context.borrow().get_symbol(name) {
				Some((t, _)) => Some(t),
				None => None,
			}
		}
	}

}

pub fn parse_namespace(namespace: &RefCell<NamespaceInfo>) -> ASTResult<()> {

	for (_sym_name, (sym_type, sym_elem)) in &namespace.borrow().symbols {
		let scope = Scope::new(namespace, sym_type.clone());

		let ret = match &sym_type.inner {
			
			InnerType::Function(ret, _) => 
				*ret.clone(),
			
			_ => 
				return Err((ParserError::NotCallable, (0usize, 0usize))), // TODO: Fix
		};

		// Get function block return type, make sure it matches the signature
		if let Some(elem) = sym_elem {
			elem.node.get_return_type(&scope, elem.token_data, &ret)?;
		} else {
			todo!(); // Handle unparsed block? Don't think this should ever happen
		}
	}
	Ok(())
}
