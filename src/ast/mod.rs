use std::collections::HashMap;

use types::Type;

use crate::{
	lexer::Token,
	parser::ComuneResult,
};

use self::{
	module::{Identifier, ModuleImpl, ModuleInterface, ModuleItemInterface, Name},
	types::BindingProps, semantic::func::validate_function_body
};

pub mod controlflow;
pub mod expression;
pub mod module;
pub mod pattern;
pub mod semantic;
pub mod statement;
pub mod traits;
pub mod types;

// AST & SEMANTIC ANALYSIS
// This module contains structs and impls related to the AST, name resolution, and type validation.

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Attribute {
	pub name: String,
	pub args: Vec<Vec<Token>>,
}

pub fn get_attribute<'a>(attributes: &'a [Attribute], attr_name: &str) -> Option<&'a Attribute> {
	attributes.iter().find(|a| a.name.as_str() == attr_name)
}

pub struct FnScope<'ctx> {
	context: &'ctx ModuleInterface,
	scope: Identifier,
	parent: Option<&'ctx FnScope<'ctx>>,
	fn_return_type: Type,
	variables: HashMap<Name, (Type, BindingProps)>,
	is_inside_loop: bool,
}

impl<'ctx> FnScope<'ctx> {
	pub fn from_parent(parent: &'ctx FnScope, is_loop_block: bool) -> Self {
		FnScope {
			context: parent.context,
			scope: parent.scope.clone(),
			parent: Some(parent),
			fn_return_type: parent.fn_return_type.clone(),
			variables: HashMap::new(),
			is_inside_loop: is_loop_block | parent.is_inside_loop
		}
	}

	pub fn new(context: &'ctx ModuleInterface, scope: Identifier, return_type: Type) -> Self {
		FnScope {
			context,
			scope,
			parent: None,
			fn_return_type: return_type,
			variables: HashMap::new(),
			is_inside_loop: false,
		}
	}

	pub fn find_symbol(
		&self,
		id: &Identifier,
		search_namespace: bool,
	) -> Option<(Identifier, Type)> {
		let mut result = None;

		if !id.is_qualified() {
			// Unqualified name, perform scope-level lookup first
			let local_lookup;

			if self.variables.contains_key(id.name()) {
				local_lookup = Some((
					id.clone(),
					self.variables.get(id.name()).cloned().unwrap().0,
				));
			} else if let Some(parent) = self.parent {
				local_lookup = parent.find_symbol(id, search_namespace);
			} else {
				local_lookup = None;
			}

			if local_lookup.is_some() {
				result = local_lookup;
			}
		}

		if result.is_none() && search_namespace {
			// Look for it in the namespace tree
			self.context.with_item(id, &self.scope, |item, id| {
				if let ModuleItemInterface::Functions(fns) = item {
					if fns.len() == 1 {
						let func = &*fns[0].read().unwrap();

						result = Some((
							id.clone(),

							Type::Function(
								Box::new(func.ret.clone()), 
								func.params.params.iter().map(|(ty, _, props)| (*props, ty.clone())).collect()
							)
						));
					} else {
						todo!("taking address of overloaded function is not yet supported")
					}
				}
			});
		}

		result
	}

	pub fn add_variable(&mut self, t: Type, n: Name, p: BindingProps) {
		self.variables.insert(n, (t, p));
	}
}

pub fn validate_module_impl(
	interface: &ModuleInterface,
	module_impl: &mut ModuleImpl,
) -> ComuneResult<()> {
	for (proto, ast) in &mut module_impl.fn_impls {
		let mut scope = proto.read().unwrap().path.clone();
		scope.path.pop();

		validate_function_body(scope.clone(), &*proto.read().unwrap(), ast, interface)?
	}

	Ok(())
}
