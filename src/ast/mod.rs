use types::Type;

use crate::lexer::Token;

use self::{
	module::{Identifier, ModuleInterface, ModuleItemInterface, Name},
	types::{BindingProps, Generics},
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

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
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
	fn_return_type: (BindingProps, Type),
	variables: Vec<(Name, Type, BindingProps)>,
	is_inside_loop: bool,
	is_unsafe: bool,
	generics: Generics,
}

impl<'ctx> FnScope<'ctx> {
	pub fn from_parent(parent: &'ctx FnScope, is_loop_block: bool, is_unsafe: bool) -> Self {
		FnScope {
			context: parent.context,
			scope: parent.scope.clone(),
			parent: Some(parent),
			fn_return_type: parent.fn_return_type.clone(),
			variables: vec![],
			is_inside_loop: is_loop_block | parent.is_inside_loop,
			is_unsafe: is_unsafe | parent.is_unsafe,
			generics: Generics::new(),
		}
	}

	pub fn new(
		context: &'ctx ModuleInterface,
		scope: Identifier,
		ret: (BindingProps, Type),
	) -> Self {
		FnScope {
			context,
			scope,
			parent: None,
			fn_return_type: ret,
			variables: vec![],
			is_inside_loop: false,
			is_unsafe: false,
			generics: Generics::new(),
		}
	}

	pub fn with_params(mut self, mut params: Generics) -> Self {
		self.generics.params.append(&mut params.params);
		self
	}

	pub fn find_type(&self, id: &Identifier) -> Option<Type> {
		if !id.is_scoped() {
			for (i, (name, ..)) in self.generics.params.iter().enumerate().rev() {
				if name == id.name() {
					return Some(Type::TypeParam(i));
				}
			}
		}

		self.context.resolve_type(id, &self.scope)
	}

	pub fn find_symbol(
		&self,
		id: &Identifier,
		search_namespace: bool,
	) -> Option<(Identifier, Type)> {
		let mut result = None;

		if !id.is_scoped() {
			// Unqualified name, perform scope-level lookup first
			let local_lookup;

			if let Some((_, ty, _)) = self
				.variables
				.iter()
				.rev()
				.find(|(name, ..)| name == id.name())
			{
				local_lookup = Some((id.clone(), ty.clone()));
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
					if let [func] = fns.read().unwrap().as_slice() {
						result = Some((
							id.clone(),
							Type::Function(
								Box::new(func.ret.1.clone()),
								func.params
									.params
									.iter()
									.map(|(ty, _, props)| (*props, ty.clone()))
									.collect(),
							),
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
		self.variables.push((n, t, p));
	}
}

macro_rules! write_arg_list {
	($buffer:ident, $args:ident, $open:literal, $close:literal) => {
		if $args.is_empty() {
			write!($buffer, "{}{}", $open, $close).unwrap();
		} else {
			let mut iter = $args.iter();
			
			write!($buffer, "{}{}", $open, iter.next().unwrap()).unwrap();
			
			for arg in iter {
				write!($buffer, ", {arg}").unwrap();
			}

			write!($buffer, "{}", $close).unwrap();
		}
	};
}

pub(crate) use write_arg_list;