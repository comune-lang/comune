use std::fmt::Display;

use crate::{
	errors::{CMNError, CMNErrorCode},
	parser::AnalyzeResult,
};

use super::{
	expression::{Atom, Expr, NodeData},
	namespace::Name,
	types::{Type, BindingProps},
	FnScope, TokenData,
};

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
	Decl(Vec<(Type, Name, BindingProps)>, Option<Expr>, TokenData),
	Expr(Expr),
}

impl Stmt {
	pub fn validate<'ctx>(&mut self, scope: &mut FnScope<'ctx>) -> AnalyzeResult<Type> {
		match self {
			Stmt::Decl(names, expr, tk) => {
				if names.len() != 1 {
					todo!()
				}

				let (binding_ty, binding_name, bindings_props) = names[0].clone();

				if let Some(expr) = expr {
					binding_ty.validate(scope)?;
					expr.get_node_data_mut().ty = Some(binding_ty.clone());

					let expr_ty = expr.validate(scope)?;

					if expr_ty != binding_ty {
						if expr_ty.is_subtype_of(&binding_ty) {
							expr.wrap_in_cast(binding_ty.clone());
						} else {
							return Err((
								CMNError::new(CMNErrorCode::AssignTypeMismatch {
									expr: expr_ty,
									to: binding_ty,
								}),
								*tk,
							));
						}
					}

					scope.add_variable(binding_ty, binding_name);
					Ok(expr_ty)
				} else {
					scope.add_variable(binding_ty.clone(), binding_name);
					Ok(binding_ty)
				}
			}

			Stmt::Expr(expr) => expr.validate(scope),
		}
	}

	pub fn wrap_in_block(self) -> Expr {
		match self {
			Stmt::Expr(expr) => expr.wrap_in_block(),

			Stmt::Decl(_, _, tk) => Expr::Atom(
				Atom::Block {
					items: vec![self],
					result: None,
				},
				NodeData { ty: None, tk },
			),
		}
	}
}

impl Display for Stmt {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Stmt::Decl(..) => todo!(),
			Stmt::Expr(expr) => expr.fmt(f),
		}
	}
}
