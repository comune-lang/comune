use std::fmt::Display;

use crate::{
	errors::{ComuneErrCode, ComuneError},
	lexer::SrcSpan,
	parser::ComuneResult,
};

use super::{
	expression::Expr,
	module::Name,
	types::{BindingProps, Type},
	FnScope,
};

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
	Decl(Vec<(Type, Name, BindingProps)>, Option<Expr>, SrcSpan),
	Expr(Expr),
}

impl Stmt {
	pub fn validate<'ctx>(&mut self, scope: &mut FnScope<'ctx>) -> ComuneResult<Type> {
		match self {
			Stmt::Decl(names, expr, tk) => {
				if names.len() != 1 {
					todo!()
				}

				let (binding_ty, binding_name, binding_props) = names[0].clone();

				if let Some(expr) = expr {
					binding_ty.validate(scope)?;
					expr.get_node_data_mut().ty = Some(binding_ty.clone());

					let expr_ty = expr.validate(scope)?;

					if expr_ty != binding_ty {
						if expr_ty.is_subtype_of(&binding_ty) {
							expr.wrap_in_cast(binding_ty.clone());
						} else {
							return Err(ComuneError::new(
								ComuneErrCode::AssignTypeMismatch {
									expr: expr_ty,
									to: binding_ty,
								},
								*tk,
							));
						}
					}

					if binding_props.is_ref {
						return Err(ComuneError::new(
							ComuneErrCode::UnstableFeature("ref_locals"),
							*tk,
						));
					}

					scope.add_variable(binding_ty, binding_name, binding_props);
					Ok(expr_ty)
				} else {
					// References must be initialized in their declaration
					if binding_props.is_ref {
						return Err(ComuneError::new(ComuneErrCode::UninitReference, *tk));
					}

					// new& is only allowed in function parameters
					if binding_props.is_new {
						return Err(ComuneError::new(ComuneErrCode::LocalNewReference, *tk));
					}

					scope.add_variable(binding_ty.clone(), binding_name, binding_props);
					Ok(binding_ty)
				}
			}

			Stmt::Expr(expr) => expr.validate(scope),
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
