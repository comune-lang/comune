use crate::{
	ast::statement::Stmt,
	errors::{ComuneErrCode, ComuneError},
	parser::ComuneResult,
};

use crate::ast::{types::Type, FnScope};

impl Stmt {
	pub fn validate<'ctx>(&mut self, scope: &mut FnScope<'ctx>) -> ComuneResult<Type> {
		match self {
			Stmt::Decl(names, expr, span) => {
				if names.len() != 1 {
					todo!()
				}

				let (binding_ty, binding_name, binding_props) = names[0].clone();
				binding_ty.validate(scope)?;

				if let Some(expr) = expr {
					expr.set_type_hint(binding_ty.clone());

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
								*span,
							));
						}
					}

					if binding_props.is_ref {
						return Err(ComuneError::new(
							ComuneErrCode::UnstableFeature("ref_locals"),
							*span,
						));
					}

					scope.add_variable(binding_ty, binding_name, binding_props);
					Ok(expr_ty)
				} else {
					// References must be initialized in their declaration
					if binding_props.is_ref {
						return Err(ComuneError::new(ComuneErrCode::UninitReference, *span));
					}

					// new& is only allowed in function parameters
					if binding_props.is_new {
						return Err(ComuneError::new(ComuneErrCode::LocalNewReference, *span));
					}

					scope.add_variable(binding_ty.clone(), binding_name, binding_props);
					Ok(binding_ty)
				}
			}

			Stmt::Expr(expr) => expr.validate(scope),
		}
	}
}
