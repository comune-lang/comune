use std::fmt::Display;

use crate::parser::AnalyzeResult;

use super::{
	ast::ASTElem,
	types::{Basic, Type, Typed},
	FnScope,
};

#[derive(Clone, Debug, PartialEq)]
pub enum ControlFlow {
	If {
		cond: ASTElem,
		body: ASTElem,
		else_body: Option<ASTElem>,
	},

	While {
		cond: ASTElem,
		body: ASTElem,
	},

	For {
		init: Option<ASTElem>,
		cond: Option<ASTElem>,
		iter: Option<ASTElem>,
		body: ASTElem,
	},

	Return {
		expr: Option<ASTElem>,
	},

	Break,
	Continue,
}

impl Typed for ControlFlow {
	fn get_type<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> AnalyzeResult<Type> {
		match self {
			ControlFlow::If {
				cond: _,
				body,
				else_body,
			} => {
				if let Some(else_body) = else_body {
					// Has an else branch, so evaluates to a type both bodies are coercable to
					let _body_type = body.get_type(scope)?;
					let _else_type = else_body.get_type(scope)?;

					//if else_body.get_expr().borrow().coercable_to(&else_type, &body_type, scope) {
					//	Ok(body_type)
					//} else if body.get_expr().borrow().coercable_to(&body_type, &else_type, scope) {
					//	Ok(else_type)
					//} else {
					//	Err((CMNError::ExprTypeMismatch(body_type, else_type), else_body.token_data))
					//}

					todo!(); // I don't remember what this is relevant for rn lol
				} else {
					// No else branch, evaluates to void
					Ok(Type::Basic(Basic::VOID))
				}
			}

			// Loops are always of type void
			ControlFlow::While { cond: _, body: _ }
			| ControlFlow::For {
				init: _,
				cond: _,
				iter: _,
				body: _,
			} => Ok(Type::Basic(Basic::VOID)),

			ControlFlow::Return { expr } => {
				if let Some(expr) = expr {
					expr.get_type(scope)
				} else {
					Ok(Type::Basic(Basic::VOID))
				}
			}

			ControlFlow::Break => todo!(),
			ControlFlow::Continue => todo!(),
		}
	}
}

impl Display for ControlFlow {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			ControlFlow::If {
				cond,
				body,
				else_body,
			} => {
				if let Some(else_body) = else_body {
					write!(f, "if {} then {} else {}", cond, body, else_body)
				} else {
					write!(f, "if {} then {}", cond, body)
				}
			}

			ControlFlow::While { cond, body } => write!(f, "while {} {}", cond, body),

			ControlFlow::For {
				init,
				cond,
				iter,
				body,
			} => {
				write!(f, "for (")?;
				if let Some(init) = init {
					write!(f, "{} ", init)?;
				} else {
					write!(f, "; ")?;
				}
				if let Some(cond) = cond {
					write!(f, "{}; ", cond)?;
				} else {
					write!(f, "; ")?;
				}
				if let Some(iter) = iter {
					write!(f, "{}", iter)?;
				}

				write!(f, ") {}", body)
			}

			ControlFlow::Return { expr } => {
				if let Some(expr) = expr {
					write!(f, "return {}", expr)
				} else {
					write!(f, "return")
				}
			}

			ControlFlow::Break => todo!(),
			ControlFlow::Continue => todo!(),
		}
	}
}