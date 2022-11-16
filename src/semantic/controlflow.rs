use std::fmt::Display;

use super::{expression::Expr, statement::Stmt};

#[derive(Clone, Debug, PartialEq)]
pub enum ControlFlow {
	If {
		cond: Expr,
		body: Expr,
		else_body: Option<Expr>,
	},

	While {
		cond: Expr,
		body: Expr,
	},

	For {
		init: Option<Stmt>,
		cond: Option<Expr>,
		iter: Option<Expr>,
		body: Expr,
	},

	Return {
		expr: Option<Expr>,
	},

	Break,
	Continue,
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
