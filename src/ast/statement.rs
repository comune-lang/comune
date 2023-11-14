use std::fmt::Display;

use crate::lexer::SrcSpan;

use super::{
	expression::Expr,
	module::Name,
	types::{BindingProps, Type},
};

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
	Decl(Vec<(Type, Name, BindingProps)>, Option<Expr>, SrcSpan),
	Expr(Expr),
}

impl Display for Stmt {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Stmt::Decl(bindings, expr, _) => {
				for (i, (ty, name, props)) in bindings.iter().enumerate() {
					if i != 0 {
						write!(f, ", ")?;
					}

					write!(f, "{ty}{props} {name}")?;
				}

				if let Some(expr) = expr {
					write!(f, " = {expr}")?;
				}

				Ok(())
			}

			Stmt::Expr(expr) => write!(f, "{expr}"),
		}
	}
}
