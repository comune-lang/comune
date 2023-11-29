use std::fmt::Display;

use crate::lexer::SrcSpan;

use super::{
	expression::Expr,
	pattern::Pattern,
};

#[derive(Clone, Debug, PartialEq)]
pub enum Stmt {
	Decl(Pattern, Option<Expr>, SrcSpan),
	Expr(Expr),
}

impl Display for Stmt {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Stmt::Decl(pattern, expr, _) => {
				write!(f, "{pattern}")?;

				if let Some(expr) = expr {
					write!(f, " = {expr}")?;
				}

				Ok(())
			}

			Stmt::Expr(expr) => write!(f, "{expr}"),
		}
	}
}
