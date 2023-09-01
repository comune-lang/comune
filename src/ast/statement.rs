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
			Stmt::Decl(..) => todo!(),
			Stmt::Expr(expr) => expr.fmt(f),
		}
	}
}
