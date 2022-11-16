use std::cell::RefCell;
use std::fmt::Display;

use super::controlflow::ControlFlow;
use super::expression::{Atom, Expr};
use super::namespace::Name;
use super::types::{Basic, Type, Typed};
use super::FnScope;
use crate::parser::AnalyzeResult;


#[derive(Clone, Debug, PartialEq)]
pub enum ASTNode {
	Block(
		Vec<ASTElem>, // Statements (doesnt need to be ASTChild because Vec is already dynamic)
	),
	Expression(RefCell<Expr>),
	Declaration(
		Type,
		Name,
		Option<Box<ASTElem>>, // Expression or Block
	),

	ControlFlow(Box<ControlFlow>),
}

impl ASTElem {
	fn print_depth(depth: usize) {
		print!("\t{: <1$}", "", depth * 4);
	}

	fn print_with_depth(&self, depth: usize) {
		ASTElem::print_depth(depth);

		match &self.node {
			ASTNode::Block(v) => {
				println!("block");
				for elem in v {
					elem.print_with_depth(depth + 1);
				}
			}

			ASTNode::Expression(expr) => {
				println!("expression {}", expr.borrow());
			}

			ASTNode::Declaration(t, n, e) => {
				if let Some(e) = e {
					println!("declaration {} {} = {};", t, n, e);
				} else {
					println!("declaration {} {};", t, n);
				}
			}
			ASTNode::ControlFlow(ctrl) => {
				println!("ctrl {}", ctrl);
			}
		}
	}

	pub fn print(&self) {
		self.print_with_depth(0);
	}

	pub fn wrap_in_block(self) -> ASTElem {
		let meta = self.token_data;
		ASTElem {
			node: ASTNode::Block(vec![self]),
			token_data: meta,
			type_info: RefCell::new(None),
		}
	}

	pub fn wrap_expr_in_cast(&self, from: Option<Type>, to: Type) {
		if let ASTNode::Expression(e) = &self.node {
			let dummy = Expr::Atom(Atom::IntegerLit(0, None), self.token_data);
			let expr = e.replace(dummy);
			e.replace(Expr::create_cast(expr, from, to.clone(), self.token_data));
			self.type_info.replace(Some(to));
		} else {
			panic!();
		}
	}

	pub fn get_expr(&self) -> &RefCell<Expr> {
		match &self.node {
			ASTNode::Expression(e) => e,
			_ => panic!(),
		}
	}
}

impl Display for ASTElem {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self.node {
			ASTNode::Block(b) => {
				write!(f, "{{\n")?;
				for elem in b {
					write!(f, "\t\t{}", elem)?;
				}
				write!(f, "\n\t}}")
			}

			ASTNode::Expression(e) => write!(f, "{}", e.borrow()),
			ASTNode::Declaration(t, n, e) => {
				if let Some(e) = e {
					write!(f, "{} {} = {};", t, n, e)
				} else {
					write!(f, "{} {};", t, n)
				}
			}
			ASTNode::ControlFlow(c) => write!(f, "{}", c),
		}
	}
}

impl ASTNode {
	fn get_type(&self, scope: &FnScope, t: Option<&Type>, meta: TokenData) -> AnalyzeResult<Type> {
		match self {
			ASTNode::Block(elems) => {
				let subscope = FnScope::from_parent(scope);
				let mut result = Type::Basic(Basic::VOID);
				for elem in elems {
					result = elem.node.get_type(&subscope, t, meta)?;
				}
				Ok(result)
			}

			ASTNode::Expression(e) => e.borrow_mut().validate(scope, t, meta),

			// Declaration types are deduced at parse-time (thanks, C-style syntax)
			ASTNode::Declaration(t, _, _) => Ok(t.clone()),

			ASTNode::ControlFlow(ctrl) => ctrl.get_type(scope),
		}
	}
}

impl Typed for ASTElem {
	fn get_type(&self, scope: &FnScope) -> AnalyzeResult<Type> {
		self.node
			.get_type(scope, self.type_info.borrow().as_ref(), self.token_data)
	}
}
