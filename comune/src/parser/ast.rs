use std::cell::RefCell;
use std::fmt::Display;

use super::lexer::Token;
use super::ASTResult;
use super::semantic::FnScope;
use super::types::{Type, Basic, Typed};
use super::expression::Expr;
use super::controlflow::ControlFlow;


pub type TokenData = (usize, usize); // idx, len

// ASTElem contains metadata for an ASTNode, used for error reporting and stuff
#[derive(Clone, Debug)]
pub struct ASTElem {
	pub node: ASTNode,
	
	// For error reporting
	pub token_data: TokenData,
	pub type_info: RefCell<Option<Type>>,
}


#[derive(Clone, Debug)]
pub enum ASTNode {
	Block(
		Vec<ASTElem>			// Statements (doesnt need to be ASTChild because Vec is already dynamic)
	), 			
	Expression(
		RefCell<Expr>
	),
	Declaration(
		Type, 					// Type
		Token,					// Identifier
		Option<Box<ASTElem>>	// Expression or Block
	),

	ControlFlow(
		Box<ControlFlow>,
	)
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
			},

			ASTNode::Expression(expr) => {
				println!("expression {}", expr.borrow());
			},

			ASTNode::Declaration(t, n, e) => {
				if let Some(e) = e {
					println!("declaration {} {} = {};", t, n, e);
				} else {
					println!("declaration {} {};", t, n);
				}
			},
    		ASTNode::ControlFlow(ctrl) => {
				println!("ctrl {}", ctrl);
			},
		}
	}

	pub fn print(&self) {
		self.print_with_depth(0);
	}


	pub fn wrap_in_block(self) -> ASTElem {
		let meta = self.token_data;
		ASTElem { node: ASTNode::Block(vec![self]), token_data: meta, type_info: RefCell::new(None) }
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
			},

            ASTNode::Expression(e) => 			write!(f, "{}", e.borrow()),
            ASTNode::Declaration(t, n, e) => 	if let Some(e) = e { write!(f, "{} {} = {};", t, n, e) } else { write!(f, "{} {};", t, n) },
            ASTNode::ControlFlow(c) => 			write!(f, "{}", c),
        }
    }
}



impl ASTNode {
	fn get_type(&self, scope: &FnScope, t: Option<&Type>, meta: TokenData) -> ASTResult<Type> {
		match self {
			ASTNode::Block(elems) => {
				let subscope = FnScope::from_parent(scope);
				let mut result = Type::from_basic(Basic::VOID);
				for elem in elems {
					result = elem.node.get_type(&subscope, t, meta)?;
				}
				Ok(result) // Just take the type of the last statement for now. Remember to add support for `return` later
			},
			
			ASTNode::Expression(e) => e.borrow_mut().validate(scope, t, meta),

			// Declaration types are deduced at parse-time (thanks, C-style syntax)
			ASTNode::Declaration(t, _, _) => Ok(t.clone()),
    		
			ASTNode::ControlFlow(ctrl) => ctrl.get_type(scope),
		}
	}
}

impl Typed for ASTElem {
    fn get_type(&self, scope: &FnScope) -> ASTResult<Type> {
        self.node.get_type(scope, self.type_info.borrow().as_ref(), self.token_data)
    }
}