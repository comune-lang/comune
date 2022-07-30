use std::fmt::Display;

use super::{ast::ASTElem, types::{Typed, Type, Basic}, ParserError};


#[derive(Clone, Debug)]
pub enum ControlFlow {
	If {
		cond: ASTElem,
		body: ASTElem,
		else_body: Option<ASTElem>
	},
	
	While {
		cond: ASTElem, 
		body: ASTElem
	},
	
	For {
		init: ASTElem, 
		cond: ASTElem, 
		iter: ASTElem,
		body: ASTElem
	},

	Return {
		expr: Option<ASTElem>,
	},

	Break,
	Continue,
}


impl Typed for ControlFlow {
    fn get_type(&self, scope: &super::semantic::Scope) -> super::ASTResult<Type> {
        match self {
            ControlFlow::If { cond: _, body, else_body } => {

				if let Some(else_body) = else_body {
					// Has an else branch, so evaluates to a type both bodies are coercable to				
					let body_type = body.get_type(scope)?;
					let else_type = else_body.get_type(scope)?;

					if else_type.coercable_to(&body_type) {
						Ok(body_type)
					} else if body_type.coercable_to(&else_type) {
						Ok(else_type)
					} else {
						Err((ParserError::TypeMismatch(body_type, else_type), else_body.token_data))
					}

				} else {
					// No else branch, evaluates to void
					Ok(Type::from_basic(Basic::VOID))
				}
			},

			// Loops are always of type void
            ControlFlow::While { cond: _, body: _ } | ControlFlow::For { init: _, cond: _, iter: _, body: _} => 
				Ok(Type::from_basic(Basic::VOID)),

            ControlFlow::Return { expr } => { 
				if let Some(expr) = expr { 
					expr.get_type(scope)
				} else {
					Ok(Type::from_basic(Basic::VOID))
				}},

            ControlFlow::Break => todo!(),
            ControlFlow::Continue => todo!(),
        }
    }
}


impl Display for ControlFlow {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ControlFlow::If { cond, body, else_body } => {
				if let Some(else_body) = else_body {
					write!(f, "if {} then {} else {}", cond, body, else_body)
				} else {
					write!(f, "if {} then {}", cond, body)
				}
			},
			ControlFlow::While { cond, body } => write!(f, "while {} {}", cond, body),
            ControlFlow::For { init, cond, iter, body } => write!(f, "for ({}; {}; {}) {}", init, cond, iter, body),
            ControlFlow::Return { expr } => if let Some(expr) = expr { write!(f, "return {}", expr) } else { write!(f, "return") },
            ControlFlow::Break => todo!(),
            ControlFlow::Continue => todo!(),
        }
    }
}