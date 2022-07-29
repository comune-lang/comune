use super::{expression::Expr, ast::ASTElem, types::{Typed, Type, Basic}, ParserError};


#[derive(Clone)]
pub enum ControlFlow {
	If {
		cond: Expr, 
		body: Box<ASTElem>, 
		else_body: Option<Box<ASTElem>>
	},
	
	While {
		cond: Expr, 
		body: Box<ASTElem>
	},
	
	For {
		init: Box<ASTElem>, 
		cond: Expr, 
		iter: Expr,
		body: Box<ASTElem>
	},

	Return {
		expr: Option<Expr>,
	},

	Break,
	Continue,
}


impl Typed for ControlFlow {
    fn get_type(&self, scope: &super::semantic::Scope, meta: super::ast::TokenData) -> super::ASTResult<Type> {
        match self {
            ControlFlow::If { cond: _, body, else_body } => {

				if let Some(else_body) = else_body {
					// Has an else branch, so evaluates to a type both bodies are coercable to				
					let body_type = body.get_type(scope, meta)?;
					let else_type = else_body.get_type(scope, meta)?;

					if else_type.coercable_to(&body_type) {
						Ok(body_type)
					} else if body_type.coercable_to(&else_type) {
						Ok(else_type)
					} else {
						Err((ParserError::TypeMismatch(body_type, else_type), meta))
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
					expr.get_type(scope, meta)
				} else {
					Ok(Type::from_basic(Basic::VOID))
				}},

            ControlFlow::Break => todo!(),
            ControlFlow::Continue => todo!(),
        }
    }
}