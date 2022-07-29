use crate::lexer::Token;

use super::{ASTResult, ParserError};
use super::semantic::Scope;
use super::types::{Type, Basic, Typed, InnerType};
use super::expression::Expr;
use super::controlflow::ControlFlow;


pub type TokenData = (usize, usize); // idx, len

// ASTElem contains metadata for an ASTNode, used for error reporting and stuff
#[derive(Clone)]
pub struct ASTElem {
	pub node: ASTNode,

	// For error reporting
	pub token_data: TokenData,
}


#[derive(Clone)]
pub enum ASTNode {
	Block(
		Vec<ASTElem>			// Statements (doesnt need to be ASTChild because Vec is already dynamic)
	), 			
	Expression(
		Expr
	),
	Declaration(
		Type, 					// Type
		Token,					// Identifier
		Option<Box<ASTElem>>	// Expression or Block
	),

	ControlFlow(
		ControlFlow,
	)
}

impl ASTNode {
	fn print_depth(depth: usize) {
		print!("\t{: <1$}", "", depth * 4);
	}

	fn print_with_depth(&self, depth: usize) {
		ASTNode::print_depth(depth);

		match self {
			ASTNode::Block(v) => {
				println!("block");
				for elem in v {
					elem.node.print_with_depth(depth + 1);
				}
			},

			ASTNode::Expression(expr) => {
				println!("expression {}", expr);
			},

			ASTNode::Declaration(t, n, e) => {
				println!("declaration (todo)");
				
			},
    		ASTNode::ControlFlow(ctrl) => {
				println!("ctrl flow (todo)");
			},
		}
	}

	pub fn print(&self) {
		self.print_with_depth(0);
	}


	pub fn validate_node(&self, scope: &mut Scope, meta: TokenData) -> ASTResult<()> {
		match self {
			ASTNode::Block(elems) => {
				let mut subscope = Scope::from_parent(scope);
				for elem in elems {
					elem.node.validate_node(&mut subscope, elem.token_data)?;
				}
				Ok(())
			},
			ASTNode::Expression(_) => Ok(()), // Bare expression has no type requirements
			ASTNode::Declaration(_, _, _) => Ok(()), // Ditto

			ASTNode::ControlFlow(ctrl) => match ctrl {

				ControlFlow::If { cond, .. } | 
				ControlFlow::While { cond, .. } | 
				ControlFlow::For { cond, .. } => {	
					// Check if condition is coercable to bool
					let cond_type = cond.get_type(scope, meta)?;
					let bool_t = Type::from_basic(Basic::BOOL);

					if cond_type.coercable_to(&bool_t) {
						Ok(())
					} else {
						Err((ParserError::TypeMismatch(cond_type, bool_t), meta))
					}
				},
				
				_ => Ok(())
			},
		}
		
	}



	// Recursively validate the return type of a block. Ignores everything except return statements and sub-blocks.
	// Returns Ok(Some(Type)) if block 
	pub fn get_return_type(&self, scope: &Scope, meta: TokenData, ret: &Type) -> ASTResult<Option<Type>> {
		match self {
			ASTNode::Block(elems) => {
				let subscope = Scope::from_parent(scope);
				let mut last_ret_type = None;

				for elem in elems {
					let stmt_type;

					match &elem.node {

						ASTNode::ControlFlow(ctrl) => {

							stmt_type = match ctrl {
								ControlFlow::Return { expr: _ } => {
									// An unconditional return statement gives the current block a return type
									let ret_type = Some(ctrl.get_type(scope, meta)?);
									last_ret_type = ret_type.clone();
									ret_type
								}

								ControlFlow::If { body, cond: _, else_body } => {
									let body_type = body.node.get_return_type(scope, meta, ret)?;
									
									// Check if both block's return types match
									// This is kinda fucked rn, figure out how to do this properly later
									if let Some(else_body) = else_body {
										let else_type = else_body.node.get_return_type(scope, meta, ret)?;
										if let Some(else_type) = else_type {
											if body_type.is_some() && !else_type.coercable_to(body_type.as_ref().unwrap()) {
												return Err((ParserError::TypeMismatch(body_type.unwrap(), else_type), meta));
											}
										}	
									}

									body_type
								},

								ControlFlow::While { body, .. } | ControlFlow::For { body, .. } => {
									body.node.get_return_type(scope, meta, ret)?
								},

								ControlFlow::Break => todo!(),
								ControlFlow::Continue => todo!(),
							};
						},

						_ => {
							// Validate sub-blocks
							stmt_type = elem.node.get_return_type(&subscope, elem.token_data, ret)?; 

						}
					}

					if let Some(stmt_type) = stmt_type {
						if stmt_type.coercable_to(ret) {
							Some(stmt_type);
						} else {
							return Err((ParserError::ReturnTypeMismatch { expected: ret.clone(), got: stmt_type }, meta));
						}
					}
				}

				Ok(last_ret_type)
			},

			// Non-block nodes don't evaluate themselves for return types
			_ => Ok(None),
		}
	}
}

impl Typed for ASTNode {
	fn get_type(&self, scope: &Scope, meta: TokenData) -> ASTResult<Type> {
		match self {
			ASTNode::Block(elems) => {
				let subscope = Scope::from_parent(scope);
				let mut result = Type::from_basic(Basic::VOID);
				for elem in elems {
					result = elem.node.get_type(&subscope, meta)?;
				}
				Ok(result) // Just take the type of the last statement for now. Remember to add support for `return` later
			},
			
			ASTNode::Expression(e) => e.get_type(scope, meta),

			// Declaration types are deduced at parse-time (thanks, C-style syntax)
			ASTNode::Declaration(t, _, _) => Ok(t.clone()),
    		
			ASTNode::ControlFlow(ctrl) => ctrl.get_type(scope, meta),
		}
	}
}

impl Typed for ASTElem {
    fn get_type(&self, scope: &Scope, _meta: TokenData) -> ASTResult<Type> {
        self.node.get_type(scope, self.token_data)
    }
}