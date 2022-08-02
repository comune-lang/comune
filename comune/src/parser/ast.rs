use std::cell::RefCell;
use std::fmt::Display;

use crate::lexer::Token;

use super::{ASTResult, ParserError};
use super::semantic::Scope;
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
		Expr
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
				println!("expression {}", expr);
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

	// Recursively validate ASTNode types and check if blocks have matching return types
	pub fn validate(&self, scope: &mut Scope, ret: &Type) -> ASTResult<Option<Type>> {
		let result = match &self.node {

			ASTNode::Block(elems) => {
				let mut subscope = Scope::from_parent(scope);
				let mut last_ret = None;

				for elem in elems {
					let t = elem.validate(&mut subscope, ret)?;

					if let Some(t) = t {
						// Only compare against return type for control flow nodes
						if let ASTNode::ControlFlow(_) = elem.node {
							if !t.coercable_to(ret) {
								return Err((ParserError::TypeMismatch(t, ret.clone()), elem.token_data))
							}
							last_ret = Some(t);
						}
					}
				}
				Ok(last_ret)
			},
			
			ASTNode::Expression(e) => Ok(Some(e.get_type(scope, ret, self.token_data)?)),
			
			ASTNode::Declaration(t, n, e) => {

				if let Some(expr) = e {
					expr.type_info.replace(Some(t.clone()));
					let expr_type = expr.get_type(scope)?;
					if !expr_type.coercable_to(t) {
						return Err((ParserError::TypeMismatch(t.clone(), expr_type), self.token_data));
					}
				}

				scope.add_variable(t.clone(), n.to_string());

				Ok(None)	
			},

			ASTNode::ControlFlow(ctrl) => match ctrl.as_ref() {

				ControlFlow::If { cond, body, else_body } => {
					let cond_type = cond.get_type(scope)?;
					let bool_t = Type::from_basic(Basic::BOOL);

					if !cond_type.coercable_to(&bool_t) {
						return Err((ParserError::TypeMismatch(cond_type, bool_t), self.token_data));
					}
					let t = body.validate(scope, ret)?;

					if let Some(else_body) = else_body {
						else_body.validate(scope, ret)?;
					}

					Ok(t)
				}

				ControlFlow::While { cond, body } => {
					let cond_type = cond.get_type(scope)?;
					let bool_t = Type::from_basic(Basic::BOOL);

					if !cond_type.coercable_to(&bool_t) {
						return Err((ParserError::TypeMismatch(cond_type, bool_t), self.token_data));
					}

					let t = body.validate(scope, ret)?;
					Ok(t)
				} 

				ControlFlow::For { cond, body, init, iter } => {	
					// Check if condition is coercable to bool
					let cond_type = cond.get_type(scope)?;
					let bool_t = Type::from_basic(Basic::BOOL);

					if !cond_type.coercable_to(&bool_t) {
						return Err((ParserError::TypeMismatch(cond_type, bool_t), self.token_data));
					}
					init.validate(scope, ret)?;
					iter.validate(scope, ret)?;
					let t = body.validate(scope, ret)?;
					if t.is_some() {
						Ok(t)
					} else {
						Ok(None)
					}
				}

				ControlFlow::Return { expr } => {
					if let Some(expr) = expr {
						let t = expr.validate(scope, ret)?;

						if let Some(t) = t {
							if t.coercable_to(ret) {
								Ok(Some(t))
							} else {
								Err((ParserError::ReturnTypeMismatch { expected: ret.clone(), got: t }, self.token_data))
							}
						} else {
							Ok(None)
						}


					} else {
						Ok(Some(Type::from_basic(Basic::VOID))) // Return with no expression is of type void 
					}
				
				},
				
				_ => Ok(None)
			},
		};

		match result {
			Ok(ref r) => self.type_info.replace(r.clone()),
			Err(e) => return Err(e),
		};
		result
	}



	// Recursively validate the return type of a block. Ignores everything except return statements and sub-blocks.
	// Returns Ok(Some(Type)) if block 
	/*pub fn get_return_type(&self, scope: &Scope, ret: &Type) -> ASTResult<Option<Type>> {
		match &self.node {
			ASTNode::Block(elems) => {
				let subscope = Scope::from_parent(scope);
				let mut last_ret_type = None;

				for elem in elems {
					let stmt_type;

					match &elem.node {

						ASTNode::ControlFlow(ctrl) => {

							stmt_type = match ctrl.as_ref() {
								ControlFlow::Return { expr: _ } => {
									// An unconditional return statement gives the current block a return type
									let ret_type = Some(ctrl.get_type(scope)?);
									last_ret_type = ret_type.clone();
									ret_type
								}

								ControlFlow::If { body, cond: _, else_body } => {
									let body_type = body.get_return_type(scope, ret)?;
									
									// Check if both block's return types match
									// This is kinda fucked rn, figure out how to do this properly later
									if let Some(else_body) = else_body {
										let else_type = else_body.get_return_type(scope, ret)?;
										if let Some(else_type) = else_type {
											if body_type.is_some() && !else_type.coercable_to(body_type.as_ref().unwrap()) {
												return Err((ParserError::TypeMismatch(body_type.unwrap(), else_type), self.token_data));
											}
										}	
									}

									body_type
								},

								ControlFlow::While { body, .. } | ControlFlow::For { body, .. } => {
									body.get_return_type(scope, ret)?
								},

								ControlFlow::Break => todo!(),
								ControlFlow::Continue => todo!(),
							};
						},

						_ => {
							// Validate sub-blocks
							stmt_type = elem.get_return_type(&subscope, ret)?; 

						}
					}

					if let Some(stmt_type) = stmt_type {
						if stmt_type.coercable_to(ret) {
							Some(stmt_type);
						} else {
							return Err((ParserError::ReturnTypeMismatch { expected: ret.clone(), got: stmt_type }, elem.token_data));
						}
					}
				}

				Ok(last_ret_type)
			},

			// Non-block nodes don't evaluate themselves for return types
			_ => Ok(None),
		}
	}*/
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

            ASTNode::Expression(e) => 			write!(f, "{}", e),
            ASTNode::Declaration(t, n, e) => 	if let Some(e) = e { write!(f, "{} {} = {};", t, n, e) } else { write!(f, "{} {};", t, n) },
            ASTNode::ControlFlow(c) => 			write!(f, "{}", c),
        }
    }
}



impl ASTNode {
	fn get_type(&self, scope: &Scope, t: Option<&Type>, meta: TokenData) -> ASTResult<Type> {
		match self {
			ASTNode::Block(elems) => {
				let subscope = Scope::from_parent(scope);
				let mut result = Type::from_basic(Basic::VOID);
				for elem in elems {
					result = elem.node.get_type(&subscope, t, meta)?;
				}
				Ok(result) // Just take the type of the last statement for now. Remember to add support for `return` later
			},
			
			ASTNode::Expression(e) => e.get_type(scope, t.unwrap(), meta),

			// Declaration types are deduced at parse-time (thanks, C-style syntax)
			ASTNode::Declaration(t, _, _) => Ok(t.clone()),
    		
			ASTNode::ControlFlow(ctrl) => ctrl.get_type(scope),
		}
	}
}

impl Typed for ASTElem {
    fn get_type(&self, scope: &Scope) -> ASTResult<Type> {
        self.node.get_type(scope, self.type_info.borrow().as_ref(), self.token_data)
    }
}