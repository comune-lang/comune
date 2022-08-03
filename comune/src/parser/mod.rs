use std::collections::HashMap;
use std::fmt::Display;
use std::cell::RefCell;

use crate::lexer::{Lexer, Token};

use self::ast::{ASTNode, ASTElem, TokenData};
use self::controlflow::ControlFlow;
use self::errors::CMNError;
use self::expression::{Expr, Operator, Atom};
use self::types::{Type, InnerType, Basic, FnParamList};

pub mod errors;
pub mod ast;
pub mod types;
pub mod expression;
pub mod semantic;
pub mod controlflow;

// Utility functions to make the code a bit cleaner

fn get_current(lexer: &RefCell<Lexer>) -> ParseResult<Token> {
	lexer.borrow().current().clone().ok_or(CMNError::UnexpectedEOF)
}

fn get_next(lexer: &RefCell<Lexer>) -> ParseResult<Token> {
	lexer.borrow_mut().next().or(Err(CMNError::UnexpectedEOF))
}

// Convenience function that matches a &str against various token kinds
fn token_compare(token: &Token, text: &str) -> bool {
	match token {
	    Token::Operator(op) => text == op.as_str(),
   		Token::Other(c) => text.chars().next().unwrap() == *c,
		Token::Keyword(keyword) => text == keyword.as_str(),
		_ => false,
	}
}


// NamespaceInfo describes a root namespace's type and symbol information, gathered on the first parsing pass.
// This is used during the generative pass to disambiguate expressions, as well as validating types and symbols.
pub struct NamespaceInfo {
	pub types: HashMap<String, Type>,
	pub symbols: HashMap<String, (Type, Option<ASTElem>)>
}

impl NamespaceInfo {
	fn new() -> Self {
		NamespaceInfo { types: HashMap::new(), symbols: HashMap::new() }
	}

	fn get_type(&self, name: &str) -> Option<Type> {
		if let Some(basic) = Basic::get_basic_type(name) {
			Some(Type::from_basic(basic))
		} else if self.types.contains_key(name) {
			self.types.get(name).cloned()
		} else {
			None
		}
	}

	fn get_symbol(&self, name: &str) -> Option<(Type, Option<ASTElem>)> {
		self.symbols.get(name).cloned()
	}

}

impl Display for NamespaceInfo {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "types:\n")?;
		
		for t in &self.types {
			write!(f, "\t{}: {}\n", t.0, t.1)?;
		}
		
		write!(f, "\nsymbols:\n")?;
		
		for t in &self.symbols {
			write!(f, "\t{}: {}\n", t.0, t.1.0)?;
		}

		Ok(())
	}
}




pub type ParseResult<T> = Result<T, CMNError>;
pub type ASTResult<T> = Result<T, (CMNError, TokenData)>;

pub struct Parser<'source> {
	lexer: &'source RefCell<Lexer>,
	context: RefCell<NamespaceInfo>,
	generate_ast: bool,
	verbose: bool,
}



impl<'source> Parser<'source> {
	pub fn new(lexer: &'source RefCell<Lexer>, verbose: bool) -> Parser<'source> {
		let result = Parser { 
			lexer, 
			context: RefCell::new(NamespaceInfo::new()),
			generate_ast: false,
			verbose
		};

		result
	}


	pub fn parse_module(&mut self, generate_ast: bool) -> ParseResult<&RefCell<NamespaceInfo>> {
		self.generate_ast = generate_ast;
		self.lexer.borrow_mut().reset().unwrap();
	
		match self.parse_namespace("") {
			Ok(()) => {
				
				if !generate_ast && self.verbose {
					println!("\ngenerated namespace info:\n\n{}", self.context.borrow());
				}

				Ok(&self.context)
			}
			Err(e) => {
				Err(e)
			}
		}
	
	}



	pub fn parse_namespace(&self, path: &str) -> ParseResult<()> {
		let mut current = get_current(&self.lexer)?;

		while current != Token::EOF && current != Token::Other('}') {
			match current {
				Token::EOF => {
					return Err(CMNError::UnexpectedEOF);
				},

				Token::Keyword(ref keyword) => {

					match keyword.as_str() {

						"class" | "struct" => {
							// TODO: Register aggregate type
						}

						"namespace" => {
							let name_token = get_next(&self.lexer)?;

							if let Token::Identifier(namespace_name) = name_token {
								self.parse_namespace(format!("{}::{}", path, namespace_name).as_str())?;
							} else {
								return Err(CMNError::ExpectedIdentifier);
							}
							
						}

						"using" => {
							// TODO: Register type alias/import statement
						}

						_ => {
							return Err(CMNError::UnexpectedToken);
						}
					}
				},

				Token::Identifier(_) => {
					// Parse declaration/definition
					let mut t = self.parse_type()?;
					let mut next = get_current(&self.lexer)?;
					
					if let Token::Identifier(id) = next {
						
						next = get_next(&self.lexer)?;

						let mut ast_elem = None;

						if let Token::Operator(op) = next {
							match op.as_str() {
								
								// Function declaration
								"(" => {	
									t = Type::new(
										InnerType::Function(
											Box::new(t), 
											self.parse_parameter_list()?
										), 
										vec![], // TODO: Generics in function declarations 
										true
									);
									
									// Past the parameter list, check if we're at a function body or not
									current = get_current(&self.lexer)?;
									
									if current == Token::Other('{') {
										// Are we generating the AST? If not, skip the function body
										if self.generate_ast {
											ast_elem = Some(self.parse_block()?);
										} else {
											self.skip_block()?;
										}
									} else if current == Token::Other(';') {
										// No function body, just a semicolon
										get_next(&self.lexer)?;
									} else {
										// Expected a function body or semicolon!
										return Err(CMNError::UnexpectedToken);
									}
								}

								"=" => {
									// Variable declaration
								}
								
								_ => {
									return Err(CMNError::UnexpectedToken);
								}
							}
						}

						// Register declaration to symbol table
						let mut ctx = self.context.borrow_mut();
						ctx.symbols.insert(id, (t, ast_elem));
					}
				}
				
				Token::Other(tk) => {
					match tk {
						';' => {
							get_next(&self.lexer)?;
						}

						_ => {
							return Err(CMNError::UnexpectedToken);
						}
					}
				},

				_ => { // Other types of tokens (literals etc) not valid at this point
					return Err(CMNError::UnexpectedToken);
				}
			}

			current = get_current(&self.lexer)?;
		}

		if current == Token::EOF {
			if path == "" {
				Ok(())
			} else {
				Err(CMNError::UnexpectedEOF)
			}
		} else if current == Token::Other('}') {
			if path != "" {
				Ok(())
			} else {
				Err(CMNError::UnexpectedToken)
			}
		}
		else {
			get_next(&self.lexer)?;
			Ok(())
		}
	}



	// Not super robust - add checks for namespace-level keywords and abort early if found
	fn skip_block(&self) -> ParseResult<Token> {	
		let mut current = get_current(&self.lexer)?;
	
		if current != Token::Other('{') {
			return Err(CMNError::UnexpectedToken);
		}
		let mut bracket_depth = 1;

		while bracket_depth > 0 {
			current = get_next(&self.lexer)?;

			match current {
				Token::Other('{') => bracket_depth += 1,
				Token::Other('}') => bracket_depth -= 1,
				_ => {}
			}
		}

		Ok(get_next(&self.lexer)?)
	}



	fn parse_block(&self) -> ParseResult<ASTElem> {
		let begin = self.lexer.borrow().get_current_start_index();
		let mut current = get_current(&self.lexer)?;

		if current != Token::Other('{') {
			return Err(CMNError::UnexpectedToken);
		}
	
		let mut result = Vec::<ASTElem>::new();

		get_next(&self.lexer)?;
		
		while get_current(&self.lexer)? != Token::Other('}') {			
			let stmt = self.parse_statement()?;
			
			if self.verbose {
				stmt.print();
			}

			result.push(stmt);

			current = get_current(&self.lexer)?;

			while current == Token::Other(';') {
				current = get_next(&self.lexer)?;
			}

		}

		get_next(&self.lexer)?; // consume closing bracket
		
		let end = self.lexer.borrow().get_index();

		Ok(ASTElem { node: ASTNode::Block(result), token_data: (begin, end - begin), type_info: RefCell::new(None)})
	}



	fn parse_statement(&self) -> ParseResult<ASTElem> {
		let mut current = get_current(&self.lexer)?;
		let begin = self.lexer.borrow().get_current_start_index();
		let mut result = None;

		match &current {
		
			Token::Identifier(id) => {
				// Might be a declaration, check if identifier is a type
				let decl_type = self.context.borrow().get_type(&id);

				if decl_type.is_some() {
					// Parse variable declaration
					
					let t = self.parse_type()?;
					let name = get_current(&self.lexer)?;
					let mut expr = None;
					
					if token_compare(&get_next(&self.lexer)?, "=") {
						get_next(&self.lexer)?;
						expr = Some(Box::new(self.parse_expression()?));
					}
					self.check_semicolon()?;
					result = Some(ASTNode::Declaration(t, name, expr));
					
				}
			},

			Token::Keyword(keyword) => {
				match keyword.as_str() {
					

					// Parse return statement

					"return" => {
						let next = get_next(&self.lexer)?;
						
						if next == Token::Other(';') {
							result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Return{expr: None})));
						} else {
							result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Return{expr: Some(self.parse_expression()?)})));
						}
						self.check_semicolon()?;
					}


					// Parse if statement
					
					"if" => {
						current = get_next(&self.lexer)?;

						// Check opening brace
						if token_compare(&current, "(") {
							get_next(&self.lexer)?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let cond = self.parse_expression()?;

						current = get_current(&self.lexer)?;
						
						// Check closing brace
						if token_compare(&current, ")") {
							get_next(&self.lexer)?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						// Parse body
						let body;
						let mut else_body = None;

						if token_compare(&get_current(&self.lexer)?, "{") {
							body = self.parse_block()?;
						} else {
							body = self.parse_statement()?.wrap_in_block();
						}

						if token_compare(&get_current(&self.lexer)?, "else") {
							get_next(&self.lexer)?;
							
							if token_compare(&get_current(&self.lexer)?, "{") {
								else_body = Some(self.parse_block()?);
							} else {
								else_body = Some(self.parse_statement()?.wrap_in_block());
							}
						}

						result = Some(ASTNode::ControlFlow(
							Box::new(ControlFlow::If {
								cond,
								body,
								
								// TODO: Add proper metadata to this
								else_body: match else_body { 
									None => None, 
									Some(e) => Some(e)},
							})));
					}

					// Invalid keyword at start of statement 
					_ => {
						return Err(CMNError::UnexpectedKeyword)
					}
				}
			}
	
			_ => {}
		}
		if result.is_some() {
			let end = self.lexer.borrow().get_index() - get_current(&self.lexer)?.len();
			let len = end - begin;
			return Ok(ASTElem {node: result.unwrap(), token_data: (begin, len), type_info: RefCell::new(None)});
		}

		// Not any of the above, try parsing an expression
		let expr = self.parse_expression()?;
		self.check_semicolon()?;
		return Ok(expr);
	}


	fn check_semicolon(&self) -> ParseResult<()> {
		if token_compare(&get_current(&self.lexer)?, ";") {
			get_next(&self.lexer)?;
			Ok(())
		} else {
			Err(CMNError::UnexpectedToken)
		}
	}



	fn parse_expression(&self) -> ParseResult<ASTElem> {
		let begin = self.lexer.borrow().get_current_start_index();
		let expr = ASTNode::Expression(self.parse_expression_bp(0)?);
		let len = self.lexer.borrow().get_index() - begin;
		Ok(ASTElem { node: expr, token_data: (begin, len), type_info: RefCell::new(None)})
	}



	// Basic pratt parser, nothing too fancy
	fn parse_expression_bp(&self, min_bp: u8) -> ParseResult<Expr> {
		let mut current = get_current(&self.lexer)?;
		let meta = (self.lexer.borrow().get_current_start_index(), current.len());

		// Get initial part of expression, could be an Atom or the operator of a unary Cons
		let lhs = match current {

			Token::Identifier(_) | Token::StringLiteral(_) | Token::NumLiteral(_) | Token::BoolLiteral(_) => 
				Expr::Atom(RefCell::new(self.parse_atom()?), meta),
			
			Token::Operator(tk) => {
				// Handle unary prefix operators
				match Operator::get_operator(&tk, false) {
					Some(op) => {
						get_next(&self.lexer)?;
						
						if let Operator::Call = op {
							// Special case; parse sub-expression
							let sub = self.parse_expression_bp(0)?;
							current = get_current(&self.lexer)?;
							if let Token::Operator(op) = current {
								if op.as_str() != ")" {
									return Err(CMNError::UnexpectedToken);
								}
								get_next(&self.lexer)?;
								return Ok(sub);
							} else {
								return Err(CMNError::UnexpectedToken);
							}
							
						} else {
							let begin_index = self.lexer.borrow().get_current_start_index();

							let rhs = self.parse_expression_bp(op.get_binding_power())?;

							let end_index = self.lexer.borrow().get_current_start_index() - 1;
							return Ok(Expr::Cons(op, vec![rhs], (end_index, end_index - begin_index)));
						}
					},
					None => return Err(CMNError::UnexpectedToken)
				};
				
				
			}
			
			_ => { return Err(CMNError::UnexpectedToken); }

		};


		loop {
			let tk = get_current(&self.lexer)?;

			let op = match tk {

				Token::Operator(op) => match Operator::get_operator(&op, true) {
					Some(result) => result,
					None => break,
				},
			
				_ => break
			
			};
			
			let binding_power = op.get_binding_power();
			let (lbp, rbp);

			if op.is_associative_rtl() {
				lbp = binding_power;
				rbp = binding_power + 1;
			} else {
				lbp = binding_power + 1;
				rbp = binding_power;
			}

			if lbp < min_bp { 
				break;
			}
			
			get_next(&self.lexer)?;

			let begin_index = self.lexer.borrow().get_index() - get_current(&self.lexer).unwrap().len();

			let rhs = self.parse_expression_bp(rbp)?;

			let end_index = self.lexer.borrow().get_index() - get_current(&self.lexer).unwrap().len();
			return Ok(Expr::Cons(op, vec![lhs, rhs], (end_index, end_index - begin_index)));
		}

		Ok(lhs)
	}



	fn parse_atom(&self) -> ParseResult<Atom> {
		let mut current = get_current(&self.lexer)?;
		let next = get_next(&self.lexer)?;

		match current {
			// TODO: Variables and function calls
			Token::Identifier(id) => {
				if let Token::Operator(ref op) = next {
					match op.as_str() {

						"(" => {
							// Function call
							let mut args = vec![];
							current = get_next(&self.lexer)?;
							
							if current != Token::Operator(")".to_string()) {
								loop {									
									args.push(self.parse_expression()?);
									
									current = get_current(&self.lexer)?;

									if let Token::Other(',') = current {
										get_next(&self.lexer)?;
									} else if current == Token::Operator(")".to_string()) {
										break;
									} else {
										return Err(CMNError::UnexpectedToken);
									}
								}
							}
							get_next(&self.lexer)?;

							Ok(Atom::FnCall{name: id, args})
						}

						"<" => {
							// TODO: Disambiguate between type parameter list or LT operator 
							todo!()
						}

						_ => {
							// Just a variable
							Ok(Atom::Variable(id))
						}
					} 
				} else {
					Ok(Atom::Variable(id))
				}	
			},

			Token::StringLiteral(s) => Ok(Atom::StringLit(s)),
			
			// TODO: Separate NumLiteral into float and int?
			Token::NumLiteral(i) => Ok(Atom::IntegerLit(i.parse::<isize>().unwrap())),

			Token::BoolLiteral(b) => Ok(Atom::BoolLit(b)),

			_ => Err(CMNError::UnexpectedToken)
		}
	}

	

	fn parse_parameter_list(&self) -> ParseResult<FnParamList> {
		let lexer = &self.lexer;
		let mut next = lexer.borrow_mut().next().unwrap();
		let mut result = vec![];

		while let Token::Identifier(_) = next {
			let mut param = (Box::new(self.parse_type()?), None);
			
			
			// Check for param name
			let current = lexer.borrow().current().clone().unwrap();
			if let Token::Identifier(id) = current {
				param.1 = Some(id);
				lexer.borrow_mut().next().unwrap();
			}
			
			result.push(param);

			// Check if we've arrived at a comma, skip it, and loop back around
			next = lexer.borrow().current().clone().unwrap();
			match next {
				Token::Other(',') => {
					next = lexer.borrow_mut().next().unwrap();
					continue;
				}
				Token::Operator(s) => {
					if s.as_str() == ")" {
						break;
					} else {
						return Err(CMNError::UnexpectedToken);
					}
				}
				_ => {
					return Err(CMNError::UnexpectedToken);
				}
			}
		}

		let current = lexer.borrow().current().clone().unwrap();

		if let Token::Operator(s) = current {
			if s.as_str() == ")" {
				lexer.borrow_mut().next().unwrap();
				Ok(result)
			} else {
				Err(CMNError::UnexpectedToken)
			}
		} else {
			Err(CMNError::UnexpectedToken)
		}
	}



	fn parse_type(&self) -> ParseResult<Type> {
		let lexer = &self.lexer;
		let mut result : Type;
		let current;
		
		{
			current = lexer.borrow().current().as_ref().unwrap().clone();
		}

		if let Token::Identifier(ref id) = current {
			// Typename
			let typename = id.clone();

			let found_type;
			{
				let ctx = self.context.borrow_mut();
				found_type = ctx.get_type(&typename);

				result = match found_type { 
					Some(t) => t.clone(),
					None => Type::new(InnerType::Unresolved(current.clone()), vec![], false)
				}
			}

			let mut next = lexer.borrow_mut().next().unwrap();
		
			match next { 
				Token::Operator(ref op) => {
					match op.as_str() {
						"*" => {
							while token_compare(&next, "*") {
								result = Type::new(InnerType::Pointer(Box::new(result)), vec![], false);
								next = lexer.borrow_mut().next().unwrap();
							}
						}
						
						"<" => {
							lexer.borrow_mut().next().unwrap();
							
							let generic = self.parse_type()?;
							result.generics.push(generic);
							
							while *lexer.borrow_mut().current().as_ref().unwrap() == Token::Other(',') {
								lexer.borrow_mut().next().unwrap();
								
								let generic = self.parse_type()?;
								result.generics.push(generic);
							}

							// assert token == '>'
							if *lexer.borrow_mut().current().as_ref().unwrap() != Token::Operator(">".to_string()) {
								return Err(CMNError::UnexpectedToken)
							}
							// consume >
							lexer.borrow_mut().next().unwrap();
						}
						_ => {
							// 
							return Ok(result);
						}
					}
				}
				_ => {
					return Ok(result);
				}
			}
			Ok(result)
		} else {
			Err(CMNError::ExpectedIdentifier)
		}
	}
		


	
}