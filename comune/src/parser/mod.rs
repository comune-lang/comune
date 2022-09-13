use std::cell::RefCell;

use self::lexer::Token;
use self::ast::{ASTNode, ASTElem, TokenData};
use self::controlflow::ControlFlow;
use self::errors::CMNError;
use self::expression::{Expr, Operator, Atom};
use self::namespace::{Namespace, NamespaceItem, NamespaceASTElem, Identifier, ScopePath};
use self::semantic::Attribute;
use self::types::{Type, FnParamList, Basic, AggregateType, Visibility};

pub mod namespace;
pub mod lexer;
pub mod errors;
pub mod ast;
pub mod types;
pub mod expression;
pub mod semantic;
pub mod controlflow;

// Utility functions to make the code a bit cleaner

fn get_current() -> ParseResult<Token> {
	lexer::CURRENT_LEXER.with(|lexer| match lexer.borrow().current() {
		Some((_, tk)) => Ok(tk.clone()),
		None => Err(CMNError::UnexpectedEOF),
	})
}

fn get_next() -> ParseResult<Token> {
	lexer::CURRENT_LEXER.with(|lexer| match lexer.borrow_mut().next() {
		Some((_, tk)) => Ok(tk.clone()),
		None => Err(CMNError::UnexpectedEOF),
	})
}

fn get_current_start_index() -> usize {
	lexer::CURRENT_LEXER.with(|lexer| lexer.borrow().current().unwrap().0)
}

fn get_current_token_index() -> usize {
	lexer::CURRENT_LEXER.with(|lexer| lexer.borrow().current_token_index())
}

// Convenience function that matches a &str against various token kinds
fn token_compare(token: &Token, text: &str) -> bool {
	match token {
	    Token::Operator(op) => text == op.as_str(),
   		Token::Other(c) => text.chars().next().unwrap() == *c,
		Token::Keyword(keyword) => text == *keyword,
		_ => false,
	}
}




pub type ParseResult<T> = Result<T, CMNError>;
pub type ASTResult<T> = Result<T, (CMNError, TokenData)>;

pub struct Parser {
	active_namespace: Option<RefCell<Namespace>>,
	root_namespace: Option<RefCell<Namespace>>,
	verbose: bool,
}



impl Parser {
	pub fn new(verbose: bool) -> Parser {
		let result = Parser { 
			active_namespace: None,
    		root_namespace: None,
			verbose,
		};

		result
	}

	pub fn current_namespace(&self) -> &RefCell<Namespace> {
		self.active_namespace.as_ref().unwrap()
	}

	pub fn parse_module(&mut self) -> ParseResult<&RefCell<Namespace>> {

		lexer::CURRENT_LEXER.with(|lexer| {
			lexer.borrow_mut().tokenize_file().unwrap();
		});

		self.active_namespace = Some(RefCell::new(Namespace::new()));
		self.root_namespace = None;

		match self.parse_namespace() {
			Ok(()) => {
				
				if self.verbose {
					println!("\ngenerated namespace info:\n\n{}", self.current_namespace().borrow());
				}

				Ok(&self.current_namespace())
			}
			Err(e) => {
				Err(e)
			}
		}
	
	}


	pub fn generate_ast(&mut self) -> ParseResult<&RefCell<Namespace>> {
		self.generate_namespace(self.active_namespace.as_ref().unwrap())?;

		Ok(self.active_namespace.as_ref().unwrap())
	}


	fn generate_namespace<'a>(&self, namespace: &'a RefCell<Namespace>) -> ParseResult<&'a RefCell<Namespace>> {
		for child in &namespace.borrow().children {
			match &child.1.0 {

				NamespaceItem::Function(_, ast_elem) => {
					let mut elem = ast_elem.borrow_mut();
					match *elem {
						NamespaceASTElem::Unparsed(idx) => {
							// Parse function block
							lexer::CURRENT_LEXER.with(|lexer| lexer.borrow_mut().seek_token_idx(idx));
							*elem = NamespaceASTElem::Parsed(self.parse_block()?)
						}

						_ => {},
					}
				},

				NamespaceItem::Namespace(ns) => { self.generate_namespace(ns)?; },

				NamespaceItem::Type(_) => {},

				_ => todo!(),
			}
		};

		Ok(namespace)
	}



	pub fn parse_namespace(&mut self) -> ParseResult<()> {
		let mut current = get_current()?;
		let mut current_attributes = vec![];

		while current != Token::EOF && current != Token::Other('}') {
			match current {
				Token::EOF => {
					return Err(CMNError::UnexpectedEOF);
				},

				Token::Other(tk) => {
					match tk {
						';' => {
							get_next()?;
						}

						'}' => return Ok(()),

						'@' => {
							// Parse attributes
							while token_compare(&get_current()?, "@") {
								current_attributes.push(self.parse_attribute()?);
							}
						}

						_ => {
							return Err(CMNError::UnexpectedToken);
						}
					}
				},

				Token::Keyword(ref keyword) => {

					match *keyword {

						"class" | "struct" => {
							let mut current_visibility = if *keyword == "struct" { Visibility::Public } else { Visibility::Private };

							// Register aggregate type
							let mut aggregate = AggregateType::new();

							let name_token = get_next()?;
							
							if let Token::Identifier(name) = name_token {
								let mut next = get_next()?;

								if token_compare(&next, ":") {
									// TODO: Parse base classes
								} else if !token_compare(&next, "{") {
									return Err(CMNError::UnexpectedToken);
								}

								next = get_next()?; // Consume brace
								
								while !token_compare(&next, "}") {

									match next { 
										Token::Identifier(_) => {
											let result = self.parse_fn_or_declaration()?;

											aggregate.members.push(
												(result.0, (result.1, result.2, current_attributes, current_visibility.clone()))
											);
											
											next = get_current()?;
											current_attributes = vec![];
										} 

										Token::Keyword(k) => {
											match k {
												"public" =>		{ current_visibility = Visibility::Public; }
												"private" =>	{ current_visibility = Visibility::Private; }
												"protected" =>	{ current_visibility = Visibility::Protected; }
												_ => return Err(CMNError::UnexpectedKeyword),
											}
											get_next()?;
											next = get_next()?;
										}

										_ => return Err(CMNError::ExpectedIdentifier),
									}
								}

								get_next()?; // Consume closing brace

								let aggregate = Type::Aggregate(Box::new(aggregate));

								self.current_namespace().borrow_mut().children.insert(
									name.expect_scopeless()?, (
										NamespaceItem::Type(RefCell::new(aggregate)), 
										current_attributes,
										None
									)
								);
								current_attributes = vec![];
							}
						}

						"namespace" => {
							let name_token = get_next()?;

							if let Token::Identifier(namespace_name) = name_token {								
								get_next()?; // Consume name
								get_next()?; // Consume brace

								let self_is_root = self.root_namespace.is_none();

								let new_namespace = Namespace::from_parent(
									&self.current_namespace().borrow().path, 
									namespace_name.expect_scopeless()?
								);

								let mut old_namespace = self.current_namespace().replace(new_namespace);
								let parsed_namespace;

								if self_is_root {
									self.root_namespace.replace(RefCell::new(old_namespace));
									self.parse_namespace()?;
									old_namespace = self.root_namespace.as_mut().unwrap().take();
									self.root_namespace = None;
								} else {
									self.parse_namespace()?;
								}

								parsed_namespace = self.current_namespace().replace(old_namespace);

								self.current_namespace().borrow_mut().children.insert(
									namespace_name.name, 
									(
										NamespaceItem::Namespace(Box::new(RefCell::new(parsed_namespace))), 
										current_attributes,
										None
									)
								);

								current_attributes = vec![];
							} else {
								return Err(CMNError::ExpectedIdentifier);
							}
						}


						"using" => {
							// Register type alias/import statement
							let name_token = get_next()?;

							if let Token::Identifier(name) = name_token {
								self.current_namespace().borrow_mut().referenced_modules.insert(name.path.scopes[0].clone());
								// TODO: Implement

							} else {
								return Err(CMNError::ExpectedIdentifier);
							}
						}

						_ => {
							return Err(CMNError::UnexpectedToken);
						}
					}
				},

				Token::Identifier(_) => {
					// Parse declaration/definition
					let result = self.parse_fn_or_declaration()?;

					match result.1 {
						Type::Function(_, _) => {
							self.current_namespace().borrow_mut().children.insert(
								result.0, 
								(
									NamespaceItem::Function(RefCell::new(result.1), RefCell::new(result.2)), 
									current_attributes,
									None	
								)
							)
						},

						_ => todo!(),
					};
					
					current_attributes = vec![];
				}
				
				

				_ => { // Other types of tokens (literals etc) not valid at this point
					return Err(CMNError::UnexpectedToken);
				}
			}

			current = get_current()?;
		}

		if current == Token::EOF {
			if self.root_namespace.is_none() {
				Ok(())
			} else {
				Err(CMNError::UnexpectedEOF)
			}
		} else if current == Token::Other('}') {
			if self.root_namespace.is_some() {
				get_next()?;
				Ok(())
			} else {
				Err(CMNError::UnexpectedToken)
			}
		}
		else {
			get_next()?;
			Ok(())
		}
	}



	// Not super robust - add checks for namespace-level keywords and abort early if found
	fn skip_block(&self) -> ParseResult<Token> {	
		let mut current = get_current()?;
	
		if current != Token::Other('{') {
			return Err(CMNError::UnexpectedToken);
		}
		let mut bracket_depth = 1;

		while bracket_depth > 0 {
			current = get_next()?;

			match current {
				Token::Other('{') => bracket_depth += 1,
				Token::Other('}') => bracket_depth -= 1,
				Token::EOF => break,
				_ => {}
			}
		}

		Ok(get_next()?)
	}



	fn parse_block(&self) -> ParseResult<ASTElem> {
		let begin = get_current_start_index();
		let mut current = get_current()?;

		if current != Token::Other('{') {
			return Err(CMNError::UnexpectedToken);
		}
	
		let mut result = Vec::<ASTElem>::new();

		get_next()?;
		
		while get_current()? != Token::Other('}') {			
			let stmt = self.parse_statement()?;
			
			if self.verbose {
				stmt.print();
			}

			result.push(stmt);

			current = get_current()?;

			while current == Token::Other(';') {
				current = get_next()?;
			}

		}

		get_next()?; // consume closing bracket
		
		let end = get_current_start_index();

		Ok(ASTElem { node: ASTNode::Block(result), token_data: (begin, end - begin), type_info: RefCell::new(None)})
	}



	fn parse_statement(&self) -> ParseResult<ASTElem> {
		let mut current = get_current()?;
		let begin = get_current_start_index();
		let mut result = None;

		match &current {
		
			Token::Identifier(id) => {
				// Might be a declaration, check if identifier is a type
				let ns = self.current_namespace().borrow();
				let root = &self.root_namespace.as_ref().unwrap_or(self.current_namespace()).borrow();

				let mut type_found = false;
				ns.with_item(id, root, |item| type_found = matches!(item.0, NamespaceItem::Type(_)));
				
				if type_found {
					// Found a type that matches, so parse variable declaration
					
					let t = self.parse_type(true)?;
					let name = get_current()?;
					let mut expr = None;
					
					if token_compare(&get_next()?, "=") {
						get_next()?;
						expr = Some(Box::new(self.parse_expression()?));
					}
					self.check_semicolon()?;
					result = Some(ASTNode::Declaration(t, name, expr));
				};
			},

			Token::Keyword(keyword) => {
				match *keyword {
					
					// Parse return statement
					"return" => {
						let next = get_next()?;
						
						if next == Token::Other(';') {
							result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Return{expr: None})));
						} else {
							result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Return{expr: Some(self.parse_expression()?)})));
						}
						self.check_semicolon()?;
					}


					// Parse if statement
					"if" => {
						current = get_next()?;

						// Check opening brace
						if token_compare(&current, "(") {
							get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let cond = self.parse_expression()?;

						current = get_current()?;
						
						// Check closing brace
						if token_compare(&current, ")") {
							get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						// Parse body
						let body;
						let mut else_body = None;

						if token_compare(&get_current()?, "{") {
							body = self.parse_block()?;
						} else {
							body = self.parse_statement()?.wrap_in_block();
						}

						if token_compare(&get_current()?, "else") {
							get_next()?;
							
							if token_compare(&get_current()?, "{") {
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

					// Parse while loop
					"while" => {
						current = get_next()?;

						// Check opening brace
						if token_compare(&current, "(") {
							current = get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let cond;
						
						if token_compare(&current, ")") {
							// No condtion in while statement!
							return Err(CMNError::UnexpectedToken);
						} else {
							cond = self.parse_expression()?;
							current = get_current()?;
						}

						// Check closing brace
						if token_compare(&current, ")") {
							current = get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						// Parse body
						let body;
						if token_compare(&current, "{") {
							body = self.parse_block()?;
						} else {
							body = self.parse_statement()?.wrap_in_block();
						}

						result = Some(ASTNode::ControlFlow(
							Box::new(ControlFlow::While { 
								cond, body
							})
						));
					}

					// Parse for loop
					"for" => {
						current = get_next()?;

						// Check opening brace
						if token_compare(&current, "(") {
							current = get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let mut init = None;
						let mut cond = None;
						let mut iter = None;

						if token_compare(&current, ";") {
							// No init statement, skip
							current = get_next()?;
						} else {
							init = Some(self.parse_statement()?); // TODO: Restrict to declaration?
							current = get_current()?;
						}

						if token_compare(&current, ";") {
							// No iter expression, skip
							current = get_next()?;
						} else {
							cond = Some(self.parse_expression()?);
							self.check_semicolon()?;
							current = get_current()?;
						}

						if token_compare(&current, ";") {
							// No cond expression, skip
							current = get_next()?;
						} else if !token_compare(&current, ")") {
							iter = Some(self.parse_expression()?);
							current = get_current()?;
						}

						// Check closing brace
						if token_compare(&current, ")") {
							current = get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						// Parse body
						let body;
						if token_compare(&current, "{") {
							body = self.parse_block()?;
						} else {
							body = self.parse_statement()?.wrap_in_block();
						}

						result = Some(ASTNode::ControlFlow(
							Box::new(ControlFlow::For { 
								init, cond, iter, body
							})
						));
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
			let end = get_current_start_index();
			let len = end - begin;
			return Ok(ASTElem {node: result.unwrap(), token_data: (begin, len), type_info: RefCell::new(None)});
		}

		// Not any of the above, try parsing an expression
		let expr = self.parse_expression()?;
		self.check_semicolon()?;
		return Ok(expr);
	}



	fn check_semicolon(&self) -> ParseResult<()> {
		if token_compare(&get_current()?, ";") {
			get_next()?;
			Ok(())
		} else {
			Err(CMNError::UnexpectedToken)
		}
	}



	fn parse_fn_or_declaration(&self) -> ParseResult<(String, Type, NamespaceASTElem)> {
		let mut t = Type::Unresolved(match get_current()? { Token::Identifier(id) => id, _ => panic!() });
		let mut next = get_next()?;
		
		if let Token::Identifier(id) = next {
			next = get_next()?;

			let mut ast_elem = NamespaceASTElem::NoElem;

			if let Token::Operator(op) = next {
				match op.as_str() {
					
					// Function declaration
					"(" => {	
						t = Type::Function(
								Box::new(t),
								self.parse_parameter_list()?
							);
						
						// Past the parameter list, check if we're at a function body or not
						let current = get_current()?;
						
						if current == Token::Other('{') {
							
							ast_elem = NamespaceASTElem::Unparsed(get_current_token_index());
							self.skip_block()?;
							
						} else if current == Token::Other(';') {
							// No function body, just a semicolon
							get_next()?;
						} else {
							// Expected a function body or semicolon!
							return Err(CMNError::UnexpectedToken);
						}
					}

					"=" => {
						get_next()?;
						// TODO: Skip expression

						//ast_elem = match self.parse_expression()?.node {
						//	ASTNode::Expression(expr) => Some(
						//		ASTElem { 
						//			node: ASTNode::Expression(RefCell::new(expr.into_inner())), 
						//			type_info: RefCell::new(None),
						//			token_data: (0, 0) // TODO: Add
						//		}),
						//	_ => panic!(), // TODO: Error handling
						//};
					
						self.check_semicolon()?;
					}

					_ => {
						return Err(CMNError::UnexpectedToken);
					}
				}
			} else {
				self.check_semicolon()?;
			}

			// Register declaration to symbol table
			// TODO: Figure out what to do if the identifier has scopes
			Ok((id.name, t, ast_elem))
		} else {
			Err(CMNError::ExpectedIdentifier)
		}
	}




	fn parse_expression(&self) -> ParseResult<ASTElem> {
		let begin = get_current_start_index();
		let expr = ASTNode::Expression(RefCell::new(self.parse_expression_bp(0)?));
		let len = get_current_start_index() - begin;
		Ok(ASTElem { node: expr, token_data: (begin, len), type_info: RefCell::new(None)})
	}



	// World's most hacked-together pratt parser (tm)
	fn parse_expression_bp(&self, min_bp: u8) -> ParseResult<Expr> {
		let mut current = get_current()?;
		let begin_lhs = get_current_start_index();

		// Get initial part of expression, could be an Atom or the operator of a unary Cons
		let mut lhs = match current {
			
			// Parse atom
			Token::Identifier(_) | Token::StringLiteral(_) | Token::NumLiteral(_, _) | Token::BoolLiteral(_) => 
				Expr::Atom(self.parse_atom()?, (begin_lhs, get_current_start_index() - begin_lhs)),
			
			
			// Handle unary prefix operators
			Token::Operator(tk) => {
				match Operator::get_operator(&tk, false) {
					Some(op) => {
						get_next()?;
						
						if let Operator::Call = op {
							// Special case; parse sub-expression
							let sub = self.parse_expression_bp(0)?;

							current = get_current()?;

							if let Token::Operator(op) = current {
								if op.as_str() != ")" {
									return Err(CMNError::UnexpectedToken);
								}
								get_next()?;
								sub
							} else {
								return Err(CMNError::UnexpectedToken);
							}

						} else {
							let rhs = self.parse_expression_bp(op.get_binding_power())?;
							
							let end_index = get_current_start_index();

							let meta = (begin_lhs, end_index - begin_lhs);
							Expr::Cons(op, vec![(rhs,meta)], meta)
						}
					}

					None => return Err(CMNError::UnexpectedToken)
				}		
			}
			
			_ => { return Err(CMNError::UnexpectedToken); }
		};

		let end_lhs = get_current_start_index();

		// Parse RHS
		loop {
			let tk = get_current()?;

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
			
			get_next()?;

			let begin_rhs = get_current_start_index();

			if op == Operator::Cast {
				let goal_t = self.parse_type(true)?;

				let end_index = get_current_start_index();
				let meta = (begin_lhs, end_index - begin_lhs);
				
				lhs = Expr::create_cast(lhs, None, goal_t, meta);
			} else {
				let rhs = self.parse_expression_bp(rbp)?;

				let end_rhs = get_current_start_index();
				let lhs_meta = (begin_lhs, end_lhs - begin_lhs);
				let rhs_meta = (begin_rhs, end_rhs - begin_rhs);

				lhs = Expr::Cons(op, vec![(lhs, lhs_meta), (rhs, rhs_meta)], (begin_rhs, end_rhs - begin_rhs));
			}
		}

		Ok(lhs)
	}



	fn parse_atom(&self) -> ParseResult<Atom> {
		let mut current = get_current()?;
		let mut result;
		let mut next = get_next()?;

		match current {
			Token::Identifier(name) => {
				result = Atom::Identifier(name.clone());

				while let Token::Operator(ref op) = next {
					match op.as_str() {

						"(" => {
							// Function call
							let mut args = vec![];
							next = get_next()?;
							
							if next != Token::Operator(")".to_string()) {
								loop {									
									args.push(self.parse_expression()?);
									
									current = get_current()?;

									if let Token::Other(',') = current {
										get_next()?;
									} else if current == Token::Operator(")".to_string()) {
										break;
									} else {
										return Err(CMNError::UnexpectedToken);
									}
								}
							}
							get_next()?;

							result = Atom::FnCall{name: name.clone(), args};
							break;
						}

						"<" => {
							// TODO: Disambiguate between type parameter list or LT operator 
							result = Atom::Identifier(name.clone());
							break;
						}

						_ => {
							// Just a variable
							result = Atom::Identifier(name.clone());
							break;
						}
					} 
				};
			},

			Token::StringLiteral(s) => result = Atom::StringLit(s),
			
			Token::NumLiteral(s, suffix) => result = {
				let suffix_b = Basic::get_basic_type(suffix.as_str());
		
				if suffix_b.is_none() && !suffix.is_empty() {
					return Err(CMNError::InvalidSuffix);
				}

				let atom = if s.find('.').is_some() {
					Atom::FloatLit(s.parse::<f64>().unwrap(), suffix_b)			
				} else {
					Atom::IntegerLit(s.parse::<isize>().unwrap(), suffix_b)
				};

				atom
			},

			Token::BoolLiteral(b) => result = Atom::BoolLit(b),

			_ => return Err(CMNError::UnexpectedToken),
		};

		Ok(result)
	}

	

	fn parse_parameter_list(&self) -> ParseResult<FnParamList> {
		let next = get_next()?;
		let mut result = vec![];

		while let Token::Identifier(_) = next {
			let mut param = (Box::new(self.parse_type(false)?), None);
			
			
			// Check for param name
			let mut current = get_current()?;
			if let Token::Identifier(id) = current {
				// TODO: Add check for scopes here (illegal in param list)
				param.1 = Some(id.name);
				get_next()?;
			}
			
			result.push(param);

			// Check if we've arrived at a comma, skip it, and loop back around
			current = get_current()?;
			match current {
				Token::Other(',') => {
					get_next()?;
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

		let current = get_current()?;

		if let Token::Operator(s) = current {
			if s.as_str() == ")" {
				get_next()?;
				Ok(result)
			} else {
				Err(CMNError::UnexpectedToken)
			}
		} else {
			Err(CMNError::UnexpectedToken)
		}
	}



	/*fn parse_scoped_name(&self) -> ParseResult<Identifier> {
		let mut path = ScopePath { scopes: vec![], absolute: false };
		
		if let Token::Identifier(id) = get_current()? {
			path.scopes.push(id);
		} else {
			return Err(CMNError::ExpectedIdentifier);
		}

		while token_compare(&get_next()?, "::") {
			if let Token::Identifier(id) = get_next()? {
				path.scopes.push(id);
			} else {
				return Err(CMNError::ExpectedIdentifier);
			}
		}
		let name = path.scopes.pop().unwrap();

		Ok(Identifier{ name, path, mem_idx: 0, resolved: None })
	}*/



	fn parse_type(&self, immediate_resolve: bool) -> ParseResult<Type> {
		let mut result = Type::Unresolved(Identifier {name: "(none)".to_string(), path: ScopePath::new(false), mem_idx: 0, resolved: None });
		let current = get_current()?;

		if let Token::Identifier(typename) = current {
			// Typename

			if immediate_resolve {
				let ctx = self.current_namespace().borrow();
				let root = &self.root_namespace.as_ref().unwrap_or(self.current_namespace()).borrow();
				
				let mut found = false;
				ctx.with_item(&typename, root, |item| {
					if let NamespaceItem::Type(t) = &item.0 {
						result = t.borrow().clone();
						found = true;
					}
				});

				if !found {
					return Err(CMNError::UnresolvedTypename(typename.to_string()));
				}
				
			} else {
				result = Type::Unresolved(typename);
			}

			let mut next = get_next()?;
		
			match next { 
				Token::Operator(ref op) => {
					match op.as_str() {
						"*" => {
							while token_compare(&next, "*") {
								result = Type::Pointer(Box::new(result));
								next = get_next()?;
							}
						}
						
						"<" => {
							get_next()?;
							
							//let generic = self.parse_type()?;
							//result.generics.push(generic);
							
							while get_current()? == Token::Other(',') {
								get_next()?;
								
								//let generic = self.parse_type()?;
								//result.generics.push(generic);
							}

							// assert token == '>'
							if get_current()? != Token::Operator(">".to_string()) {
								return Err(CMNError::UnexpectedToken)
							}
							// consume >
							get_next()?;
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


	fn parse_attribute(&self) -> ParseResult<Attribute> {
		if !token_compare(&get_current()?, "@") {
			return Err(CMNError::UnexpectedToken); // You called this from the wrong place lol
		}

		let name = get_next()?;
		let mut result;
		
		if let Token::Identifier(name) = name {
			result = Attribute { name: name.expect_scopeless()?, args: vec![] };
		} else {
			return Err(CMNError::ExpectedIdentifier);
		}

		let mut current = get_next()?;

		if token_compare(&current, "(") {
			if current != Token::Operator(")".to_string()) {
				loop {									
					result.args.push(self.parse_expression()?);
					
					current = get_current()?;

					if let Token::Other(',') = current {
						get_next()?;
					} else if current == Token::Operator(")".to_string()) {
						break;
					} else {
						return Err(CMNError::UnexpectedToken);
					}
				}
			}
			get_next()?;
		}

		Ok(result)
	}
}