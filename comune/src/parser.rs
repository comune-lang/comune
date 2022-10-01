use std::cell::RefCell;
use std::sync::{Arc, RwLock};

use crate::constexpr::ConstExpr;
use crate::errors::CMNError;
use crate::lexer::{Lexer, Token};

use crate::semantic::ast::{ASTElem, ASTNode, TokenData};
use crate::semantic::controlflow::ControlFlow;
use crate::semantic::expression::{Atom, Expr, Operator};
use crate::semantic::namespace::{
	Identifier, Namespace, NamespaceASTElem, NamespaceItem, ScopePath,
};
use crate::semantic::types::{AlgebraicType, Basic, FnParamList, Type, TypeDef, Visibility};
use crate::semantic::Attribute;

// Convenience function that matches a &str against various token kinds
fn token_compare(token: &Token, text: &str) -> bool {
	match token {
		Token::Operator(op) => text == *op,
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
	pub lexer: RefCell<Lexer>,
}

impl Parser {
	pub fn new(lexer: Lexer, verbose: bool) -> Parser {
		let result = Parser {
			active_namespace: None,
			root_namespace: None,
			lexer: RefCell::new(lexer),
			verbose,
		};

		result
	}

	fn get_current(&self) -> ParseResult<Token> {
		match self.lexer.borrow().current() {
			Some((_, tk)) => Ok(tk.clone()),
			None => Err(CMNError::UnexpectedEOF),
		}
	}

	fn get_next(&self) -> ParseResult<Token> {
		match self.lexer.borrow_mut().next() {
			Some((_, tk)) => Ok(tk.clone()),
			None => Err(CMNError::UnexpectedEOF),
		}
	}

	fn get_current_start_index(&self) -> usize {
		self.lexer.borrow().current().unwrap().0
	}

	fn get_current_token_index(&self) -> usize {
		self.lexer.borrow().current_token_index()
	}

	pub fn current_namespace(&self) -> &RefCell<Namespace> {
		self.active_namespace.as_ref().unwrap()
	}

	pub fn parse_module(&mut self) -> ParseResult<&RefCell<Namespace>> {
		self.lexer.borrow_mut().tokenize_file().unwrap();
		self.active_namespace = Some(RefCell::new(Namespace::new()));
		self.root_namespace = None;

		match self.parse_namespace() {
			Ok(()) => {
				if self.verbose {
					println!(
						"\ngenerated namespace info:\n\n{}",
						self.current_namespace().borrow()
					);
				}

				Ok(&self.current_namespace())
			}
			Err(e) => Err(e),
		}
	}

	pub fn generate_ast(&mut self) -> ParseResult<&RefCell<Namespace>> {
		self.generate_namespace(self.active_namespace.as_ref().unwrap())?;

		Ok(self.active_namespace.as_ref().unwrap())
	}

	fn generate_namespace<'a>(
		&self,
		namespace: &'a RefCell<Namespace>,
	) -> ParseResult<&'a RefCell<Namespace>> {
		for child in &namespace.borrow().children {
			match &child.1 .0 {
				NamespaceItem::Function(_, ast_elem) => {
					let mut elem = ast_elem.borrow_mut();
					match *elem {
						NamespaceASTElem::Unparsed(idx) => {
							// Parse function block
							self.lexer.borrow_mut().seek_token_idx(idx);
							*elem = NamespaceASTElem::Parsed(self.parse_block()?)
						}

						_ => {}
					}
				}

				NamespaceItem::Namespace(ns) => {
					self.generate_namespace(ns)?;
				}

				NamespaceItem::Type(_) => {}

				NamespaceItem::Alias(_) => {}

				_ => todo!(),
			}
		}

		for im in &namespace.borrow().impls {
			// Generate impl function bodies
			for method in im.1 {
				let mut elem = method.2.borrow_mut();
				match *elem {
					NamespaceASTElem::Unparsed(idx) => {
						// Parse method block
						self.lexer.borrow_mut().seek_token_idx(idx);
						*elem = NamespaceASTElem::Parsed(self.parse_block()?)
					}

					_ => {}
				}
			}
		}

		Ok(namespace)
	}

	pub fn parse_namespace(&mut self) -> ParseResult<()> {
		let mut current = self.get_current()?;
		let mut current_attributes = vec![];

		while current != Token::EOF && current != Token::Other('}') {
			match current {
				Token::EOF => {
					return Err(CMNError::UnexpectedEOF);
				}

				Token::Other(tk) => {
					match tk {
						';' => {
							self.get_next()?;
						}

						'}' => return Ok(()),

						'@' => {
							// Parse attributes
							while token_compare(&self.get_current()?, "@") {
								current_attributes.push(self.parse_attribute()?);
							}
						}

						_ => {
							return Err(CMNError::UnexpectedToken);
						}
					}
				}

				Token::Keyword(keyword) => {
					match keyword {
						"enum" => {
							todo!()
						}

						"struct" => {
							// Register algebraic type
							let mut current_visibility = Visibility::Public;
							let mut aggregate = AlgebraicType::new();
							let name_token = self.get_next()?;

							if let Token::Identifier(name) = name_token {
								let mut next = self.get_next()?;

								if !token_compare(&next, "{") {
									return Err(CMNError::UnexpectedToken);
								}

								next = self.get_next()?; // Consume brace

								while !token_compare(&next, "}") {
									match next {
										Token::Identifier(_) => {
											let result = self.parse_namespace_declaration()?;

											match result.1 {
												NamespaceItem::Variable(t, n) => {
													aggregate.items.push((
														result.0,
														(
															NamespaceItem::Variable(t, n),
															vec![],
															None,
														),
														current_visibility.clone(),
													))
												}

												_ => todo!(),
											}

											next = self.get_current()?;
										}

										Token::Keyword(k) => {
											match k {
												"public" => {
													current_visibility = Visibility::Public;
												}
												"private" => {
													current_visibility = Visibility::Private;
												}
												"protected" => {
													current_visibility = Visibility::Protected;
												}
												_ => return Err(CMNError::UnexpectedKeyword),
											}
											self.get_next()?;
											next = self.get_next()?;
										}

										_ => return Err(CMNError::ExpectedIdentifier),
									}
								}

								self.get_next()?; // Consume closing brace

								let aggregate = TypeDef::Algebraic(Box::new(aggregate));

								self.current_namespace().borrow_mut().children.insert(
									name.expect_scopeless()?,
									(
										NamespaceItem::Type(Arc::new(RwLock::new(aggregate))),
										current_attributes,
										None,
									),
								);
								current_attributes = vec![];
							}
						}

						"namespace" => {
							let name_token = self.get_next()?;

							if let Token::Identifier(namespace_name) = name_token {
								self.get_next()?; // Consume name
								self.get_next()?; // Consume brace

								let self_is_root = self.root_namespace.is_none();

								let new_namespace = Namespace::from_parent(
									&self.current_namespace().borrow().path,
									namespace_name.expect_scopeless()?,
								);

								let mut old_namespace =
									self.current_namespace().replace(new_namespace);
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
										NamespaceItem::Namespace(Box::new(RefCell::new(
											parsed_namespace,
										))),
										current_attributes,
										None,
									),
								);

								current_attributes = vec![];
							} else {
								return Err(CMNError::ExpectedIdentifier);
							}
						}

						"impl" => {
							let impl_name_token = self.get_next()?;
							let impl_name;
							let mut _trait_name = None;

							if let Token::Identifier(id) = &impl_name_token {
								match self.get_next()? {
									Token::Other('{') => {
										// Regular impl
										impl_name = id.clone();
										self.get_next()?;
									}

									Token::Keyword("for") => {
										// Trait impl
										_trait_name = Some(id);

										if let Token::Identifier(id) = self.get_next()? {
											impl_name = id;
										} else {
											return Err(CMNError::ExpectedIdentifier);
										}

										if !token_compare(&self.get_next()?, "{") {
											return Err(CMNError::UnexpectedToken);
										}

										self.get_next()?;
									}

									_ => return Err(CMNError::UnexpectedToken),
								}

								let mut current = self.get_current()?;

								// Parse functions

								while current != Token::Other('}') {
									let fn_ret = self.parse_type(false)?;

									let fn_name =
										if let Token::Identifier(id) = self.get_current()? {
											id.expect_scopeless()?
										} else {
											return Err(CMNError::ExpectedIdentifier);
										};

									self.get_next()?;

									let fn_params = self.parse_parameter_list()?;

									let ast_elem =
										NamespaceASTElem::Unparsed(self.get_current_token_index());
									self.skip_block()?;

									// Register impl
									let impls = &mut self.current_namespace().borrow_mut().impls;

									let current_impl = (
										fn_name,
										Arc::new(RwLock::new(TypeDef::Function(fn_ret, fn_params))),
										RefCell::new(ast_elem),
										None,
									);

									if let Some(impls) = impls.get_mut(&impl_name) {
										impls.push(current_impl);
									} else {
										impls.insert(impl_name.clone(), vec![current_impl]);
									}

									current = self.get_current()?;
								}

								self.get_next()?;
							} else {
								return Err(CMNError::ExpectedIdentifier);
							}
						}

						"import" => {
							// Register import statement
							if let Token::Identifier(name) = self.get_next()? {
								self.current_namespace()
									.borrow_mut()
									.referenced_modules
									.insert(name);
								self.get_next()?;
								self.check_semicolon()?;
							} else {
								return Err(CMNError::ExpectedIdentifier);
							}
						}

						"using" => {
							if let Token::Identifier(name) = self.get_next()? {
								if token_compare(&self.get_next()?, "=") {
									// Found a '=' token, so fetch the name to alias
									if let Token::Identifier(aliased) = self.get_next()? {
										self.current_namespace().borrow_mut().children.insert(
											name.expect_scopeless()?,
											(NamespaceItem::Alias(aliased), vec![], None),
										);

										self.get_next()?;
										self.check_semicolon()?;
									} else {
										return Err(CMNError::ExpectedIdentifier);
									}
								} else {
									// No '=' token, just bring the name into scope
									self.current_namespace().borrow_mut().children.insert(
										name.name.clone(),
										(NamespaceItem::Alias(name), vec![], None),
									);

									self.check_semicolon()?;
								}
							}
						}

						_ => {
							return Err(CMNError::UnexpectedToken);
						}
					}
				}

				Token::Identifier(_) => {
					// Parse declaration/definition
					let result = self.parse_namespace_declaration()?;

					match result.1 {
						NamespaceItem::Function(_, _) => self
							.current_namespace()
							.borrow_mut()
							.children
							.insert(result.0, (result.1, current_attributes, None)),

						_ => todo!(),
					};

					current_attributes = vec![];
				}

				_ => {
					// Other types of tokens (literals etc) not valid at this point
					return Err(CMNError::UnexpectedToken);
				}
			}

			current = self.get_current()?;
		}

		if current == Token::EOF {
			if self.root_namespace.is_none() {
				Ok(())
			} else {
				Err(CMNError::UnexpectedEOF)
			}
		} else if current == Token::Other('}') {
			if self.root_namespace.is_some() {
				self.get_next()?;
				Ok(())
			} else {
				Err(CMNError::UnexpectedToken)
			}
		} else {
			self.get_next()?;
			Ok(())
		}
	}

	// Not super robust - add checks for namespace-level keywords and abort early if found
	fn skip_block(&self) -> ParseResult<Token> {
		let mut current = self.get_current()?;

		if current != Token::Other('{') {
			return Err(CMNError::UnexpectedToken);
		}
		let mut bracket_depth = 1;

		while bracket_depth > 0 {
			current = self.get_next()?;

			match current {
				Token::Other('{') => bracket_depth += 1,
				Token::Other('}') => bracket_depth -= 1,
				Token::EOF => break,
				_ => {}
			}
		}

		Ok(self.get_next()?)
	}

	fn parse_block(&self) -> ParseResult<ASTElem> {
		let begin = self.get_current_start_index();
		let mut current = self.get_current()?;

		if current != Token::Other('{') {
			return Err(CMNError::UnexpectedToken);
		}

		let mut result = Vec::<ASTElem>::new();

		self.get_next()?;

		while self.get_current()? != Token::Other('}') {
			let stmt = self.parse_statement()?;

			if self.verbose {
				stmt.print();
			}

			result.push(stmt);

			current = self.get_current()?;

			while current == Token::Other(';') {
				current = self.get_next()?;
			}
		}

		self.get_next()?; // consume closing bracket

		let end = self.get_current_start_index();

		Ok(ASTElem {
			node: ASTNode::Block(result),
			token_data: (begin, end - begin),
			type_info: RefCell::new(None),
		})
	}

	fn parse_statement(&self) -> ParseResult<ASTElem> {
		let mut current = self.get_current()?;
		let begin = self.get_current_start_index();
		let mut result = None;

		if self.is_at_type_token(true)? {
			// This is a variable declaration

			let t = self.parse_type(true)?;
			let name = self.get_current()?;
			let mut expr = None;

			if token_compare(&self.get_next()?, "=") {
				self.get_next()?;
				expr = Some(Box::new(self.parse_expression()?));
			}
			self.check_semicolon()?;
			result = Some(ASTNode::Declaration(t, name, expr));
		} else {
			// This isn't a variable declaration, check if it's a control flow statement
			if let Token::Keyword(keyword) = &current {
				match *keyword {
					// Parse return statement
					"return" => {
						let next = self.get_next()?;

						if next == Token::Other(';') {
							result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Return {
								expr: None,
							})));
						} else {
							result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Return {
								expr: Some(self.parse_expression()?),
							})));
						}
						self.check_semicolon()?;
					}

					"break" => {
						let _next = self.get_next()?;
						// TODO: Labeled break and continue
						result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Break)));
						self.check_semicolon()?;
					}

					"continue" => {
						let _next = self.get_next()?;
						// TODO: Labeled break and continue
						result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Continue)));
						self.check_semicolon()?;
					}

					// Parse if statement
					"if" => {
						current = self.get_next()?;

						// Check opening brace
						if token_compare(&current, "(") {
							self.get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let cond = self.parse_expression()?;

						current = self.get_current()?;

						// Check closing brace
						if token_compare(&current, ")") {
							self.get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						// Parse body
						let body;
						let mut else_body = None;

						if token_compare(&self.get_current()?, "{") {
							body = self.parse_block()?;
						} else {
							body = self.parse_statement()?.wrap_in_block();
						}

						if token_compare(&self.get_current()?, "else") {
							self.get_next()?;

							if token_compare(&self.get_current()?, "{") {
								else_body = Some(self.parse_block()?);
							} else {
								else_body = Some(self.parse_statement()?.wrap_in_block());
							}
						}

						result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::If {
							cond,
							body,

							// TODO: Add proper metadata to this
							else_body: match else_body {
								None => None,
								Some(e) => Some(e),
							},
						})));
					}

					// Parse while loop
					"while" => {
						current = self.get_next()?;

						// Check opening brace
						if token_compare(&current, "(") {
							current = self.get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let cond;

						if token_compare(&current, ")") {
							// No condtion in while statement!
							return Err(CMNError::UnexpectedToken);
						} else {
							cond = self.parse_expression()?;
							current = self.get_current()?;
						}

						// Check closing brace
						if token_compare(&current, ")") {
							current = self.get_next()?;
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

						result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::While {
							cond,
							body,
						})));
					}

					// Parse for loop
					"for" => {
						current = self.get_next()?;

						// Check opening brace
						if token_compare(&current, "(") {
							current = self.get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let mut init = None;
						let mut cond = None;
						let mut iter = None;

						if token_compare(&current, ";") {
							// No init statement, skip
							current = self.get_next()?;
						} else {
							init = Some(self.parse_statement()?); // TODO: Restrict to declaration?
							current = self.get_current()?;
						}

						if token_compare(&current, ";") {
							// No iter expression, skip
							current = self.get_next()?;
						} else {
							cond = Some(self.parse_expression()?);
							self.check_semicolon()?;
							current = self.get_current()?;
						}

						if token_compare(&current, ";") {
							// No cond expression, skip
							current = self.get_next()?;
						} else if !token_compare(&current, ")") {
							iter = Some(self.parse_expression()?);
							current = self.get_current()?;
						}

						// Check closing brace
						if token_compare(&current, ")") {
							current = self.get_next()?;
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

						result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::For {
							init,
							cond,
							iter,
							body,
						})));
					}

					// Invalid keyword at start of statement
					_ => return Err(CMNError::UnexpectedKeyword),
				}
			}
		}

		// Check if we found a valid interpretation of the statement yet. If not, parse it as an expression
		if result.is_some() {
			let end = self.get_current_start_index();
			let len = end - begin;
			return Ok(ASTElem {
				node: result.unwrap(),
				token_data: (begin, len),
				type_info: RefCell::new(None),
			});
		}

		// Not any of the above, try parsing an expression
		let expr = self.parse_expression()?;
		self.check_semicolon()?;
		return Ok(expr);
	}

	fn check_semicolon(&self) -> ParseResult<()> {
		if token_compare(&self.get_current()?, ";") {
			self.get_next()?;
			Ok(())
		} else {
			Err(CMNError::UnexpectedToken)
		}
	}

	fn parse_namespace_declaration(&self) -> ParseResult<(String, NamespaceItem)> {
		let t = self.parse_type(false)?;
		let item;
		let mut next = self.get_current()?;

		if let Token::Identifier(id) = next {
			next = self.get_next()?;

			if let Token::Operator(op) = next {
				match op {
					// Function declaration
					"(" => {
						let t = TypeDef::Function(t, self.parse_parameter_list()?);

						// Past the parameter list, check if we're at a function body or not
						let current = self.get_current()?;
						let ast_elem;

						if current == Token::Other('{') {
							ast_elem = NamespaceASTElem::Unparsed(self.get_current_token_index());
							self.skip_block()?;
						} else if current == Token::Other(';') {
							ast_elem = NamespaceASTElem::NoElem;
							self.get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						item = NamespaceItem::Function(
							Arc::new(RwLock::new(t)),
							RefCell::new(ast_elem),
						);
					}

					"=" => {
						self.get_next()?;
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
						todo!();
					}

					_ => {
						return Err(CMNError::UnexpectedToken);
					}
				}
			} else {
				item = NamespaceItem::Variable(t, RefCell::new(NamespaceASTElem::NoElem));
				self.check_semicolon()?;
			}

			// Register declaration to symbol table
			// TODO: Figure out what to do if the identifier has scopes
			Ok((id.name, item))
		} else {
			Err(CMNError::ExpectedIdentifier)
		}
	}

	fn parse_expression(&self) -> ParseResult<ASTElem> {
		let begin = self.get_current_start_index();
		let expr = ASTNode::Expression(RefCell::new(self.parse_expression_bp(0)?));
		let len = self.get_current_start_index() - begin;
		Ok(ASTElem {
			node: expr,
			token_data: (begin, len),
			type_info: RefCell::new(None),
		})
	}

	// World's most hacked-together pratt parser (tm)
	fn parse_expression_bp(&self, min_bp: u8) -> ParseResult<Expr> {
		let mut current = self.get_current()?;
		let begin_lhs = self.get_current_start_index();

		// Get initial part of expression, could be an Atom or the operator of a unary Cons
		let mut lhs = match current {
			// Parse atom
			Token::Identifier(_)
			| Token::StringLiteral(_)
			| Token::NumLiteral(_, _)
			| Token::BoolLiteral(_) => Expr::Atom(
				self.parse_atom()?,
				(begin_lhs, self.get_current_start_index() - begin_lhs),
			),

			// Handle unary prefix operators
			Token::Operator(tk) => {
				match Operator::get_operator(&tk, false) {
					Some(op) => {
						self.get_next()?;

						if let Operator::Call = op {
							// Special case; parse sub-expression
							let sub = self.parse_expression_bp(0)?;

							current = self.get_current()?;

							if let Token::Operator(op) = current {
								if op != ")" {
									return Err(CMNError::UnexpectedToken);
								}
								self.get_next()?;
								sub
							} else {
								return Err(CMNError::UnexpectedToken);
							}
						} else {
							let rhs = self.parse_expression_bp(op.get_binding_power())?;

							let end_index = self.get_current_start_index();

							let meta = (begin_lhs, end_index - begin_lhs);
							Expr::Cons(op, vec![(rhs, None, meta)], meta)
						}
					}

					None => return Err(CMNError::UnexpectedToken),
				}
			}

			_ => {
				return Err(CMNError::UnexpectedToken);
			}
		};

		let end_lhs = self.get_current_start_index();

		// Parse RHS
		loop {
			let tk = self.get_current()?;

			let op = match tk {
				Token::Operator(op) => match Operator::get_operator(&op, true) {
					Some(result) => result,
					None => break,
				},

				_ => break,
			};

			let binding_power = op.get_binding_power();
			let (lbp, rbp);

			if op.is_associative_rtl() {
				lbp = binding_power + 1;
				rbp = binding_power;
			} else {
				lbp = binding_power;
				rbp = binding_power + 1;
			}

			if lbp < min_bp {
				break;
			}

			self.get_next()?;

			let begin_rhs = self.get_current_start_index();

			if op == Operator::Cast {
				let goal_t = self.parse_type(true)?;

				let end_index = self.get_current_start_index();
				let meta = (begin_lhs, end_index - begin_lhs);

				lhs = Expr::create_cast(lhs, None, goal_t, meta);
			} else {
				let rhs = self.parse_expression_bp(rbp)?;

				let end_rhs = self.get_current_start_index();
				let lhs_meta = (begin_lhs, end_lhs - begin_lhs);
				let rhs_meta = (begin_rhs, end_rhs - begin_rhs);

				lhs = Expr::Cons(
					op,
					vec![(lhs, None, lhs_meta), (rhs, None, rhs_meta)],
					(begin_rhs, end_rhs - begin_rhs),
				);
			}
		}

		Ok(lhs)
	}

	fn parse_atom(&self) -> ParseResult<Atom> {
		let mut current = self.get_current()?;
		let mut result;
		let mut next = self.get_next()?;

		match current {
			Token::Identifier(name) => {
				result = None;

				if let Some(Type::TypeRef(ty, id)) = self.find_type(&name) {
					match &*ty.upgrade().unwrap().read().unwrap() {
						// Parse with algebraic typename
						TypeDef::Algebraic(_) => {
							match &next {
								Token::Other('{') => {
									// Parse initializers
									let mut inits = vec![];

									while next != Token::Other('}') {
										if let Token::Identifier(member_name) = self.get_next()? {
											if self.get_next()? != Token::Other(':') {
												return Err(CMNError::UnexpectedToken);
											}

											self.get_next()?;

											let expr = match self.parse_expression()?.node {
												ASTNode::Expression(expr) => expr,
												_ => panic!(),
											};

											inits.push((
												Some(member_name.expect_scopeless()?),
												expr,
												(0, 0),
											));
										} else {
											return Err(CMNError::UnexpectedToken);
										}

										next = self.get_current()?;
									}

									self.get_next()?;

									result = Some(Atom::AlgebraicLit(
										Type::TypeRef(ty.clone(), id.clone()),
										inits,
									));
								}

								_ => return Err(CMNError::UnexpectedToken),
							}
						}

						_ => {}
					}
				}

				if result.is_none() {
					// Variable or function name
					result = Some(Atom::Identifier(name.clone()));
					while let Token::Operator(op) = next {
						match op {
							"(" => {
								// Function call
								let mut args = vec![];
								next = self.get_next()?;

								if next != Token::Operator(")") {
									loop {
										args.push(self.parse_expression()?);

										current = self.get_current()?;

										if let Token::Other(',') = current {
											self.get_next()?;
										} else if current == Token::Operator(")") {
											break;
										} else {
											return Err(CMNError::UnexpectedToken);
										}
									}
								}
								self.get_next()?;

								result = Some(Atom::FnCall {
									name: name.clone(),
									args,
								});
								break;
							}

							"<" => {
								// TODO: Generics
								result = Some(Atom::Identifier(name.clone()));
								break;
							}

							_ => break,
						}
					}
				}
			}

			Token::StringLiteral(s) => result = Some(Atom::StringLit(s)),

			Token::NumLiteral(s, suffix) => {
				result = {
					let mut suffix_b = Basic::get_basic_type(suffix.as_str());

					if suffix_b.is_none() && !suffix.is_empty() {
						suffix_b = match suffix.as_str() {
							// Add special numeric suffixes here
							"f" => Some(Basic::FLOAT { size_bytes: 4 }),

							_ => return Err(CMNError::InvalidSuffix),
						};
					}

					let atom = if s.find('.').is_some() {
						Atom::FloatLit(s.parse::<f64>().unwrap(), suffix_b)
					} else {
						Atom::IntegerLit(s.parse::<i128>().unwrap(), suffix_b)
					};

					Some(atom)
				}
			}

			Token::BoolLiteral(b) => result = Some(Atom::BoolLit(b)),

			_ => return Err(CMNError::UnexpectedToken),
		};

		Ok(result.unwrap())
	}

	fn find_type(&self, typename: &Identifier) -> Option<Type> {
		if typename.path.scopes.is_empty() {
			if let Some(basic) = Basic::get_basic_type(&typename.name) {
				return Some(Type::Basic(basic));
			}
		}
		let ctx = self.current_namespace().borrow();
		let root = &self
			.root_namespace
			.as_ref()
			.unwrap_or(self.current_namespace())
			.borrow();

		let mut result = None;
		ctx.with_item(&typename, root, |item, id| match &item.0 {
			NamespaceItem::Type(t) | NamespaceItem::Function(t, _) => {
				result = Some(Type::TypeRef(Arc::downgrade(t), id.clone()))
			}

			_ => {}
		});

		result
	}

	// Returns true if the current token is the start of a Type.
	// In ambiguous contexts (i.e. function blocks), `resolve_idents` enables basic name resolution
	fn is_at_type_token(&self, resolve_idents: bool) -> ParseResult<bool> {
		match self.get_current()? {
			Token::Identifier(typename) => {
				if resolve_idents {
					let mut found = false;

					if Basic::get_basic_type(&typename.name).is_some()
						&& typename.path.scopes.is_empty()
					{
						found = true;
					} else {
						let ctx = self.current_namespace().borrow();
						let root = &self
							.root_namespace
							.as_ref()
							.unwrap_or(self.current_namespace())
							.borrow();

						ctx.with_item(&typename, root, |item, _| {
							if let NamespaceItem::Type(_) = &item.0 {
								found = true;
							}
						});
					}

					Ok(found)
				} else {
					Ok(true)
				}
			}

			Token::Keyword(kw) => Ok(match kw {
				"mut" | "const" | "ref" => true,

				_ => false,
			}),

			_ => Ok(false),
		}
	}

	fn parse_parameter_list(&self) -> ParseResult<FnParamList> {
		let mut result = vec![];

		if token_compare(&self.get_current()?, "(") {
			self.get_next()?;
		} else {
			return Err(CMNError::UnexpectedToken);
		}

		while self.is_at_type_token(false)? {
			let mut param = (self.parse_type(false)?, None);

			// Check for param name
			let mut current = self.get_current()?;
			if let Token::Identifier(id) = current {
				param.1 = Some(id.expect_scopeless()?);
				self.get_next()?;
			}

			result.push(param);

			// Check if we've arrived at a comma, skip it, and loop back around
			current = self.get_current()?;

			match current {
				Token::Other(',') => {
					self.get_next()?;
					continue;
				}

				Token::Operator(")") => break,

				_ => {
					return Err(CMNError::UnexpectedToken);
				}
			}
		}

		let current = self.get_current()?;

		if let Token::Operator(s) = current {
			if s == ")" {
				self.get_next()?;
				Ok(result)
			} else {
				Err(CMNError::UnexpectedToken)
			}
		} else {
			Err(CMNError::UnexpectedToken)
		}
	}

	fn parse_type(&self, immediate_resolve: bool) -> ParseResult<Type> {
		let mut result = Type::Unresolved(Identifier {
			name: "(none)".to_string(),
			path: ScopePath::new(false),
			mem_idx: 0,
			resolved: None,
		});

		if self.is_at_type_token(immediate_resolve)? {
			let mut current = self.get_current()?;
			let typename;

			// TODO: Actually do something with these
			while let Token::Keyword(kw) = current {
				match kw {
					"const" => {}
					"mut" => {}
					"ref" => {}
					_ => return Err(CMNError::UnexpectedKeyword),
				}
				current = self.get_next()?;
			}

			if let Token::Identifier(id) = current {
				typename = id;
			} else {
				return Err(CMNError::ExpectedIdentifier);
			}

			// Typename

			if immediate_resolve {
				let ctx = self.current_namespace().borrow();
				let root = &self
					.root_namespace
					.as_ref()
					.unwrap_or(self.current_namespace())
					.borrow();

				let mut found = false;

				if let Some(b) = Basic::get_basic_type(&typename.name) {
					if typename.path.scopes.is_empty() {
						result = Type::Basic(b);
						found = true;
					}
				} else {
					ctx.with_item(&typename, root, |item, id| {
						if let NamespaceItem::Type(t) = &item.0 {
							result = Type::TypeRef(Arc::downgrade(t), id.clone());
							found = true;
						}
					});
				}

				if !found {
					return Err(CMNError::UnresolvedTypename(typename.to_string()));
				}
			} else {
				result = Type::Unresolved(typename);
			}

			let mut next = self.get_next()?;

			match next {
				Token::Operator(op) => {
					match op {
						"*" => {
							while token_compare(&next, "*") {
								result = Type::Pointer(Box::new(result));
								next = self.get_next()?;
							}
						}

						"[" => {
							self.get_next()?;
							let const_expr = self.parse_expression()?;
							let dummy_expr = Expr::Atom(Atom::IntegerLit(0, None), (0, 0));

							if self.get_current()? != Token::Operator("]") {
								return Err(CMNError::UnexpectedToken);
							}

							result = Type::Array(
								Box::new(result),
								RefCell::new(vec![ConstExpr::Expr(
									const_expr.get_expr().replace(dummy_expr),
								)]),
							);

							self.get_next()?;
						}

						"<" => {
							self.get_next()?;

							//let generic = self.parse_type()?;
							//result.generics.push(generic);

							while self.get_current()? == Token::Other(',') {
								self.get_next()?;

								//let generic = self.parse_type()?;
								//result.generics.push(generic);
							}

							// assert token == '>'
							if self.get_current()? != Token::Operator(">") {
								return Err(CMNError::UnexpectedToken);
							}
							// consume >
							self.get_next()?;
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
		if !token_compare(&self.get_current()?, "@") {
			return Err(CMNError::UnexpectedToken); // You called this from the wrong place lol
		}

		let name = self.get_next()?;
		let mut result;

		if let Token::Identifier(name) = name {
			result = Attribute {
				name: name.expect_scopeless()?,
				args: vec![],
			};
		} else {
			return Err(CMNError::ExpectedIdentifier);
		}

		let mut current = self.get_next()?;

		if token_compare(&current, "(") {
			current = self.get_next()?;

			if current != Token::Operator(")") {
				let mut current_seq = vec![];
				let mut paren_depth = 0;

				loop {
					match current {
						Token::Other(',') => {
							if paren_depth == 0 {
								result.args.push(current_seq);
								current_seq = vec![];
								current = self.get_next()?;
								continue;
							}
						}

						Token::Operator(op) => match op {
							"(" => paren_depth += 1,

							")" => {
								if paren_depth == 0 {
									result.args.push(current_seq);
									break;
								} else {
									paren_depth -= 1
								}
							}

							_ => {}
						},
						_ => {}
					}

					current_seq.push(current);
					current = self.get_next()?;
				}
			}
			self.get_next()?;
		}

		Ok(result)
	}
}
