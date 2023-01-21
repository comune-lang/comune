use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

use crate::ast::pattern::{Binding, Pattern};
use crate::constexpr::ConstExpr;
use crate::errors::{CMNError, CMNErrorCode};
use crate::lexer::{Lexer, Token};

use crate::ast::controlflow::ControlFlow;
use crate::ast::expression::{Atom, Expr, FnRef, NodeData, Operator};
use crate::ast::namespace::{
	Identifier, ItemRef, Name, Namespace, NamespaceASTElem, NamespaceItem,
};
use crate::ast::statement::Stmt;
use crate::ast::traits::{Impl, TraitDef, TraitRef};
use crate::ast::types::{
	AlgebraicDef, Basic, BindingProps, FnDef, FnParamList, TupleKind, Type, TypeDef, TypeParamList,
	TypeRef, Visibility,
};
use crate::ast::{Attribute, TokenData};

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
pub type AnalyzeResult<T> = Result<T, (CMNError, TokenData)>;

pub struct Parser {
	pub namespace: Namespace,
	pub lexer: RefCell<Lexer>,
	current_scope: Identifier,
	verbose: bool,
}

impl Parser {
	pub fn new(lexer: Lexer, verbose: bool) -> Parser {
		Parser {
			namespace: Namespace::new(Identifier::new(true)),
			current_scope: Identifier::new(true),
			lexer: RefCell::new(lexer),
			verbose,
		}
	}

	fn err(&self, code: CMNErrorCode) -> CMNError {
		CMNError::new_with_parser(code, self)
	}

	fn get_current(&self) -> ParseResult<Token> {
		match self.lexer.borrow().current() {
			Some((_, tk)) => Ok(tk.clone()),
			None => Err(self.err(CMNErrorCode::UnexpectedEOF)),
		}
	}

	fn get_next(&self) -> ParseResult<Token> {
		match self.lexer.borrow_mut().next() {
			Some((_, tk)) => Ok(tk.clone()),
			None => Err(self.err(CMNErrorCode::UnexpectedEOF)),
		}
	}

	// Consume the current token, returning an error if it doesn't match `expected`
	fn consume(&self, expected: &Token) -> ParseResult<()> {
		if &self.get_current()? == expected {
			self.get_next()?;
			Ok(())
		} else {
			Err(self.err(CMNErrorCode::UnexpectedToken))
		}
	}

	fn get_current_start_index(&self) -> usize {
		self.lexer.borrow().current().unwrap().0
	}

	fn get_current_token_index(&self) -> usize {
		self.lexer.borrow().current_token_index()
	}

	pub fn parse_module(&mut self) -> ParseResult<&Namespace> {
		self.lexer.borrow_mut().tokenize_file().unwrap();

		match self.parse_namespace(&Identifier::new(true)) {
			Ok(()) => {
				if self.verbose {
					println!("\ngenerated namespace info:\n\n{}", &self.namespace);
				}

				Ok(&self.namespace)
			}
			Err(e) => Err(e),
		}
	}

	pub fn generate_ast(&mut self) -> ParseResult<()> {
		for child in &self.namespace.children {
			match &child.1 .0 {
				NamespaceItem::Functions(fns) => {
					for (_, ast) in fns {
						let mut elem = ast.borrow_mut();

						if let NamespaceASTElem::Unparsed(idx) = *elem {
							// Parse function block
							self.lexer.borrow_mut().seek_token_idx(idx);
							*elem = NamespaceASTElem::Parsed(self.parse_block()?)
						}
					}
				}

				NamespaceItem::Type(_) | NamespaceItem::Alias(_) | NamespaceItem::Trait(_) => {}

				_ => todo!(),
			}
		}

		for (_, im) in self.namespace.trait_solver.get_local_impls() {
			// Generate impl function bodies
			let im = im.read().unwrap();

			for fns in im.items.values() {
				for (_, ast) in fns {
					let mut elem = ast.borrow_mut();

					if let NamespaceASTElem::Unparsed(idx) = *elem {
						// Parse method block
						self.lexer.borrow_mut().seek_token_idx(idx);
						*elem = NamespaceASTElem::Parsed(self.parse_block()?)
					}
				}
			}
		}

		Ok(())
	}

	pub fn parse_namespace(&mut self, scope: &Identifier) -> ParseResult<()> {
		let mut current = self.get_current()?;
		let mut current_attributes = vec![];

		while current != Token::Eof && current != Token::Other('}') {
			match current {
				Token::Other(';') => {
					self.get_next()?;
				}

				Token::Other('@') => {
					// Parse attributes
					while token_compare(&self.get_current()?, "@") {
						current_attributes.push(self.parse_attribute()?);
					}
				}

				Token::Keyword(keyword) => {
					match keyword {
						"enum" => {
							let mut aggregate = AlgebraicDef::new();
							let Token::Name(name) = self.get_next()? else { return Err(self.err(CMNErrorCode::ExpectedIdentifier)) };

							let mut next = self.get_next()?;

							if token_compare(&next, "<") {
								aggregate.params = self.parse_type_parameter_list()?;
								next = self.get_current()?;
							}

							if !token_compare(&next, "{") {
								return Err(self.err(CMNErrorCode::UnexpectedToken));
							}

							next = self.get_next()?; // Consume brace

							while !token_compare(&next, "}") {
								let Token::Name(variant_name) = next else { return Err(self.err(CMNErrorCode::UnexpectedToken)) };

								self.get_next()?;

								let tuple = self.parse_tuple_type(false)?;
								//aggregate.variants.push((variant_name, tuple));

								next = self.get_current()?;

								match next {
									Token::Other(',') => next = self.get_next()?,

									Token::Other('}') => break,

									_ => return Err(self.err(CMNErrorCode::UnexpectedToken)),
								}
							}

							self.get_next()?; // Consume closing brace

							let aggregate = TypeDef::Algebraic(aggregate);

							self.namespace.children.insert(
								Identifier::from_parent(scope, name),
								(
									NamespaceItem::Type(Arc::new(RwLock::new(aggregate))),
									current_attributes,
									None,
								),
							);

							current_attributes = vec![];
						}

						"struct" => {
							// Register algebraic type
							let mut current_visibility = Visibility::Public;
							let mut aggregate = AlgebraicDef::new();
							let Token::Name(name) = self.get_next()? else { return Err(self.err(CMNErrorCode::ExpectedIdentifier)) };

							let mut next = self.get_next()?;

							if token_compare(&next, "<") {
								aggregate.params = self.parse_type_parameter_list()?;
								next = self.get_current()?;
							}

							if !token_compare(&next, "{") {
								return Err(self.err(CMNErrorCode::UnexpectedToken));
							}

							next = self.get_next()?; // Consume brace

							while !token_compare(&next, "}") {
								match next {
									Token::Name(_) => {
										let result = self.parse_namespace_declaration()?;

										match result.1 {
											NamespaceItem::Variable(t, _) => aggregate
												.members
												.push((result.0, t, current_visibility.clone())),

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
											_ => {
												return Err(
													self.err(CMNErrorCode::UnexpectedKeyword)
												)
											}
										}
										self.get_next()?;
										next = self.get_next()?;
									}

									_ => return Err(self.err(CMNErrorCode::ExpectedIdentifier)),
								}
							}

							self.get_next()?; // Consume closing brace

							let aggregate = TypeDef::Algebraic(aggregate);

							self.namespace.children.insert(
								Identifier::from_parent(scope, name),
								(
									NamespaceItem::Type(Arc::new(RwLock::new(aggregate))),
									current_attributes,
									None,
								),
							);

							current_attributes = vec![];
						}

						"trait" => {
							let Token::Name(name) = self.get_next()? else {
								return Err(self.err(CMNErrorCode::UnexpectedToken));
							};

							let mut this_trait = TraitDef {
								items: HashMap::new(),
								types: HashMap::new(),
								supers: vec![],
							};

							let mut next = self.get_next()?;

							if !token_compare(&next, "{") {
								return Err(self.err(CMNErrorCode::UnexpectedToken));
							}

							next = self.get_next()?; // Consume brace

							while !token_compare(&next, "}") {
								let Token::Name(_) = next else {
									return Err(self.err(CMNErrorCode::UnexpectedToken))
								};

								let (name, item) = self.parse_namespace_declaration()?;

								match item {
									NamespaceItem::Functions(fns) => {
										for (func, ast) in fns {
											if !matches!(&*ast.borrow(), NamespaceASTElem::NoElem) {
												panic!("default trait method definitions are not yet supported")
											}

											if let Some(fns) = this_trait.items.get_mut(&name) {
												fns.push((func, ast));
											} else {
												this_trait
													.items
													.insert(name.clone(), vec![(func, ast)]);
											}
										}
									}

									_ => todo!(),
								}

								next = self.get_current()?;
							}

							self.get_next()?; // Consume closing brace

							self.namespace.children.insert(
								Identifier::from_parent(scope, name),
								(
									NamespaceItem::Trait(Arc::new(RwLock::new(this_trait))),
									current_attributes,
									None,
								),
							);
							current_attributes = vec![];
						}

						"namespace" => {
							let Token::Name(namespace_name) = self.get_next()? else {
								return Err(self.err(CMNErrorCode::ExpectedIdentifier));
							};

							self.get_next()?; // Consume name
							self.consume(&Token::Other('{'))?; // Consume brace

							self.current_scope.path.push(namespace_name);

							let scope = self.current_scope.clone();
							self.parse_namespace(&scope)?;
							self.current_scope.path.pop();

							current_attributes = vec![];
						}

						"impl" => {
							self.get_next()?;

							// Parse type or trait name, depending on if the next token is "for"
							let mut impl_ty = self.parse_type(false)?;
							let mut trait_name = None;

							if self.get_current()? == Token::Keyword("for") {
								self.get_next()?;

								// We parsed the trait as a type, so extract it
								let Type::TypeRef(ItemRef::Unresolved { name, scope, type_args }) = impl_ty else {
									return Err(self.err(CMNErrorCode::ExpectedIdentifier)); // TODO: Proper error
								};

								trait_name = Some(ItemRef::<TraitRef>::Unresolved {
									name,
									scope,
									type_args,
								});

								// Then parse the implementing type, for real this time
								impl_ty = self.parse_type(false)?;
							}

							// Consume barce
							self.consume(&Token::Other('{'))?;

							// Parse functions
							let mut functions = HashMap::new();

							while self.get_current()? != Token::Other('}') {
								let ret = self.parse_type(false)?;

								let Token::Name(fn_name) = self.get_current()? else {
									return Err(self.err(CMNErrorCode::ExpectedIdentifier));
								};

								self.get_next()?;

								let params = self.parse_parameter_list()?;

								let ast =
									NamespaceASTElem::Unparsed(self.get_current_token_index());

								self.skip_block()?;

								let current_impl = vec![(
									Arc::new(RwLock::new(FnDef {
										ret,
										params,
										type_params: vec![],
									})),
									RefCell::new(ast),
								)];

								functions.insert(fn_name, current_impl);
								current_attributes = vec![];
							}

							// Register impl to solver
							let im = Arc::new(RwLock::new(Impl {
								implements: trait_name.clone(),
								items: functions,
								types: HashMap::new(),
								scope: self.current_scope.clone(),

								canonical_root: Identifier {
									qualifier: (
										Some(Box::new(impl_ty.clone())),
										trait_name.map(Box::new),
									),
									path: vec![],
									absolute: true,
								},
							}));

							self.namespace.trait_solver.register_impl(impl_ty, im);

							self.consume(&Token::Other('}'))?;
						}

						"import" => {
							// Register import statement
							self.get_next()?;

							if self.is_at_identifier_token()? {
								self.namespace
									.referenced_modules
									.insert(self.parse_identifier()?);
								self.check_semicolon()?;
							} else {
								return Err(self.err(CMNErrorCode::ExpectedIdentifier));
							}
						}

						"using" => {
							self.get_next()?;

							let mut names = self.parse_multi_identifier()?;

							if names.len() == 1 {
								if self.get_current()? == Token::Operator("=") {
									// Found a '=' token, so fetch the name to alias
									self.get_next()?;

									let name = names[0].expect_scopeless()?.clone();
									let aliased = self.parse_identifier()?;

									self.namespace.children.insert(
										Identifier::from_parent(scope, name),
										(NamespaceItem::Alias(aliased), vec![], None),
									);

									self.check_semicolon()?;
								} else {
									// No '=' token, just bring the name into scope
									let name = names.remove(0);

									self.namespace.children.insert(
										Identifier::from_parent(
											scope,
											name.path.last().unwrap().clone(),
										),
										(NamespaceItem::Alias(name), vec![], None),
									);

									self.check_semicolon()?;
								}
							} else {
								for name in names {
									self.namespace.children.insert(
										Identifier::from_parent(scope, name.name().clone()),
										(NamespaceItem::Alias(name), vec![], None),
									);
								}
								self.check_semicolon()?;
							}
						}

						_ => {
							return Err(self.err(CMNErrorCode::UnexpectedToken));
						}
					}
				}

				_ => {
					// Parse declaration/definition
					let (name, mut result) = self.parse_namespace_declaration()?;

					let id = Identifier::from_parent(scope, name);

					match &mut result {
						NamespaceItem::Functions(fns) => {
							if let Some((NamespaceItem::Functions(existing), ..)) =
								self.namespace.children.get_mut(&id)
							{
								existing.append(fns);
							} else {
								self.namespace
									.children
									.insert(id, (result, current_attributes, None));
							}
						}

						_ => todo!(),
					};

					current_attributes = vec![];
				}
			}

			current = self.get_current()?;
		}

		if current == Token::Eof {
			if scope.path.is_empty() {
				Ok(())
			} else {
				Err(self.err(CMNErrorCode::UnexpectedEOF))
			}
		} else if current == Token::Other('}') {
			if !scope.path.is_empty() {
				self.get_next()?;
				Ok(())
			} else {
				Err(self.err(CMNErrorCode::UnexpectedToken))
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
			return Err(self.err(CMNErrorCode::UnexpectedToken));
		}
		let mut bracket_depth = 1;

		while bracket_depth > 0 {
			current = self.get_next()?;

			match current {
				Token::Other('{') => bracket_depth += 1,
				Token::Other('}') => bracket_depth -= 1,
				Token::Eof => break,
				_ => {}
			}
		}

		self.get_next()
	}

	fn parse_block(&self) -> ParseResult<Expr> {
		let begin = self.get_current_start_index();
		let mut current = self.get_current()?;

		if current != Token::Other('{') {
			return Err(self.err(CMNErrorCode::UnexpectedToken));
		}

		let mut items = vec![];
		let mut result = None;

		self.get_next()?;

		while self.get_current()? != Token::Other('}') {
			let stmt = self.parse_statement()?;

			current = self.get_current()?;

			if current == Token::Other('}') {
				if let Stmt::Expr(expr) = stmt {
					result = Some(Box::new(expr));
					break;
				} else {
					panic!() // TODO: Error handling
				}
			}

			// Certain control flow statements don't need a semicolon
			// when used as a block item, so we check for those here

			let mut semicolon_optional = false;

			if let Stmt::Expr(Expr::Atom(Atom::CtrlFlow(ctrl), _)) = &stmt {
				if matches!(
					&**ctrl,
					ControlFlow::For { .. }
						| ControlFlow::If { .. } | ControlFlow::While { .. }
						| ControlFlow::Match { .. }
				) {
					semicolon_optional = true;
				}
			}

			if !semicolon_optional {
				self.check_semicolon()?;
			}

			items.push(stmt);

			while self.get_current()? == Token::Other(';') {
				self.get_next()?;
			}
		}

		self.get_next()?; // consume closing bracket

		let end = self.get_current_start_index();

		Ok(Expr::Atom(
			Atom::Block { items, result },
			NodeData {
				tk: (begin, end - begin),
				ty: None,
			},
		))
	}

	fn check_semicolon(&self) -> ParseResult<()> {
		if token_compare(&self.get_current()?, ";") {
			self.get_next()?;
			Ok(())
		} else {
			Err(self.err(CMNErrorCode::UnexpectedToken))
		}
	}

	fn parse_namespace_declaration(&self) -> ParseResult<(Name, NamespaceItem)> {
		let t = self.parse_type(false)?;
		let item;

		let Token::Name(name) = self.get_current()? else {
			return Err(self.err(CMNErrorCode::ExpectedIdentifier))
		};

		if let Token::Operator(op) = self.get_next()? {
			match op {
				// Function declaration
				"<" | "(" => {
					let mut type_params = vec![];

					if op == "<" {
						type_params = self.parse_type_parameter_list()?;
					}

					let t = FnDef {
						ret: t,
						params: self.parse_parameter_list()?,
						type_params,
					};

					// Past the parameter list, check if we're at a function body or not

					let ast_elem;

					match self.get_current()? {
						Token::Other('{') => {
							ast_elem = NamespaceASTElem::Unparsed(self.get_current_token_index());
							self.skip_block()?;
						}

						Token::Other(';') => {
							ast_elem = NamespaceASTElem::NoElem;
							self.get_next()?;
						}

						_ => return Err(self.err(CMNErrorCode::UnexpectedToken)),
					}

					item = NamespaceItem::Functions(vec![(
						Arc::new(RwLock::new(t)),
						RefCell::new(ast_elem),
					)]);
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
					return Err(self.err(CMNErrorCode::UnexpectedToken));
				}
			}
		} else {
			item = NamespaceItem::Variable(t, RefCell::new(NamespaceASTElem::NoElem));
			self.check_semicolon()?;
		}

		Ok((name, item))
	}

	fn parse_binding_props(&self) -> ParseResult<Option<BindingProps>> {
		if !matches!(
			self.get_current()?,
			Token::Operator("&") | Token::Keyword("mut")
		) {
			return Ok(None);
		}

		let mut props = BindingProps::default();

		if self.get_current()? == Token::Operator("&") {
			props.is_ref = true;
			self.get_next()?;
		}

		// `unsafe` is only a binding property when it follows "&"
		if self.get_current()? == Token::Keyword("unsafe") && props.is_ref {
			props.is_unsafe = true;
			self.get_next()?;
		}

		if self.get_current()? == Token::Keyword("mut") {
			props.is_mut = true;
			self.get_next()?;
		}

		Ok(Some(props))
	}

	fn parse_statement(&self) -> ParseResult<Stmt> {
		let begin = self.get_current_start_index();

		let binding_props = self.parse_binding_props()?;

		if self.is_at_type_token(true)? {
			// This is a declaration

			let ty = self.parse_type(true)?;

			let Token::Name(name) = self.get_current()? else {
				return Err(self.err(CMNErrorCode::ExpectedIdentifier))
			};

			let mut expr = None;

			if token_compare(&self.get_next()?, "=") {
				self.get_next()?;
				expr = Some(self.parse_expression()?);
			}

			let stmt_result = Stmt::Decl(
				vec![(ty, name, binding_props.unwrap_or_default())],
				expr,
				(begin, self.get_current_start_index() - begin),
			);

			Ok(stmt_result)
		} else {
			// TODO: Error out if binding_props.is_ref or binding_props.is_mut is true
			// binding_props.is_unsafe is fine because that's allowed in front of a block

			// This isn't a declaration, so parse an expression

			let expr = self.parse_expression()?;

			Ok(Stmt::Expr(expr))
		}
	}

	fn parse_pattern(&self) -> ParseResult<Pattern> {
		if self.is_at_type_token(true)? {
			let pattern_ty = self.parse_type(true)?;

			let is_ref = self.get_current()? == Token::Operator("&");

			if is_ref {
				self.get_next()?;
			}

			match self.get_current()? {
				Token::Name(id) => {
					self.get_next()?;

					Ok(Pattern::Binding(Binding {
						name: Some(id),
						ty: pattern_ty,
						is_ref,
						is_mut: true,
					}))
				}

				Token::Other('{') => todo!(),

				_ => Err(self.err(CMNErrorCode::UnexpectedToken)),
			}
		} else {
			Err(self.err(CMNErrorCode::UnexpectedToken))
		}
	}

	fn parse_expression(&self) -> ParseResult<Expr> {
		self.parse_expression_bp(0)
	}

	// World's most hacked-together pratt parser (tm)
	fn parse_expression_bp(&self, min_bp: u8) -> ParseResult<Expr> {
		let mut current = self.get_current()?;
		let begin_lhs = self.get_current_start_index();

		// Get initial part of expression, could be an Atom or the operator of a unary Cons
		let mut lhs = if self.is_at_identifier_token()? {
			Expr::Atom(
				self.parse_atom()?,
				NodeData {
					ty: None,
					tk: (begin_lhs, self.get_current_start_index() - begin_lhs),
				},
			)
		} else {
			match current {
				// Parse atom
				Token::StringLiteral(_)
				| Token::CStringLiteral(_)
				| Token::NumLiteral(_, _)
				| Token::BoolLiteral(_)
				| Token::Keyword(_) => Expr::Atom(
					self.parse_atom()?,
					NodeData {
						ty: None,
						tk: (begin_lhs, self.get_current_start_index() - begin_lhs),
					},
				),

				// Handle unary prefix operators
				Token::Operator(tk) => {
					let Some(op) = Operator::get_operator(tk, false) else {
							return Err(self.err(CMNErrorCode::UnexpectedToken))
						};

					self.get_next()?;

					if let Operator::Call = op {
						// Special case; parse sub-expression
						let sub = self.parse_expression_bp(0)?;

						current = self.get_current()?;

						if let Token::Operator(op) = current {
							if op != ")" {
								return Err(self.err(CMNErrorCode::UnexpectedToken));
							}
							self.get_next()?;
							sub
						} else {
							return Err(self.err(CMNErrorCode::UnexpectedToken));
						}
					} else {
						let rhs = self.parse_expression_bp(op.get_binding_power())?;

						let end_index = self.get_current_start_index();

						let tk = (begin_lhs, end_index - begin_lhs);
						Expr::Unary(Box::new(rhs), op, NodeData { ty: None, tk })
					}
				}

				_ => {
					return Err(self.err(CMNErrorCode::UnexpectedToken));
				}
			}
		};

		// Parse RHS
		loop {
			let tk = self.get_current()?;

			let op = match tk {
				Token::Operator(op) => match Operator::get_operator(op, true) {
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

			match op {
				Operator::Cast => {
					let goal_t = self.parse_type(true)?;

					let end_index = self.get_current_start_index();
					let meta = (begin_lhs, end_index - begin_lhs);

					lhs = Expr::create_cast(lhs, goal_t, NodeData { ty: None, tk: meta });
				}

				Operator::PostInc | Operator::PostDec => {
					let meta = (begin_lhs, self.get_current_start_index() - begin_lhs);

					// Create compound assignment expression
					lhs = Expr::Cons(
						[
							Box::new(lhs),
							Box::new(Expr::Atom(
								Atom::IntegerLit(1, None),
								NodeData {
									ty: None,
									tk: (0, 0),
								},
							)),
						],
						match op {
							Operator::PostInc => Operator::AssAdd,
							Operator::PostDec => Operator::AssSub,
							_ => panic!(),
						},
						NodeData { ty: None, tk: meta },
					);
				}

				Operator::Subscr => {
					let rhs = self.parse_expression_bp(rbp)?;
					let end_rhs = self.get_current_start_index();

					lhs = Expr::Cons(
						[Box::new(lhs), Box::new(rhs)],
						op,
						NodeData {
							ty: None,
							tk: (begin_rhs, end_rhs - begin_rhs),
						},
					);

					if self.get_current()? == Token::Operator("]") {
						self.get_next()?;
					} else {
						return Err(self.err(CMNErrorCode::UnexpectedToken));
					}
				}

				_ => {
					let rhs = self.parse_expression_bp(rbp)?;
					let end_rhs = self.get_current_start_index();

					lhs = Expr::Cons(
						[Box::new(lhs), Box::new(rhs)],
						op,
						NodeData {
							ty: None,
							tk: (begin_rhs, end_rhs - begin_rhs),
						},
					);
				}
			}
		}

		Ok(lhs)
	}

	fn parse_atom(&self) -> ParseResult<Atom> {
		let mut result = None;
		let mut current = self.get_current()?;

		if self.is_at_identifier_token()? {
			let id = self.parse_identifier()?;

			if let Some(Type::TypeRef(ItemRef::Resolved(mut found))) = self.find_type(&id) {
				match &*found.def.upgrade().unwrap().read().unwrap() {
					// Parse with algebraic typename
					TypeDef::Algebraic(_) => {
						if let Token::Operator("<") = self.get_current()? {
							found.args = self.parse_type_argument_list()?;
						}

						if let Token::Other('{') = self.get_current()? {
							// Parse struct literal

							let mut inits = vec![];

							while self.get_current()? != Token::Other('}') {
								self.get_next()?;

								if let Token::Name(member_name) = self.get_current()? {
									self.get_next()?;

									self.consume(&Token::Other(':'))?;

									let expr = self.parse_expression()?;

									inits.push((Some(member_name), expr));
								} else if self.get_current()? != Token::Other('}') {
									return Err(self.err(CMNErrorCode::UnexpectedToken));
								}
							}

							self.consume(&Token::Other('}'))?;

							result = Some(Atom::AlgebraicLit(
								Type::TypeRef(ItemRef::Resolved(found)),
								inits,
							));
						} else {
							return Err(self.err(CMNErrorCode::UnexpectedToken));
						}
					}

					TypeDef::Class => todo!(),
				}
			}

			if result.is_none() {
				// Variable or function name
				result = Some(Atom::Identifier(id.clone()));

				if let Token::Operator("(" | "<") = self.get_current()? {
					let mut type_args = vec![];

					if self.get_current()? == Token::Operator("<") {
						let mut is_function = false;

						self.namespace
							.with_item(&id, &self.current_scope, |item, _| {
								is_function = matches!(&item.0, NamespaceItem::Functions(..));
							});

						if is_function {
							type_args = self.parse_type_argument_list()?
						} else {
							// Not a function, return as plain Identifier early
							return Ok(result.unwrap());
						}
					}

					// Function call
					let mut args = vec![];

					if self.get_next()? != Token::Operator(")") {
						loop {
							args.push(self.parse_expression()?);

							current = self.get_current()?;

							if let Token::Other(',') = current {
								self.get_next()?;
							} else if current == Token::Operator(")") {
								break;
							} else {
								return Err(self.err(CMNErrorCode::UnexpectedToken));
							}
						}
					}
					self.get_next()?;

					result = Some(Atom::FnCall {
						name: id,
						args,
						type_args,
						resolved: FnRef::None,
					});
				}
			}
		} else {
			let next = self.get_next()?;

			match current {
				Token::StringLiteral(s) => result = Some(Atom::StringLit(s)),

				Token::CStringLiteral(s) => result = Some(Atom::CStringLit(s)),

				Token::NumLiteral(s, suffix) => {
					let mut suffix_b = Basic::get_basic_type(suffix.as_str());

					if suffix_b.is_none() && !suffix.is_empty() {
						suffix_b = match suffix.as_str() {
							// Add special numeric suffixes here
							"f" => Some(Basic::Float { size_bytes: 4 }),

							_ => return Err(self.err(CMNErrorCode::InvalidSuffix)),
						};
					}

					let atom = if s.find('.').is_some() {
						Atom::FloatLit(s.parse::<f64>().unwrap(), suffix_b)
					} else {
						Atom::IntegerLit(s.parse::<i128>().unwrap(), suffix_b)
					};

					result = Some(atom);
				}

				Token::BoolLiteral(b) => result = Some(Atom::BoolLit(b)),

				Token::Keyword(keyword) => match keyword {
					// Parse return statement
					"return" => {
						if next == Token::Other(';') || next == Token::Other('}') {
							result =
								Some(Atom::CtrlFlow(Box::new(ControlFlow::Return { expr: None })));
						} else {
							result = Some(Atom::CtrlFlow(Box::new(ControlFlow::Return {
								expr: Some(self.parse_expression()?),
							})));
						}
					}

					"break" => {
						// TODO: Labeled break and continue

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::Break)));
					}

					"continue" => {
						// TODO: Labeled break and continue

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::Continue)));
					}

					"match" => {
						let scrutinee = self.parse_expression()?;
						current = self.get_current()?;

						if current != Token::Other('{') {
							return Err(self.err(CMNErrorCode::UnexpectedToken));
						}

						current = self.get_next()?;

						let mut branches = vec![];

						while current != Token::Other('}') {
							let branch_pat = self.parse_pattern()?;
							let branch_block;

							if self.get_current()? != Token::Operator("=>") {
								return Err(self.err(CMNErrorCode::UnexpectedToken));
							}

							if self.get_next()? == Token::Other('{') {
								branch_block = self.parse_block()?;
							} else {
								branch_block = self.parse_expression()?;

								// After a bare expression, a comma is required
								if self.get_current()? != Token::Other(',') {
									return Err(self.err(CMNErrorCode::UnexpectedToken));
								}

								self.get_next()?;
							}

							while self.get_current()? == Token::Other(',') {
								self.get_next()?;
							}

							current = self.get_current()?;
							branches.push((branch_pat, branch_block));
						}

						self.get_next()?;

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::Match {
							scrutinee,
							branches,
						})));
					}

					// Parse if statement
					"if" => {
						// Parse condition
						let cond = self.parse_expression()?;

						// Parse body
						let body;
						let mut else_body = None;

						if token_compare(&self.get_current()?, "{") {
							body = self.parse_block()?;
						} else {
							return Err(self.err(CMNErrorCode::UnexpectedToken));
						}

						if token_compare(&self.get_current()?, "else") {
							self.get_next()?;

							if token_compare(&self.get_current()?, "{") {
								else_body = Some(self.parse_block()?);
							} else {
								return Err(self.err(CMNErrorCode::UnexpectedToken));
							}
						}

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::If {
							cond,
							body,

							// TODO: Add proper metadata to this
							else_body,
						})));
					}

					// Parse while loop
					"while" => {
						let cond = self.parse_expression()?;
						let body = self.parse_block()?;

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::While { cond, body })));
					}

					// Parse for loop
					"for" => {
						// Check opening brace
						if token_compare(&next, "(") {
							current = self.get_next()?;
						} else {
							return Err(self.err(CMNErrorCode::UnexpectedToken));
						}

						let mut init = None;
						let mut cond = None;
						let mut iter = None;

						if token_compare(&current, ";") {
							// No init statement, skip
							current = self.get_next()?;
						} else {
							init = Some(self.parse_statement()?); // TODO: Restrict to declaration?
							self.check_semicolon()?;
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
							return Err(self.err(CMNErrorCode::UnexpectedToken));
						}

						// Parse body
						let body = if token_compare(&current, "{") {
							self.parse_block()?
						} else {
							self.parse_statement()?.wrap_in_block()
						};

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::For {
							init,
							cond,
							iter,
							body,
						})));
					}

					// Invalid keyword at start of statement
					_ => return Err(self.err(CMNErrorCode::UnexpectedKeyword)),
				},

				_ => return Err(self.err(CMNErrorCode::UnexpectedToken)),
			};
		}

		Ok(result.unwrap())
	}

	fn find_type(&self, typename: &Identifier) -> Option<Type> {
		self.namespace
			.resolve_type(typename, &self.current_scope, &vec![])
	}

	// Returns true if the current token is the start of a Type.
	// In ambiguous contexts (i.e. function blocks), `resolve_idents` enables basic name resolution
	fn is_at_type_token(&self, resolve_idents: bool) -> ParseResult<bool> {
		let current = self.get_current()?;

		let current_idx = self.get_current_token_index();

		if current == Token::Operator("(") {
			// This might be the start of a tuple OR expression, so we gotta peek ahead whoops
			self.get_next()?;
		}

		if self.is_at_identifier_token()? {
			if resolve_idents {
				let typename = self.parse_identifier()?;

				self.lexer.borrow_mut().seek_token_idx(current_idx);

				Ok(self
					.namespace
					.resolve_type(&typename, &self.current_scope, &vec![])
					.is_some())
			} else {
				self.lexer.borrow_mut().seek_token_idx(current_idx);

				Ok(true)
			}
		} else {
			Ok(false)
		}
	}

	fn is_at_identifier_token(&self) -> ParseResult<bool> {
		Ok(matches!(
			self.get_current()?,
			Token::Name(_) | Token::Operator("::" | "<")
		))
	}

	fn parse_identifier(&self) -> ParseResult<Identifier> {
		if !self.is_at_identifier_token()? {
			return Err(self.err(CMNErrorCode::ExpectedIdentifier));
		}

		let absolute;
		let qualifier;

		if self.get_current()? == Token::Operator("::") {
			self.get_next()?;

			absolute = true;
			qualifier = (None, None);
		} else if self.get_current()? == Token::Operator("<") {
			self.get_next()?;

			let ty = self.parse_type(true)?;

			let tr = match self.get_current()? {
				Token::Operator("as") => {
					self.get_next()?;
					Some(Box::new(ItemRef::Unresolved {
						name: self.parse_identifier()?,
						scope: self.current_scope.clone(),
						type_args: vec![],
					}))
				}

				Token::Operator(">") => None,

				_ => return Err(self.err(CMNErrorCode::UnexpectedToken)),
			};

			self.consume(&Token::Operator(">"))?;

			absolute = true;
			qualifier = (Some(Box::new(ty)), tr);
		} else {
			absolute = false;
			qualifier = (None, None);
		}

		let mut path = vec![];

		loop {
			let Token::Name(name) = self.get_current()? else {
				return Err(self.err(CMNErrorCode::UnexpectedToken));
			};

			path.push(name);

			if self.get_next()? == Token::Operator("::") {
				self.get_next()?;
			} else {
				break;
			}
		}

		Ok(Identifier {
			qualifier,
			path,
			absolute,
		})
	}

	fn parse_multi_identifier(&self) -> ParseResult<Vec<Identifier>> {
		if !self.is_at_identifier_token()? {
			return Err(self.err(CMNErrorCode::ExpectedIdentifier));
		}

		let absolute = if self.get_current()? == Token::Operator("::") {
			self.get_next()?;
			true
		} else {
			false
		};

		self.parse_multi_identifier_component(absolute)
	}

	fn parse_multi_identifier_component(&self, absolute: bool) -> ParseResult<Vec<Identifier>> {
		let mut result = vec![];

		let mut current = Identifier {
			qualifier: (None, None),
			absolute,
			path: vec![],
		};

		loop {
			match self.get_current()? {
				Token::Name(name) => {
					self.get_next()?;
					current.path.push(name)
				}

				Token::Other('{') => {
					self.get_next()?;
					let mut paths = vec![];

					while self.get_current()? != Token::Other('}') {
						let mut sub_paths = self.parse_multi_identifier_component(absolute)?;

						for sub_path in &mut sub_paths {
							let mut sub_path_prefix = current.path.clone();

							sub_path_prefix.append(&mut sub_path.path);

							sub_path.path = sub_path_prefix
						}

						paths.append(&mut sub_paths);

						if self.get_current()? == Token::Other(',') {
							self.get_next()?;
						}
					}

					self.consume(&Token::Other('}'))?;
				}

				_ => return Err(self.err(CMNErrorCode::UnexpectedToken)),
			}

			if self.get_current()? == Token::Operator("::") {
				self.get_next()?;
			} else {
				break;
			}
		}

		if result.is_empty() {
			result.push(current);
		}

		Ok(result)
	}

	fn parse_parameter_list(&self) -> ParseResult<FnParamList> {
		let mut result = FnParamList {
			params: vec![],
			variadic: false,
		};

		if token_compare(&self.get_current()?, "(") {
			self.get_next()?;
		} else {
			return Err(self.err(CMNErrorCode::UnexpectedToken));
		}

		loop {
			let props = self.parse_binding_props()?;

			if !self.is_at_type_token(false)? {
				break;
			}

			let mut param = (self.parse_type(false)?, None, props.unwrap_or_default());

			// Check for param name
			let mut current = self.get_current()?;

			if let Token::Name(name) = current {
				param.1 = Some(name);
				self.get_next()?;
			}

			result.params.push(param);

			// Check if we've arrived at a comma, skip it, and loop back around
			current = self.get_current()?;

			match current {
				Token::Other(',') => {
					self.get_next()?;
					continue;
				}

				Token::Operator(")") => break,

				_ => {
					return Err(self.err(CMNErrorCode::UnexpectedToken));
				}
			}
		}

		match self.get_current()? {
			Token::Operator(")") => {
				self.get_next()?;
				Ok(result)
			}

			Token::Operator("...") => {
				if self.get_next()? == Token::Operator(")") {
					self.get_next()?;
					result.variadic = true;
					Ok(result)
				} else {
					Err(self.err(CMNErrorCode::UnexpectedToken))
				}
			}

			_ => Err(self.err(CMNErrorCode::UnexpectedToken)),
		}
	}

	fn parse_type(&self, immediate_resolve: bool) -> ParseResult<Type> {
		let mut result;

		if !self.is_at_type_token(immediate_resolve)? {
			return Err(self.err(CMNErrorCode::ExpectedIdentifier));
		}

		if self.get_current()? == Token::Operator("(") {
			let (kind, types) = self.parse_tuple_type(immediate_resolve)?;

			Ok(Type::Tuple(kind, types))
		} else if self.is_at_identifier_token()? {
			let typename = self.parse_identifier()?;

			if immediate_resolve {
				if let Some(ty) =
					self.namespace
						.resolve_type(&typename, &self.current_scope, &vec![])
				{
					result = ty;
				} else {
					return Err(self.err(CMNErrorCode::UnresolvedTypename(typename.to_string())));
				}
			} else {
				result = Type::TypeRef(ItemRef::Unresolved {
					name: typename,
					scope: self.current_scope.clone(),
					type_args: vec![],
				});
			}

			let mut next = self.get_current()?;

			match next {
				Token::Operator("*") => {
					// Pointer type

					while token_compare(&next, "*") {
						result = Type::Pointer(Box::new(result));
						next = self.get_next()?;
					}
				}

				Token::Operator("[") => {
					// Array type

					self.get_next()?;

					let const_expr = self.parse_expression()?;

					self.consume(&Token::Operator("]"))?;

					result = Type::Array(
						Box::new(result),
						Arc::new(RwLock::new(vec![ConstExpr::Expr(const_expr)])),
					);
				}

				Token::Operator("(") => {
					// Function type

					self.get_next()?;

					let ret = Box::new(result);
					let mut args = vec![];

					while self.get_current()? != Token::Operator(")") {
						args.push(self.parse_type(immediate_resolve)?);

						match self.get_current()? {
							Token::Other(',') => self.get_next()?,

							Token::Operator(")") => break,

							_ => return Err(self.err(CMNErrorCode::UnexpectedToken)),
						};
					}

					self.get_next()?;

					result = Type::Function(ret, vec![]);
				}

				Token::Operator("<") => {
					// Type parameters

					if let Type::TypeRef(
						ItemRef::Resolved(TypeRef { args, .. })
						| ItemRef::Unresolved {
							type_args: args, ..
						},
					) = &mut result
					{
						*args = self.parse_type_argument_list()?;
					} else {
						panic!("can't apply type parameters to this type of Type!") // TODO: Real error handling
					}
				}

				_ => {}
			}

			Ok(result)
		} else {
			Err(self.err(CMNErrorCode::UnexpectedToken))
		}
	}

	fn parse_attribute(&self) -> ParseResult<Attribute> {
		if !token_compare(&self.get_current()?, "@") {
			return Err(self.err(CMNErrorCode::UnexpectedToken)); // You called this from the wrong place lol
		}

		let name = self.get_next()?;
		let mut result;

		if let Token::Name(name) = name {
			result = Attribute {
				name: name.to_string(),
				args: vec![],
			};
		} else {
			return Err(self.err(CMNErrorCode::ExpectedIdentifier));
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

	fn parse_type_parameter_list(&self) -> ParseResult<TypeParamList> {
		if !token_compare(&self.get_current()?, "<") {
			return Err(self.err(CMNErrorCode::UnexpectedToken));
		}

		let mut result = vec![];
		let mut current = self.get_next()?;

		loop {
			match current {
				Token::Name(name) => {
					let mut traits = vec![];

					current = self.get_next()?;

					if let Token::Other(':') = current {
						current = self.get_next()?;

						// Collect trait bounds
						while self.is_at_identifier_token()? {
							let tr = self.parse_identifier()?;

							traits.push(ItemRef::Unresolved {
								name: tr,
								scope: self.current_scope.clone(),
								type_args: vec![],
							});

							current = self.get_next()?;

							match current {
								Token::Operator("+") => current = self.get_next()?,

								Token::Other(',') => break,

								_ => return Err(self.err(CMNErrorCode::UnexpectedToken)),
							}
						}
					}

					result.push((name, traits, None));

					match &current {
						Token::Operator(">") => continue,
						Token::Other(',') => {
							current = self.get_next()?;
							continue;
						}

						_ => return Err(self.err(CMNErrorCode::UnexpectedToken)),
					}
				}

				Token::Operator(">") => break,

				_ => {
					return Err(self.err(CMNErrorCode::UnexpectedToken));
				}
			}
		}

		self.get_next()?;

		Ok(result)
	}

	fn parse_type_argument_list(&self) -> ParseResult<Vec<Type>> {
		self.get_next()?;

		let mut result = vec![];

		loop {
			let generic = self.parse_type(true)?;
			result.push(generic);

			if self.get_current()? == Token::Other(',') {
				self.get_next()?;
			} else {
				break;
			}
		}

		if self.get_current()? != Token::Operator(">") {
			return Err(self.err(CMNErrorCode::UnexpectedToken));
		}

		// consume closing angle bracket
		self.get_next()?;

		Ok(result)
	}

	fn parse_tuple_type(&self, immediate_resolve: bool) -> ParseResult<(TupleKind, Vec<Type>)> {
		let mut types = vec![];

		if self.get_current()? != Token::Operator("(") {
			return Err(self.err(CMNErrorCode::UnexpectedToken));
		}

		self.get_next()?;

		let mut kind = None;

		loop {
			types.push(self.parse_type(immediate_resolve)?);

			match self.get_current()? {
				Token::Other(',') => {
					// Check if tuple kind is consistent
					if matches!(kind, Some(TupleKind::Sum)) {
						return Err(self.err(CMNErrorCode::UnexpectedToken));
					}

					kind = Some(TupleKind::Product);
				}

				Token::Operator("|") => {
					// Ditto
					if matches!(kind, Some(TupleKind::Product)) {
						return Err(self.err(CMNErrorCode::UnexpectedToken));
					}

					kind = Some(TupleKind::Sum);
				}

				Token::Operator(")") => break,

				_ => {
					return Err(self.err(CMNErrorCode::UnexpectedToken));
				}
			}

			self.get_next()?;
		}

		self.get_next()?;

		match kind {
			Some(kind) => Ok((kind, types)),

			None => Ok((TupleKind::Product, types)),
		}
	}
}
