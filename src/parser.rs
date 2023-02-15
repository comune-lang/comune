use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

use crate::ast::pattern::{Binding, Pattern};
use crate::constexpr::ConstExpr;
use crate::errors::{ComuneError, ComuneErrCode};
use crate::lexer::{Lexer, SrcSpan, Token};

use crate::ast::controlflow::ControlFlow;
use crate::ast::expression::{Atom, Expr, FnRef, NodeData, Operator};
use crate::ast::module::{
	Identifier, ItemRef, Name, ModuleImpl, ModuleASTElem, ModuleItemImpl, ModuleImportKind, ModuleItemInterface, ModuleInterface, ModuleItemOpaque,
};
use crate::ast::statement::Stmt;
use crate::ast::traits::{ImplBlockInterface, TraitInterface, TraitRef};
use crate::ast::types::{
	AlgebraicDef, Basic, BindingProps, FnPrototype, FnParamList, TupleKind, Type, TypeDef, TypeParamList,
	TypeRef, Visibility,
};
use crate::ast::Attribute;

// Convenience function that matches a &str against various token kinds
fn token_compare(token: &Token, text: &str) -> bool {
	match token {
		Token::Operator(op) => text == *op,
		Token::Other(c) => text.chars().next().unwrap() == *c,
		Token::Keyword(keyword) => text == *keyword,
		_ => false,
	}
}

pub type ComuneResult<T> = Result<T, ComuneError>;

pub struct Parser {
	pub interface: Arc<ModuleInterface>,
	pub module_impl: ModuleImpl,
	pub lexer: RefCell<Lexer>,
	pub imports_opaque: HashMap<Name, HashMap<Identifier, ModuleItemOpaque>>,
	current_scope: Identifier,
	verbose: bool,
}

impl Parser {
	pub fn new(lexer: Lexer, verbose: bool) -> Parser {
		Parser {
			interface: Arc::new(ModuleInterface::new(Identifier::new(true))),
			module_impl: ModuleImpl::new(),
			current_scope: Identifier::new(true),
			lexer: RefCell::new(lexer),
			imports_opaque: HashMap::new(),
			verbose,
		}
	}

	fn err<T>(&self, code: ComuneErrCode) -> ComuneResult<T> {
		Err(ComuneError::new(code, SrcSpan::new()))
	}

	fn get_current(&self) -> ComuneResult<Token> {
		match self.lexer.borrow().current() {
			Some((_, tk)) => Ok(tk.clone()),
			None => self.err(ComuneErrCode::UnexpectedEOF),
		}
	}

	fn get_next(&self) -> ComuneResult<Token> {
		match self.lexer.borrow_mut().next() {
			Some((_, tk)) => Ok(tk.clone()),
			None => self.err(ComuneErrCode::UnexpectedEOF),
		}
	}

	// Consume the current token, returning an error if it doesn't match `expected`
	fn consume(&self, expected: &Token) -> ComuneResult<()> {
		if &self.get_current()? == expected {
			self.get_next()?;
			Ok(())
		} else {
			self.err(ComuneErrCode::UnexpectedToken)
		}
	}

	fn get_current_start_index(&self) -> usize {
		self.lexer.borrow().current().unwrap().0.start
	}

	fn get_prev_end_index(&self) -> usize {
		let prev = self.lexer.borrow().previous().unwrap().0;
		prev.start + prev.len
	}

	fn get_current_token_index(&self) -> usize {
		self.lexer.borrow().current_token_index()
	}

	pub fn parse_interface(&mut self) -> ComuneResult<&ModuleInterface> {
		self.lexer.borrow_mut().tokenize_file().unwrap();

		match self.parse_namespace(&Identifier::new(true)) {
			Ok(()) => {
				if self.verbose {
					todo!()
					//println!("\ngenerated namespace info:\n\n{}", &self.interface);
				}

				Ok(&self.interface)
			}
			Err(e) => Err(e),
		}
	}

	pub fn generate_ast(&mut self) -> ComuneResult<()> {
		let mut children_bodies = HashMap::new();

		for (name, child) in &self.module_impl.children {
			match child {
				ModuleItemImpl::Functions(fns) => {
					let mut fn_bodies = vec![];

					for elem in fns {
						// Parse function block
						if let ModuleASTElem::Unparsed(idx) = elem {
							self.lexer.borrow_mut().seek_token_idx(*idx);

							fn_bodies.push(ModuleASTElem::Parsed(self.parse_block()?));
						}
					}

					children_bodies.insert(name.clone(), ModuleItemImpl::Functions(fn_bodies));
				}

				_ => todo!(),
			}
		}

		for (name, body) in children_bodies {
			self.module_impl.children.insert(name, body);
		}

		let mut impl_bodies = HashMap::new();

		for (im_ty, im_name, im) in &self.module_impl.impl_bodies {
			let mut im_body = HashMap::new();

			// Generate impl function bodies
			for (fn_name, fns) in im {
				let mut fn_bodies = vec![];

				for ast in fns {
					if let ModuleASTElem::Unparsed(idx) = *ast {
						// Parse method block
						self.lexer.borrow_mut().seek_token_idx(idx);
						fn_bodies.push(ModuleASTElem::Parsed(self.parse_block()?));
					}
				}

				im_body.insert(fn_name.clone(), fn_bodies);
			}

			impl_bodies.insert((im_ty.clone(), im_name.clone()), im_body);
		}

		for ((ty, name), body) in impl_bodies {
			self.module_impl.impl_bodies.push((ty, name, body));
		}

		Ok(())
	}

	pub fn parse_namespace(&mut self, scope: &Identifier) -> ComuneResult<()> {
		while !matches!(self.get_current()?, Token::Eof | Token::Other('}')) {
			let mut current_attributes = self.parse_attributes()?;

			match self.get_current()? {
				Token::Other(';') => {
					self.get_next()?;
				}

				Token::Keyword("enum") => {
					let mut aggregate = AlgebraicDef::new();
					let Token::Name(name) = self.get_next()? else { return self.err(ComuneErrCode::ExpectedIdentifier) };

					let mut next = self.get_next()?;

					if token_compare(&next, "<") {
						aggregate.params = self.parse_type_parameter_list()?;
						next = self.get_current()?;
					}

					if !token_compare(&next, "{") {
						return self.err(ComuneErrCode::UnexpectedToken);
					}

					next = self.get_next()?; // Consume brace

					// TODO: Actually finish this

					while !token_compare(&next, "}") {
						let Token::Name(_variant_name) = next else { return self.err(ComuneErrCode::UnexpectedToken) };

						self.get_next()?;

						let _tuple = self.parse_tuple_type(false)?;
						//aggregate.variants.push((variant_name, tuple));

						next = self.get_current()?;

						match next {
							Token::Other(',') => next = self.get_next()?,

							Token::Other('}') => break,

							_ => return self.err(ComuneErrCode::UnexpectedToken),
						}
					}

					self.get_next()?; // Consume closing brace

					aggregate.attributes = current_attributes;

					Arc::get_mut(&mut self.interface).unwrap().children.insert(
						Identifier::from_parent(scope, name),
						ModuleItemInterface::Type(Arc::new(RwLock::new(TypeDef::Algebraic(aggregate)))),
					);
				}

				Token::Keyword("struct") => {
					// Register algebraic type
					let mut current_visibility = Visibility::Public;
					let mut aggregate = AlgebraicDef::new();
					let Token::Name(name) = self.get_next()? else { return self.err(ComuneErrCode::ExpectedIdentifier) };

					let mut next = self.get_next()?;

					if token_compare(&next, "<") {
						aggregate.params = self.parse_type_parameter_list()?;
						next = self.get_current()?;
					}

					if !token_compare(&next, "{") {
						return self.err(ComuneErrCode::UnexpectedToken);
					}

					next = self.get_next()?; // Consume brace

					while !token_compare(&next, "}") {
						match next {
							Token::Name(_) => {
								let result =
									self.parse_namespace_declaration(current_attributes)?;
								current_attributes = vec![];

								match result.1 {
									ModuleItemInterface::Variable(t) => aggregate.members.push((
										result.0,
										t,
										current_visibility.clone(),
									)),

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
									_ => return self.err(ComuneErrCode::UnexpectedKeyword),
								}
								self.get_next()?;
								next = self.get_next()?;
							}

							_ => return self.err(ComuneErrCode::ExpectedIdentifier),
						}
					}

					self.get_next()?; // Consume closing brace

					aggregate.attributes = current_attributes;

					Arc::get_mut(&mut self.interface).unwrap().children.insert(
						Identifier::from_parent(scope, name),
						ModuleItemInterface::Type(Arc::new(RwLock::new(TypeDef::Algebraic(aggregate)))),
					);
				}

				Token::Keyword("trait") => {
					let Token::Name(name) = self.get_next()? else {
						return self.err(ComuneErrCode::UnexpectedToken);
					};

					let mut this_trait = TraitInterface {
						items: HashMap::new(),
						types: HashMap::new(),
						supers: vec![],
						attributes: current_attributes,
					};

					let mut next = self.get_next()?;

					if !token_compare(&next, "{") {
						return self.err(ComuneErrCode::UnexpectedToken);
					}

					next = self.get_next()?; // Consume brace

					while !token_compare(&next, "}") {
						let func_attributes = self.parse_attributes()?;
						let (name, interface, im) = self.parse_namespace_declaration(func_attributes)?;

						match (interface, im) {
							(ModuleItemInterface::Functions(mut funcs), ModuleItemImpl::Functions(mut parsed)) => {
								if let Some(fns) = this_trait.items.get_mut(&name) {
									fns.append(&mut funcs);
								} else {
									this_trait.items.insert(name.clone(), funcs);
								}

								if !parsed.is_empty() {
									panic!("default impls in trait definitions are not yet supported");
								}
							}

							_ => todo!(),
						}

						next = self.get_current()?;
					}

					self.get_next()?; // Consume closing brace

					Arc::get_mut(&mut self.interface).unwrap().children.insert(
						Identifier::from_parent(scope, name),
						ModuleItemInterface::Trait(Arc::new(RwLock::new(this_trait))),
					);
				}

				Token::Keyword("impl") => {
					self.get_next()?;

					// Parse type or trait name, depending on if the next token is "for"
					let mut impl_ty = self.parse_type(false)?;
					let mut trait_name = None;

					if self.get_current()? == Token::Keyword("for") {
						self.get_next()?;

						// We parsed the trait as a type, so extract it
						let Type::TypeRef(ItemRef::Unresolved { name, scope, type_args }) = impl_ty else {
							return self.err(ComuneErrCode::ExpectedIdentifier); // TODO: Proper error
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
					let mut asts = HashMap::new();

					while self.get_current()? != Token::Other('}') {
						let func_attributes = self.parse_attributes()?;

						let ret = self.parse_type(false)?;

						let Token::Name(fn_name) = self.get_current()? else {
							return self.err(ComuneErrCode::ExpectedIdentifier);
						};

						self.get_next()?;

						let params = self.parse_parameter_list()?;
						let ast = ModuleASTElem::Unparsed(self.get_current_token_index());

						self.skip_block()?;

						// TODO: Proper overload handling here
						functions.insert(fn_name.clone(), vec![Arc::new(RwLock::new(FnPrototype {
							ret,
							params,
							type_params: vec![],
							attributes: func_attributes,
						}))]);

						asts.insert(fn_name, ast);
					}

					// Register impl to solver
					Arc::get_mut(&mut self.interface).unwrap().trait_solver.register_impl(impl_ty.clone(), ImplBlockInterface {
						implements: trait_name.clone(),
						functions,
						types: HashMap::new(),
						scope: self.current_scope.clone(),

						canonical_root: Identifier {
							qualifier: (Some(Box::new(impl_ty.clone())), trait_name.map(Box::new)),
							path: vec![],
							absolute: true,
						},
					});

					self.consume(&Token::Other('}'))?;
				}

				Token::Keyword("import") => {
					// Register import statement
					self.get_next()?;

					if self.is_at_identifier_token()? {
						let import = ModuleImportKind::Extern(self.parse_identifier()?);

						Arc::get_mut(&mut self.interface).unwrap()
							.import_names
							.insert(import);

						self.check_semicolon()?;
					} else {
						return self.err(ComuneErrCode::ExpectedIdentifier);
					}
				}

				Token::Keyword("using") => {
					self.get_next()?;

					let mut names = self.parse_multi_identifier()?;

					if names.len() == 1 {
						if self.get_current()? == Token::Operator("=") {
							// Found a '=' token, so fetch the name to alias
							self.get_next()?;

							let name = names[0].expect_scopeless()?.clone();

							if self.is_at_type_token(false)? {
								let ty = self.parse_type(false)?;

								Arc::get_mut(&mut self.interface).unwrap()
									.children
									.insert(
										Identifier::from_parent(scope, name),
										ModuleItemInterface::TypeAlias(Arc::new(RwLock::new(ty))),
									);
							} else {
								let aliased = self.parse_identifier()?;

								Arc::get_mut(&mut self.interface).unwrap()
									.children
									.insert(
										Identifier::from_parent(scope, name),
										ModuleItemInterface::Alias(aliased),
									);
							}

							self.check_semicolon()?;
						} else {
							// No '=' token, just bring the name into scope
							let name = names.remove(0);

							Arc::get_mut(&mut self.interface).unwrap()
								.children
								.insert(
									Identifier::from_parent(scope, name.path.last().unwrap().clone()),
									ModuleItemInterface::Alias(name),
								);

							self.check_semicolon()?;
						}
					} else {
						for name in names {
							Arc::get_mut(&mut self.interface).unwrap()
								.children
								.insert(
									Identifier::from_parent(scope, name.name().clone()),
									ModuleItemInterface::Alias(name),
								);
						}

						self.check_semicolon()?;
					}
				}

				Token::Keyword("module") => {
					let Token::Name(module) = self.get_next()? else {
						return self.err(ComuneErrCode::UnexpectedToken)
					};

					match self.get_next()? {
						Token::Other(';') => {
							// TODO: Add submodule to import list
							Arc::get_mut(&mut self.interface).unwrap().import_names.insert(ModuleImportKind::Child(module));
							self.get_next()?;
						}

						Token::Other('{') => {
							self.current_scope.path.push(module);

							let scope = self.current_scope.clone();
							self.parse_namespace(&scope)?;
							self.current_scope.path.pop();
						}

						_ => return self.err(ComuneErrCode::UnexpectedToken)
					}
					
				}

				Token::Keyword(_) => {
					return self.err(ComuneErrCode::UnexpectedKeyword);
				}

				_ => {
					// Parse declaration/definition
					let (name, mut protos, mut defs) =
						self.parse_namespace_declaration(current_attributes)?;

					let id = Identifier::from_parent(scope, name);
					
					match (&mut protos, &mut defs) {

						(ModuleItemInterface::Functions(fns), ModuleItemImpl::Functions(asts)) => {

							let module_interface = Arc::get_mut(&mut self.interface).unwrap();
		
							if let Some(ModuleItemInterface::Functions(existing)) =
								module_interface.children.get_mut(&id)
							{
								existing.append(fns);
							} else {
								module_interface.children.insert(id.clone(), protos);
							}

							if let Some(ModuleItemImpl::Functions(existing)) =
								self.module_impl.children.get_mut(&id)
							{
								existing.append(asts);
							} else {
								self.module_impl.children.insert(id, defs);
							}
						}

						_ => todo!(),
					}
				}
			}
		}

		if self.get_current()? == Token::Eof {
			if scope.path.is_empty() {
				Ok(())
			} else {
				self.err(ComuneErrCode::UnexpectedEOF)
			}
		} else if self.get_current()? == Token::Other('}') {
			if !scope.path.is_empty() {
				self.get_next()?;
				Ok(())
			} else {
				self.err(ComuneErrCode::UnexpectedToken)
			}
		} else {
			self.get_next()?;
			Ok(())
		}
	}

	// Not super robust - add checks for namespace-level keywords and abort early if found
	fn skip_block(&self) -> ComuneResult<Token> {
		let mut current = self.get_current()?;

		if current != Token::Other('{') {
			return self.err(ComuneErrCode::UnexpectedToken);
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

	fn parse_block(&self) -> ComuneResult<Expr> {
		let begin = self.get_current_start_index();
		let mut current = self.get_current()?;

		if current != Token::Other('{') {
			return self.err(ComuneErrCode::UnexpectedToken);
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

		let end = self.get_prev_end_index();

		Ok(Expr::Atom(
			Atom::Block { items, result },
			NodeData {
				tk: SrcSpan {
					start: begin,
					len: end - begin,
				},
				ty: None,
			},
		))
	}

	fn parse_attributes(&self) -> ComuneResult<Vec<Attribute>> {
		let mut result = vec![];

		while self.get_current()? == Token::Other('@') {
			result.push(self.parse_attribute()?);
		}
		Ok(result)
	}

	fn check_semicolon(&self) -> ComuneResult<()> {
		if token_compare(&self.get_current()?, ";") {
			self.get_next()?;
			Ok(())
		} else {
			self.err(ComuneErrCode::UnexpectedToken)
		}
	}

	fn parse_namespace_declaration(
		&self,
		attributes: Vec<Attribute>,
	) -> ComuneResult<(Name, ModuleItemInterface, ModuleItemImpl)> {
		let t = self.parse_type(false)?;
		let interface;
		let item;

		let Token::Name(name) = self.get_current()? else {
			return self.err(ComuneErrCode::ExpectedIdentifier)
		};

		if let Token::Operator(op) = self.get_next()? {
			match op {
				// Function declaration
				"<" | "(" => {
					let mut type_params = vec![];

					if op == "<" {
						type_params = self.parse_type_parameter_list()?;
					}

					let t = FnPrototype {
						ret: t,
						params: self.parse_parameter_list()?,
						type_params,
						attributes,
					};

					// Past the parameter list, check if we're at a function body or not

					let ast_elem;

					match self.get_current()? {
						Token::Other('{') => {
							ast_elem = ModuleASTElem::Unparsed(self.get_current_token_index());
							self.skip_block()?;
						}

						Token::Other(';') => {
							ast_elem = ModuleASTElem::NoElem;
							self.get_next()?;
						}

						_ => return self.err(ComuneErrCode::UnexpectedToken),
					}

					interface = ModuleItemInterface::Functions(vec![Arc::new(RwLock::new(t))]);
					item = ModuleItemImpl::Functions(vec![ast_elem]);
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
					return self.err(ComuneErrCode::UnexpectedToken);
				}
			}
		} else {
			interface = ModuleItemInterface::Variable(t);
			item = todo!();
			self.check_semicolon()?;
		}

		Ok((name, interface, item))
	}

	fn parse_binding_props(&self) -> ComuneResult<Option<BindingProps>> {
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

	fn parse_statement(&self) -> ComuneResult<Stmt> {
		let begin = self.get_current_start_index();

		let binding_props = self.parse_binding_props()?;

		if self.is_at_type_token(true)? {
			// This is a declaration

			let ty = self.parse_type(true)?;

			let Token::Name(name) = self.get_current()? else {
				return self.err(ComuneErrCode::ExpectedIdentifier)
			};

			let mut expr = None;

			if token_compare(&self.get_next()?, "=") {
				self.get_next()?;
				expr = Some(self.parse_expression()?);
			}

			let stmt_result = Stmt::Decl(
				vec![(ty, name, binding_props.unwrap_or_default())],
				expr,
				SrcSpan {
					start: begin,
					len: self.get_prev_end_index() - begin,
				},
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

	fn parse_pattern(&self) -> ComuneResult<Pattern> {
		let props = self.parse_binding_props()?;

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
						props: props.unwrap_or_default(),
					}))
				}

				Token::Other('{') => todo!(),

				_ => self.err(ComuneErrCode::UnexpectedToken),
			}
		} else {
			self.err(ComuneErrCode::UnexpectedToken)
		}
	}

	fn parse_expression(&self) -> ComuneResult<Expr> {
		self.parse_expression_bp(0)
	}

	// World's most hacked-together pratt parser (tm)
	fn parse_expression_bp(&self, min_bp: u8) -> ComuneResult<Expr> {
		let mut current = self.get_current()?;
		let begin_lhs = self.get_current_start_index();

		// Get initial part of expression, could be an Atom or the operator of a unary Cons
		let mut lhs = match current {
			// Parse atom
			Token::StringLiteral(_)
			| Token::CStringLiteral(_)
			| Token::NumLiteral(_, _)
			| Token::BoolLiteral(_)
			| Token::Operator("[")
			| Token::Keyword(_) => Expr::Atom(
				self.parse_atom()?,
				NodeData {
					ty: None,
					tk: SrcSpan {
						start: begin_lhs,
						len: self.get_prev_end_index() - begin_lhs,
					},
				},
			),

			_ if self.is_at_identifier_token()? => Expr::Atom(
				self.parse_atom()?,
				NodeData {
					ty: None,
					tk: SrcSpan {
						start: begin_lhs,
						len: self.get_prev_end_index() - begin_lhs,
					},
				},
			),

			// Handle unary prefix operators
			Token::Operator(tk) => {
				let Some(op) = Operator::get_operator(tk, false) else {
						return self.err(ComuneErrCode::UnexpectedToken)
					};

				self.get_next()?;

				if let Operator::Call = op {
					// Special case; parse sub-expression
					let sub = self.parse_expression_bp(0)?;

					current = self.get_current()?;

					if let Token::Operator(op) = current {
						if op != ")" {
							return self.err(ComuneErrCode::UnexpectedToken);
						}
						self.get_next()?;
						sub
					} else {
						return self.err(ComuneErrCode::UnexpectedToken);
					}
				} else {
					let rhs = self.parse_expression_bp(op.get_binding_power())?;

					let end_index = self.get_prev_end_index();

					let tk = SrcSpan {
						start: begin_lhs,
						len: end_index - begin_lhs,
					};
					Expr::Unary(Box::new(rhs), op, NodeData { ty: None, tk })
				}
			}

			_ => {
				return self.err(ComuneErrCode::UnexpectedToken);
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

					let end_index = self.get_prev_end_index();
					let tk = SrcSpan {
						start: begin_lhs,
						len: end_index - begin_lhs,
					};

					lhs = Expr::create_cast(lhs, goal_t, NodeData { ty: None, tk });
				}

				Operator::PostInc | Operator::PostDec => {
					let tk = SrcSpan {
						start: begin_lhs,
						len: self.get_prev_end_index() - begin_lhs,
					};

					// Create compound assignment expression
					lhs = Expr::Cons(
						[
							Box::new(lhs),
							Box::new(Expr::Atom(
								Atom::IntegerLit(1, None),
								NodeData {
									ty: None,
									tk: SrcSpan::new(),
								},
							)),
						],
						match op {
							Operator::PostInc => Operator::AssAdd,
							Operator::PostDec => Operator::AssSub,
							_ => panic!(),
						},
						NodeData { ty: None, tk },
					);
				}

				Operator::Subscr => {
					let rhs = self.parse_expression_bp(rbp)?;
					let end_rhs = self.get_prev_end_index();

					lhs = Expr::Cons(
						[Box::new(lhs), Box::new(rhs)],
						op,
						NodeData {
							ty: None,
							tk: SrcSpan {
								start: begin_rhs,
								len: end_rhs - begin_rhs,
							},
						},
					);

					if self.get_current()? == Token::Operator("]") {
						self.get_next()?;
					} else {
						return self.err(ComuneErrCode::UnexpectedToken);
					}
				}

				_ => {
					let rhs = self.parse_expression_bp(rbp)?;
					let end_rhs = self.get_prev_end_index();

					lhs = Expr::Cons(
						[Box::new(lhs), Box::new(rhs)],
						op,
						NodeData {
							ty: None,
							tk: SrcSpan {
								start: begin_rhs,
								len: end_rhs - begin_rhs,
							},
						},
					);
				}
			}
		}

		Ok(lhs)
	}

	fn parse_atom(&self) -> ComuneResult<Atom> {
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

									inits.push((member_name, expr));
								} else if self.get_current()? != Token::Other('}') {
									return self.err(ComuneErrCode::UnexpectedToken);
								}
							}

							self.consume(&Token::Other('}'))?;

							result = Some(Atom::AlgebraicLit(
								Type::TypeRef(ItemRef::Resolved(found)),
								inits,
							));
						} else {
							return self.err(ComuneErrCode::UnexpectedToken);
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

						self.interface
							.with_item(&id, &self.current_scope, |item, _| {
								is_function = matches!(item, ModuleItemInterface::Functions(..));
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
								return self.err(ComuneErrCode::UnexpectedToken);
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
			// Not at an identifier, parse the other kinds of Atom

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

							_ => return self.err(ComuneErrCode::InvalidSuffix),
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

				Token::Operator("[") => {
					// Array literal

					let mut elements = vec![];

					loop {
						elements.push(self.parse_expression()?);

						if self.get_current()? == Token::Other(',') {
							self.get_next()?;
						} else if self.get_current()? == Token::Operator("]") {
							break;
						} else {
							return self.err(ComuneErrCode::UnexpectedToken);
						}
					}

					self.consume(&Token::Operator("]"))?;

					result = Some(Atom::ArrayLit(elements));
				}

				Token::Keyword(keyword) => match keyword {
					"return" => {
						// Parse return statement

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
							return self.err(ComuneErrCode::UnexpectedToken);
						}

						current = self.get_next()?;

						let mut branches = vec![];

						while current != Token::Other('}') {
							let branch_pat = self.parse_pattern()?;
							let branch_block;

							if self.get_current()? != Token::Operator("=>") {
								return self.err(ComuneErrCode::UnexpectedToken);
							}

							if self.get_next()? == Token::Other('{') {
								branch_block = self.parse_block()?;
							} else {
								branch_block = self.parse_expression()?;

								// After a bare expression, a comma is required
								if self.get_current()? != Token::Other(',') {
									return self.err(ComuneErrCode::UnexpectedToken);
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

					"if" => {
						// Parse if statement

						// Parse condition
						let cond = self.parse_expression()?;

						// Parse body
						let body;
						let mut else_body = None;

						if token_compare(&self.get_current()?, "{") {
							body = self.parse_block()?;
						} else {
							return self.err(ComuneErrCode::UnexpectedToken);
						}

						if token_compare(&self.get_current()?, "else") {
							self.get_next()?;

							if token_compare(&self.get_current()?, "{") {
								else_body = Some(self.parse_block()?);
							} else {
								return self.err(ComuneErrCode::UnexpectedToken);
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
						self.consume(&Token::Operator("("))?;

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
							return self.err(ComuneErrCode::UnexpectedToken);
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
					_ => return self.err(ComuneErrCode::UnexpectedKeyword),
				},

				_ => return self.err(ComuneErrCode::UnexpectedToken),
			};
		}

		Ok(result.unwrap())
	}

	fn find_type(&self, typename: &Identifier) -> Option<Type> {
		self.interface.resolve_type(typename, &self.current_scope)
	}

	// Returns true if the current token is the start of a Type.
	// In ambiguous contexts (i.e. function blocks), `resolve_idents` enables basic name resolution
	fn is_at_type_token(&self, resolve_idents: bool) -> ComuneResult<bool> {
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
					.interface
					.resolve_type(&typename, &self.current_scope)
					.is_some())
			} else {
				self.lexer.borrow_mut().seek_token_idx(current_idx);

				Ok(true)
			}
		} else {
			Ok(false)
		}
	}

	fn is_at_identifier_token(&self) -> ComuneResult<bool> {
		Ok(matches!(
			self.get_current()?,
			Token::Name(_) | Token::Operator("::" | "<")
		))
	}

	fn parse_identifier(&self) -> ComuneResult<Identifier> {
		if !self.is_at_identifier_token()? {
			return self.err(ComuneErrCode::ExpectedIdentifier);
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

				_ => return self.err(ComuneErrCode::UnexpectedToken),
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
				return self.err(ComuneErrCode::UnexpectedToken);
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

	fn parse_multi_identifier(&self) -> ComuneResult<Vec<Identifier>> {
		if !self.is_at_identifier_token()? {
			return self.err(ComuneErrCode::ExpectedIdentifier);
		}

		let absolute = if self.get_current()? == Token::Operator("::") {
			self.get_next()?;
			true
		} else {
			false
		};

		self.parse_multi_identifier_component(absolute)
	}

	fn parse_multi_identifier_component(&self, absolute: bool) -> ComuneResult<Vec<Identifier>> {
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

					while self.get_current()? != Token::Other('}') {
						let mut sub_paths = self.parse_multi_identifier_component(absolute)?;

						for sub_path in &mut sub_paths {
							let mut sub_path_prefix = current.path.clone();

							sub_path_prefix.append(&mut sub_path.path);

							sub_path.path = sub_path_prefix
						}

						result.append(&mut sub_paths);

						if self.get_current()? == Token::Other(',') {
							self.get_next()?;
						}
					}

					self.consume(&Token::Other('}'))?;
				}

				_ => return self.err(ComuneErrCode::UnexpectedToken),
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

	fn parse_parameter_list(&self) -> ComuneResult<FnParamList> {
		let mut result = FnParamList {
			params: vec![],
			variadic: false,
		};

		if token_compare(&self.get_current()?, "(") {
			self.get_next()?;
		} else {
			return self.err(ComuneErrCode::UnexpectedToken);
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
					return self.err(ComuneErrCode::UnexpectedToken);
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
					self.err(ComuneErrCode::UnexpectedToken)
				}
			}

			_ => self.err(ComuneErrCode::UnexpectedToken),
		}
	}

	fn parse_type(&self, immediate_resolve: bool) -> ComuneResult<Type> {
		let mut result;

		if !self.is_at_type_token(immediate_resolve)? {
			return self.err(ComuneErrCode::ExpectedIdentifier);
		}

		if self.get_current()? == Token::Operator("(") {
			let (kind, types) = self.parse_tuple_type(immediate_resolve)?;

			Ok(Type::Tuple(kind, types))
		} else if self.is_at_identifier_token()? {
			let typename = self.parse_identifier()?;

			if immediate_resolve {
				if let Some(ty) = self.interface.resolve_type(&typename, &self.current_scope) {
					result = ty;
				} else {
					return self.err(ComuneErrCode::UnresolvedTypename(typename.to_string()));
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

							_ => return self.err(ComuneErrCode::UnexpectedToken),
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
			self.err(ComuneErrCode::UnexpectedToken)
		}
	}

	fn parse_attribute(&self) -> ComuneResult<Attribute> {
		if !token_compare(&self.get_current()?, "@") {
			return self.err(ComuneErrCode::UnexpectedToken); // You called this from the wrong place lol
		}

		let name = self.get_next()?;
		let mut result;

		if let Token::Name(name) = name {
			result = Attribute {
				name: name.to_string(),
				args: vec![],
			};
		} else {
			return self.err(ComuneErrCode::ExpectedIdentifier);
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

	fn parse_type_parameter_list(&self) -> ComuneResult<TypeParamList> {
		if !token_compare(&self.get_current()?, "<") {
			return self.err(ComuneErrCode::UnexpectedToken);
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

								_ => return self.err(ComuneErrCode::UnexpectedToken),
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

						_ => return self.err(ComuneErrCode::UnexpectedToken),
					}
				}

				Token::Operator(">") => break,

				_ => {
					return self.err(ComuneErrCode::UnexpectedToken);
				}
			}
		}

		self.get_next()?;

		Ok(result)
	}

	fn parse_type_argument_list(&self) -> ComuneResult<Vec<Type>> {
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
			return self.err(ComuneErrCode::UnexpectedToken);
		}

		// consume closing angle bracket
		self.get_next()?;

		Ok(result)
	}

	fn parse_tuple_type(&self, immediate_resolve: bool) -> ComuneResult<(TupleKind, Vec<Type>)> {
		let mut types = vec![];

		if self.get_current()? != Token::Operator("(") {
			return self.err(ComuneErrCode::UnexpectedToken);
		}

		self.get_next()?;

		let mut kind = None;

		loop {
			types.push(self.parse_type(immediate_resolve)?);

			match self.get_current()? {
				Token::Other(',') => {
					// Check if tuple kind is consistent
					if matches!(kind, Some(TupleKind::Sum)) {
						return self.err(ComuneErrCode::UnexpectedToken);
					}

					kind = Some(TupleKind::Product);
				}

				Token::Operator("|") => {
					// Ditto
					if matches!(kind, Some(TupleKind::Product)) {
						return self.err(ComuneErrCode::UnexpectedToken);
					}

					kind = Some(TupleKind::Sum);
				}

				Token::Operator(")") => break,

				_ => {
					return self.err(ComuneErrCode::UnexpectedToken);
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
