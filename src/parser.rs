use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Arc, RwLock};

use crate::ast::pattern::{Binding, Pattern};
use crate::constexpr::ConstExpr;
use crate::errors::{ComuneErrCode, ComuneError};
use crate::lexer::{Lexer, SrcSpan, Token};

use crate::ast::controlflow::ControlFlow;
use crate::ast::expression::{Atom, Expr, FnRef, NodeData, Operator, XtorKind};
use crate::ast::module::{
	Identifier, ItemRef, ModuleASTElem, ModuleImpl, ModuleImportKind, ModuleInterface,
	ModuleItemInterface, Name,
};
use crate::ast::statement::Stmt;
use crate::ast::traits::{ImplBlockInterface, TraitInterface, TraitRef};
use crate::ast::types::{
	Basic, BindingProps, DataLayout, FloatSize, FnParamList, FnPrototype, GenericArg, GenericArgs,
	GenericParam, Generics, TupleKind, Type, TypeDef, Visibility,
};
use crate::ast::{Attribute, FnScope};

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
	pub interface: ModuleInterface,
	pub module_impl: ModuleImpl,
	pub lexer: RefCell<Lexer>,
	current_scope: Arc<Identifier>,
}

enum DeclParseResult {
	Function(Name, Arc<FnPrototype>),
	Variable(Name, Type),
}

impl<'ctx> Parser {
	pub fn new(lexer: Lexer, module_name: Identifier) -> Parser {
		Parser {
			interface: ModuleInterface::new(module_name),
			module_impl: ModuleImpl::new(),
			lexer: RefCell::new(lexer),
			current_scope: Arc::new(Identifier::new(true)),
		}
	}

	fn err<T>(&self, code: ComuneErrCode) -> ComuneResult<T> {
		Err(ComuneError::new(
			code,
			self.lexer.borrow().current().unwrap().0,
		))
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

		self.parse_namespace(&Identifier::new(true))?;

		Ok(&self.interface)
	}

	pub fn generate_ast(&mut self) -> ComuneResult<()> {
		let mut fn_impls = HashMap::new();

		for (proto, ast) in &self.module_impl.fn_impls {
			// Parse function block
			if let ModuleASTElem::Unparsed(idx) = ast {
				self.lexer.borrow_mut().seek_token_idx(*idx);

				let scope = FnScope::new(
					&self.interface,
					proto.path.clone(),
					proto.ret.clone(),
					&proto.generics,
				);

				fn_impls.insert(
					proto.clone(),
					ModuleASTElem::Parsed(self.parse_block(&scope)?),
				);
			}
		}

		self.module_impl.fn_impls = fn_impls;

		Ok(())
	}

	pub fn parse_namespace(&mut self, scope: &Identifier) -> ComuneResult<()> {
		while !matches!(self.get_current()?, Token::Eof | Token::Other('}')) {
			let current_attributes = self.parse_attributes()?;

			// This should be set to `false` by any declaration that "consumes" it
			let mut unsafe_token_store = false;
			let decl_start_token = self.lexer.borrow().current_token_index();

			if self.get_current()? == Token::Keyword("unsafe") {
				self.get_next()?;
				unsafe_token_store = true
			}

			match self.get_current()? {
				Token::Other(';') => {
					self.get_next()?;
				}

				Token::Keyword("enum") => {
					let def = Arc::new(RwLock::new(TypeDef::new()));
					let mut def_write = def.write().unwrap();

					let Token::Name(name) = self.get_next()? else { return self.err(ComuneErrCode::ExpectedIdentifier) };
					let full_name = Identifier::from_parent(scope, name);

					self.get_next()?;

					def_write.generics = self.parse_generic_param_list(None)?;

					let self_ty = Type::TypeRef {
						def: Arc::downgrade(&def),
						args: def_write.generics.get_as_arg_list(),
					};

					self.consume(&Token::Other('{'))?;

					let parent_name = Identifier {
						qualifier: (Some(Box::new(self_ty.clone())), None),
						path: vec![],
						absolute: true,
					};

					loop {
						let attributes = self.parse_attributes()?;

						match self.get_current()? {
							Token::Name(variant_name) => {
								let variant = if self.get_next()? == Token::Other('{') {
									self.parse_struct_body(
										variant_name.clone(),
										&parent_name,
										def_write.generics.clone(),
										attributes,
									)?
								} else {
									Arc::new(RwLock::new(TypeDef {
										members: vec![],
										variants: vec![],
										name: Identifier::from_parent(
											&parent_name,
											variant_name.clone(),
										),
										layout: DataLayout::Declared,
										generics: def_write.generics.clone(),
										attributes,
										init: vec![],
										drop: None,
									}))
								};

								def_write.variants.push((variant_name, variant));

								match self.get_current()? {
									Token::Other(',') => self.get_next()?,

									Token::Other('}') => break,

									_ => return self.err(ComuneErrCode::UnexpectedToken),
								};
							}

							Token::Keyword(k @ ("new" | "drop")) => {
								let func = self.parse_xtor(
									scope,
									def_write.generics.clone(),
									&self_ty,
									k,
								)?;

								match k {
									"drop" => {
										// TODO: Proper error reporting
										assert!(def_write.drop.is_none());
										def_write.drop.replace(func);
									}

									"new" => {
										def_write.init.push(func);
									}

									_ => unreachable!(),
								}
							}

							Token::Other('}') => break,

							_ => return self.err(ComuneErrCode::UnexpectedToken),
						}
					}

					self.get_next()?; // Consume closing brace

					def_write.attributes = current_attributes;
					def_write.name = full_name.clone();

					drop(def_write);

					self.interface
						.children
						.insert(full_name, ModuleItemInterface::Type(def));
				}

				Token::Keyword("struct") => {
					let Token::Name(name) = self.get_next()? else {
						return self.err(ComuneErrCode::UnexpectedToken)
					};

					self.get_next()?;

					let generics = self.parse_generic_param_list(None)?;

					// Register algebraic type
					let def = self.parse_struct_body(name, scope, generics, current_attributes)?;
					let def_name = def.read().unwrap().name.clone();

					self.interface
						.children
						.insert(def_name, ModuleItemInterface::Type(def));
				}

				Token::Keyword("trait") => {
					let Token::Name(name) = self.get_next()? else {
						return self.err(ComuneErrCode::UnexpectedToken);
					};

					self.get_next()?;

					let generics = self.parse_generic_param_list(None)?;

					let mut this_trait = TraitInterface {
						items: HashMap::new(),
						generics,
						supers: vec![],
						attributes: current_attributes,
					};

					self.consume(&Token::Other('{'))?;

					while self.get_current()? != Token::Other('}') {
						let func_attributes = self.parse_attributes()?;

						match self.parse_namespace_declaration(
							func_attributes,
							Some(&Type::TypeParam(0)),
						)? {
							(DeclParseResult::Function(name, proto), ast) => {
								self.module_impl.fn_impls.insert(proto.clone(), ast);

								if let Some(existing) = this_trait.items.get_mut(&name) {
									existing.push(proto);
								} else {
									this_trait.items.insert(name, vec![proto]);
								}
							}

							(DeclParseResult::Variable(..), _) => todo!(),
						}

						self.get_current()?;
					}

					self.get_next()?; // Consume closing brace

					self.interface.children.insert(
						Identifier::from_parent(scope, name),
						ModuleItemInterface::Trait(Arc::new(RwLock::new(this_trait))),
					);
				}

				Token::Keyword("impl") => {
					self.get_next()?;

					// Parse generic parameters
					let params = self.parse_generic_param_list(None)?;

					// Parse type or trait name, depending on if the next token is "for"
					let mut impl_ty = self.parse_type(None)?;
					let mut trait_name = None;

					if self.get_current()? == Token::Keyword("for") {
						self.get_next()?;

						// We parsed the trait as a type, so extract it
						let Type::Unresolved { name, scope, generic_args, .. } = impl_ty else {
							return self.err(ComuneErrCode::ExpectedIdentifier); // TODO: Proper error
						};

						trait_name = Some(ItemRef::<TraitRef>::Unresolved {
							name,
							scope,
							generic_args,
						});

						// Then parse the implementing type, for real this time
						impl_ty = self.parse_type(None)?;
					}

					// Consume brace
					self.consume(&Token::Other('{'))?;

					// Parse functions
					let mut functions: HashMap<_, Vec<Arc<FnPrototype>>> = HashMap::new();

					let canonical_root = Identifier {
						qualifier: (
							Some(Box::new(impl_ty.clone())),
							trait_name.clone().map(Box::new),
						),
						path: vec![],
						absolute: true,
					};

					while self.get_current()? != Token::Other('}') {
						let func_attributes = self.parse_attributes()?;

						let ret = self.parse_type(None)?;
						let props = self.parse_binding_props()?.unwrap_or_default();

						let Token::Name(fn_name) = self.get_current()? else {
							return self.err(ComuneErrCode::ExpectedIdentifier);
						};

						self.get_next()?;

						let generics = self.parse_generic_param_list(None)?;
						let params = self.parse_parameter_list(Some(&impl_ty), None)?;
						let ast = ModuleASTElem::Unparsed(self.get_current_token_index());

						self.skip_block()?;

						let proto = Arc::new(FnPrototype {
							path: Identifier::from_parent(&canonical_root, fn_name.clone()),
							ret: (props, ret),
							params,
							generics,
							attributes: func_attributes,
							is_unsafe: if unsafe_token_store {
								unsafe_token_store = false;
								true
							} else {
								false
							},
						});

						if let Some(existing) = functions.get_mut(&fn_name) {
							existing.push(proto.clone());
						} else {
							functions.insert(fn_name.clone(), vec![proto.clone()]);
						}

						self.module_impl.fn_impls.insert(proto, ast);
					}

					// Register impl to solver
					self.interface.impl_solver.register_impl(
						impl_ty.clone(),
						ImplBlockInterface {
							implements: trait_name.clone(),
							functions,
							types: HashMap::new(),
							scope: self.current_scope.clone(),

							canonical_root,
							params,
						},
					);

					self.consume(&Token::Other('}'))?;
				}

				Token::Keyword("import") => {
					// Register import statement
					self.get_next()?;

					if self.is_at_identifier_token()? {
						let import = ModuleImportKind::Extern(self.parse_identifier(None)?);

						self.interface.import_names.insert(import);

						self.check_semicolon()?;
					} else {
						return self.err(ComuneErrCode::ExpectedIdentifier);
					}
				}

				Token::Keyword("type") => {
					let Token::Name(name) = self.get_next()? else {
						return self.err(ComuneErrCode::ExpectedIdentifier)
					};

					self.get_next()?;

					let generics = self.parse_generic_param_list(None)?;

					self.consume(&Token::Operator("="))?;

					let ty = self.parse_type(None)?;

					self.interface.children.insert(
						Identifier::from_parent(scope, name),
						ModuleItemInterface::TypeAlias(Arc::new(RwLock::new((ty, generics)))),
					);
				}

				Token::Keyword("using") => {
					self.get_next()?;

					let mut names = self.parse_multi_identifier()?;

					if names.len() == 1 {
						if self.get_current()? == Token::Operator("=") {
							// Found a '=' token, so fetch the name to alias
							self.get_next()?;

							let name = names[0].expect_scopeless()?.clone();
							let aliased = self.parse_identifier(None)?;

							self.interface.children.insert(
								Identifier::from_parent(scope, name),
								ModuleItemInterface::Alias(aliased),
							);

							self.check_semicolon()?;
						} else {
							// No '=' token, just bring the name into scope
							let name = names.remove(0);

							self.interface.children.insert(
								Identifier::from_parent(scope, name.path.last().unwrap().clone()),
								ModuleItemInterface::Alias(name),
							);

							self.check_semicolon()?;
						}
					} else {
						for name in names {
							self.interface.children.insert(
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
							self.interface
								.import_names
								.insert(ModuleImportKind::Child(module));
							self.get_next()?;
						}

						Token::Other('{') => {
							let old_scope = self.current_scope.clone();
							self.current_scope =
								Arc::new(Identifier::from_parent(&old_scope, module));
							let scope = self.current_scope.clone();
							self.parse_namespace(&scope)?;
							self.current_scope = old_scope;
						}

						_ => return self.err(ComuneErrCode::UnexpectedToken),
					}
				}

				Token::Keyword(_) => {
					return self.err(ComuneErrCode::UnexpectedKeyword);
				}

				_ => {
					// Parse declaration/definition

					match self.parse_namespace_declaration(current_attributes, None)? {
						(DeclParseResult::Function(name, mut proto), ast) => {
							if unsafe_token_store {
								unsafe_token_store = false;
								Arc::get_mut(&mut proto).unwrap().is_unsafe = true
							}

							let id = Identifier::from_parent(scope, name);

							self.module_impl.fn_impls.insert(proto.clone(), ast);

							if let Some(ModuleItemInterface::Functions(existing)) =
								self.interface.children.get(&id)
							{
								existing.write().unwrap().push(proto);
							} else {
								self.interface.children.insert(
									id,
									ModuleItemInterface::Functions(Arc::new(RwLock::new(vec![
										proto,
									]))),
								);
							}
						}

						(DeclParseResult::Variable(name, ty), ModuleASTElem::NoElem) => {
							let id = Identifier::from_parent(scope, name);

							self.interface.children.insert(
								id,
								ModuleItemInterface::Variable(Arc::new(RwLock::new(ty))),
							);
						}

						_ => todo!(),
					}
				}
			}

			if unsafe_token_store {
				self.lexer.borrow_mut().seek_token_idx(decl_start_token);
				return self.err(ComuneErrCode::UnexpectedKeyword);
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

	fn parse_struct_body(
		&mut self,
		name: Name,
		scope: &Identifier,
		generics: Generics,
		mut attributes: Vec<Attribute>,
	) -> ComuneResult<Arc<RwLock<TypeDef>>> {
		let mut current_visibility = Visibility::Public;

		let def = Arc::new(RwLock::new(TypeDef::new()));
		let mut def_write = def.write().unwrap();

		let full_name = Identifier::from_parent(scope, name);

		def_write.name = full_name.clone();
		def_write.attributes = attributes;
		attributes = vec![];

		// Get the generic params
		def_write.generics = generics;

		let self_ty = Type::TypeRef {
			def: Arc::downgrade(&def),
			args: def_write.generics.get_as_arg_list(),
		};

		self.consume(&Token::Other('{'))?; // Consume brace

		loop {
			match self.get_current()? {
				Token::Name(_) => {
					let result = self.parse_namespace_declaration(attributes, None)?;
					attributes = vec![];

					match result.0 {
						DeclParseResult::Variable(name, t) => {
							def_write
								.members
								.push((name, t, current_visibility.clone()))
						}

						_ => todo!(),
					}
				}

				Token::Keyword(k @ ("public" | "private" | "protected")) => {
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
						_ => unreachable!(),
					}

					self.consume(&Token::Other(':'))?;
				}

				Token::Keyword(k @ ("new" | "drop")) => {
					let func = self.parse_xtor(scope, def_write.generics.clone(), &self_ty, k)?;

					match k {
						"drop" => {
							// TODO: Proper error reporting
							assert!(def_write.drop.is_none());
							def_write.drop.replace(func);
						}

						"new" => {
							def_write.init.push(func);
						}

						_ => unreachable!(),
					}
				}

				Token::Keyword(_) => return self.err(ComuneErrCode::UnexpectedKeyword),

				Token::Other('}') => break,

				_ => return self.err(ComuneErrCode::UnexpectedToken),
			}
		}

		self.consume(&Token::Other('}'))?; // Consume brace

		drop(def_write);
		Ok(def)
	}

	fn parse_xtor(
		&mut self,
		scope: &Identifier,
		base_generics: Generics,
		self_ty: &Type,
		keyword: &str,
	) -> ComuneResult<Arc<FnPrototype>> {
		self.get_next()?;

		let mut generics = self.parse_generic_param_list(None)?;
		generics.add_base_generics(base_generics);

		let params = self.parse_parameter_list(Some(&self_ty), None)?;

		let mut path = Identifier::from_parent(&scope, keyword.into());
		path.qualifier.0 = Some(Box::new(self_ty.clone()));

		let func = Arc::new(FnPrototype {
			path,
			params,
			generics,
			ret: (BindingProps::default(), Type::Basic(Basic::Void)),
			attributes: vec![],
			is_unsafe: false,
		});

		// Skip c'tor/d'tor body
		let ast = self.get_current_token_index();
		self.skip_block()?;

		// Add fn to module impl
		self.module_impl
			.fn_impls
			.insert(func.clone(), ModuleASTElem::Unparsed(ast));

		Ok(func)
	}

	fn skip_expression(&self) -> ComuneResult<()> {
		loop {
			match self.get_next()? {
				Token::Other('{') => self.skip_block()?,

				Token::Other(';') | Token::Eof => break,

				_ => {
					self.get_next()?;
				}
			}
		}

		Ok(())
	}

	fn skip_block(&self) -> ComuneResult<()> {
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

		self.get_next()?;
		Ok(())
	}

	fn parse_block(&self, scope: &FnScope<'ctx>) -> ComuneResult<Expr> {
		let begin = self.get_current_start_index();
		let mut current = self.get_current()?;

		let is_unsafe;

		if current == Token::Keyword("unsafe") {
			is_unsafe = true;
			current = self.get_next()?;
		} else {
			is_unsafe = false;
		}

		if current != Token::Other('{') {
			return self.err(ComuneErrCode::UnexpectedToken);
		}

		let mut items = vec![];
		let mut result = None;

		self.get_next()?;

		while self.get_current()? != Token::Other('}') {
			let stmt = self.parse_statement(scope)?;

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
			} else if matches!(stmt, Stmt::Expr(Expr::Atom(Atom::Block { .. }, _))) {
				semicolon_optional = true;
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
			Atom::Block {
				items,
				result,
				is_unsafe,
			},
			NodeData {
				span: SrcSpan {
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
		self_ty: Option<&Type>,
	) -> ComuneResult<(DeclParseResult, ModuleASTElem)> {
		let t = self.parse_type(None)?;
		let props = self.parse_binding_props()?.unwrap_or_default();
		let interface;
		let item;

		let Token::Name(name) = self.get_current()? else {
			return self.err(ComuneErrCode::ExpectedIdentifier)
		};

		if let Token::Operator(op) = self.get_next()? {
			match op {
				// Function declaration
				"<" | "(" => {
					let generics = self.parse_generic_param_list(None)?;

					let t = FnPrototype {
						path: Identifier::from_parent(&self.current_scope, name.clone()),
						ret: (props, t),
						params: self.parse_parameter_list(self_ty, None)?,
						generics,
						attributes,
						is_unsafe: false,
					};

					// Past the parameter list, check if we're at a function body or not

					match self.get_current()? {
						Token::Other('{') => {
							item = ModuleASTElem::Unparsed(self.get_current_token_index());
							self.skip_block()?;
						}

						Token::Other(';') => {
							item = ModuleASTElem::NoElem;
							self.get_next()?;
						}

						_ => return self.err(ComuneErrCode::UnexpectedToken),
					};

					interface = DeclParseResult::Function(name, Arc::new(t));
				}

				"=" => {
					self.get_next()?;

					item = ModuleASTElem::Unparsed(self.get_current_token_index());
					interface = DeclParseResult::Variable(name, t);

					self.skip_expression()?;
					self.check_semicolon()?;
				}

				_ => {
					return self.err(ComuneErrCode::UnexpectedToken);
				}
			}
		} else {
			self.check_semicolon()?;
			interface = DeclParseResult::Variable(name, t);
			item = ModuleASTElem::NoElem;
		}

		Ok((interface, item))
	}

	fn parse_binding_props(&self) -> ComuneResult<Option<BindingProps>> {
		let mut props = BindingProps::default();

		if !matches!(
			self.get_current()?,
			Token::Keyword("new" | "mut") | Token::Operator("&")
		) {
			return Ok(None);
		}

		// a binding can be *either* `new` or `mut`.
		// if it is `new`, it must also be `&`
		if self.get_current()? == Token::Keyword("new") {
			props.is_new = true;
			props.is_ref = true;

			self.get_next()?;
			self.consume(&Token::Operator("&"))?;

			return Ok(Some(props));
		}

		if self.get_current()? == Token::Keyword("mut") {
			props.is_mut = true;
			self.get_next()?;
		}

		if self.get_current()? == Token::Operator("&") {
			props.is_ref = true;
			self.get_next()?;
		}

		Ok(Some(props))
	}

	fn parse_statement(&self, scope: &FnScope<'ctx>) -> ComuneResult<Stmt> {
		let begin = self.get_current_start_index();
		let begin_token = self.get_current_token_index();

		if self.is_at_type_token(Some(scope))? {
			// This is a declaration

			let ty = self.parse_type(Some(scope))?;
			let binding_props = self.parse_binding_props()?;

			let Token::Name(name) = self.get_current()? else {
				// Nope, try to parse as an expression after all
				self.lexer.borrow_mut().seek_token_idx(begin_token);

				return Ok(Stmt::Expr(self.parse_expression(scope)?))
			};

			let mut expr = None;

			if token_compare(&self.get_next()?, "=") {
				self.get_next()?;
				expr = Some(self.parse_expression(scope)?);
			}

			let span = SrcSpan {
				start: begin,
				len: self.get_prev_end_index() - begin,
			};

			let mut props = binding_props.unwrap_or_default();

			props.span = span;

			let stmt_result = Stmt::Decl(vec![(ty, name, props)], expr, span);

			Ok(stmt_result)
		} else {
			// This isn't a declaration, so parse an expression

			Ok(Stmt::Expr(self.parse_expression(scope)?))
		}
	}

	fn parse_pattern(&self, scope: &FnScope<'ctx>) -> ComuneResult<Pattern> {
		if self.is_at_type_token(Some(scope))? {
			let pattern_ty = self.parse_type(Some(scope))?;
			let props = self.parse_binding_props()?.unwrap_or_default();

			match self.get_current()? {
				Token::Name(id) => {
					self.get_next()?;

					Ok(Pattern::Binding(Binding {
						name: Some(id),
						ty: pattern_ty,
						props,
					}))
				}

				Token::Other('{') => {
					let Type::TypeRef { def, args } = &pattern_ty else {
						todo!()
					};

					let def = def.upgrade().unwrap();
					let def = def.read().unwrap();

					self.get_next()?;

					let mut patterns = vec![];

					while self.get_current()? != Token::Other('}') {
						let Token::Name(name) = self.get_current()? else {
							return self.err(ComuneErrCode::UnexpectedToken)
						};

						let Some((_, ty)) = def.get_member(&name, args) else {
							todo!()
						};

						patterns.push(Pattern::Binding(Binding {
							name: Some(name),
							ty,
							props,
						}));

						match self.get_next()? {
							Token::Other(',') => self.get_next()?,

							Token::Other('}') => break,

							_ => return self.err(ComuneErrCode::UnexpectedToken),
						};
					}

					self.get_next()?;

					Ok(Pattern::Destructure(patterns, pattern_ty))
				}

				_ => self.err(ComuneErrCode::UnexpectedToken),
			}
		} else {
			self.err(ComuneErrCode::UnexpectedToken)
		}
	}

	fn parse_expression(&self, scope: &FnScope<'ctx>) -> ComuneResult<Expr> {
		self.parse_expression_bp(0, scope)
	}

	// World's most hacked-together pratt parser (tm)
	fn parse_expression_bp(&self, min_bp: u8, scope: &FnScope<'ctx>) -> ComuneResult<Expr> {
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
			| Token::Other('{')
			| Token::Keyword(_) => Expr::Atom(
				self.parse_atom(scope)?,
				NodeData {
					ty: None,
					span: SrcSpan {
						start: begin_lhs,
						len: self.get_prev_end_index() - begin_lhs,
					},
				},
			),

			_ if self.is_at_identifier_token()? => Expr::Atom(
				self.parse_atom(scope)?,
				NodeData {
					ty: None,
					span: SrcSpan {
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
					let sub = self.parse_expression_bp(0, scope)?;

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
					let rhs = self.parse_expression_bp(op.get_binding_power(), scope)?;

					let end_index = self.get_prev_end_index();

					let tk = SrcSpan {
						start: begin_lhs,
						len: end_index - begin_lhs,
					};
					Expr::Unary(Box::new(rhs), op, NodeData { ty: None, span: tk })
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

			match op {
				Operator::Cast => {
					let goal_t = self.parse_type(Some(scope))?;
					let end_index = self.get_prev_end_index();
					let tk = SrcSpan {
						start: begin_lhs,
						len: end_index - begin_lhs,
					};

					lhs = Expr::create_cast(lhs, goal_t, NodeData { ty: None, span: tk });
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
									span: SrcSpan::new(),
								},
							)),
						],
						match op {
							Operator::PostInc => Operator::AssAdd,
							Operator::PostDec => Operator::AssSub,
							_ => panic!(),
						},
						NodeData { ty: None, span: tk },
					);
				}

				Operator::Subscr => {
					let rhs = self.parse_expression_bp(rbp, scope)?;
					let end_rhs = self.get_prev_end_index();

					lhs = Expr::Cons(
						[Box::new(lhs), Box::new(rhs)],
						op,
						NodeData {
							ty: None,
							span: SrcSpan {
								start: begin_lhs,
								len: end_rhs - begin_lhs,
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
					let rhs = self.parse_expression_bp(rbp, scope)?;
					let end_rhs = self.get_prev_end_index();

					lhs = Expr::Cons(
						[Box::new(lhs), Box::new(rhs)],
						op,
						NodeData {
							ty: None,
							span: SrcSpan {
								start: begin_lhs,
								len: end_rhs - begin_lhs,
							},
						},
					);
				}
			}
		}

		Ok(lhs)
	}

	fn parse_atom(&self, scope: &FnScope<'ctx>) -> ComuneResult<Atom> {
		let mut result;

		if self.is_at_identifier_token()? {
			let id = self.parse_identifier(Some(scope))?;

			// Variable or function name
			result = Some(Atom::Identifier(id.clone()));

			if let Token::Operator("(" | "<") = self.get_current()? {
				let start_token = self.get_current_token_index();
				let mut type_args = vec![];

				if self.get_current()? == Token::Operator("<") {
					// Here lies the Turbofish, vanquished after a battle
					// lasting months on end, at the cost of tuple syntax.

					type_args = match self.parse_generic_arg_list(Some(scope)) {
						Ok(args) => args,

						Err(ComuneError {
							code: ComuneErrCode::UnexpectedToken | ComuneErrCode::ExpectedIdentifier,
							..
						}) => {
							self.lexer.borrow_mut().seek_token_idx(start_token);

							return Ok(Atom::Identifier(id));
						}

						Err(e) => return Err(e),
					}
				}

				// Function call
				let mut args = vec![];

				if self.get_next()? != Token::Operator(")") {
					loop {
						args.push(self.parse_expression(scope)?);

						if self.get_current()? == Token::Other(',') {
							self.get_next()?;
						} else if self.get_current()? == Token::Operator(")") {
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
					generic_args: type_args,
					resolved: FnRef::None,
				});
			}
		} else {
			// Not at an identifier, parse the other kinds of Atom

			match self.get_current()? {
				Token::StringLiteral(s) => {
					self.get_next()?;

					result = Some(Atom::StringLit(s));
				}

				Token::CStringLiteral(s) => {
					self.get_next()?;

					result = Some(Atom::CStringLit(s));
				}

				Token::NumLiteral(s, suffix) => {
					self.get_next()?;

					let mut suffix_b = Basic::get_basic_type(suffix.as_str());

					if suffix_b.is_none() && !suffix.is_empty() {
						suffix_b = match suffix.as_str() {
							// Add special numeric suffixes here
							"f" => Some(Basic::Float {
								size: FloatSize::F32,
							}),

							_ => return self.err(ComuneErrCode::InvalidSuffix),
						};
					}

					let atom = if s.find('.').is_some() {
						Atom::FloatLit(s.parse::<f64>().unwrap(), suffix_b)
					} else {
						Atom::IntegerLit(
							if s.len() >= 2 {
								if matches!(&s[0..2], "0x" | "0X") {
									i128::from_str_radix(&s[2..], 16).unwrap()
								} else if matches!(&s[0..2], "0b" | "0B") {
									i128::from_str_radix(&s[2..], 2).unwrap()
								} else {
									s.parse::<i128>().unwrap()
								}
							} else {
								s.parse::<i128>().unwrap()
							}, 
							suffix_b
						)
					};

					result = Some(atom);
				}

				Token::BoolLiteral(b) => {
					self.get_next()?;

					result = Some(Atom::BoolLit(b));
				}

				Token::Operator("[") => {
					// Array literal
					self.get_next()?;

					let mut elements = vec![];

					loop {
						elements.push(self.parse_expression(scope)?);

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

				Token::Other('{') | Token::Keyword("unsafe") => {
					let Expr::Atom(block @ Atom::Block { .. }, _) = self.parse_block(scope)? else {
						panic!()
					};

					result = Some(block);
				}

				Token::Keyword(keyword) => match keyword {
					"new" => {
						self.get_next()?;

						let placement = if self.get_current()? == Token::Operator("(") {
							// Placement-new
							self.get_next()?;
							let expr = self.parse_expression(scope)?;
							self.consume(&Token::Operator(")"))?;

							Some(Box::new(expr))
						} else {
							// Regular new
							None
						};

						let Type::TypeRef { def, args: generic_args } = self.parse_typeref(Some(scope))? else {
							unreachable!()
						};

						if self.get_current()? == Token::Other('{') {
							// Parse literal constructor

							let mut inits = vec![];

							while self.get_current()? != Token::Other('}') {
								self.get_next()?;

								if let Token::Name(member_name) = self.get_current()? {
									match self.get_next()? {
										// plain `member: expr` syntax
										Token::Other(':') => {
											self.get_next()?;

											let expr = self.parse_expression(scope)?;

											inits.push((member_name, expr));
										}

										// shorthand when `expr` is equal to the member name
										Token::Other(',') | Token::Other('}') => {
											let expr = Expr::Atom(
												Atom::Identifier(Identifier::from_name(
													member_name.clone(),
													false,
												)),
												NodeData::new(),
											);

											inits.push((member_name, expr))
										}

										_ => return self.err(ComuneErrCode::UnexpectedToken),
									}
								} else if self.get_current()? != Token::Other('}') {
									return self.err(ComuneErrCode::UnexpectedToken);
								}
							}

							self.consume(&Token::Other('}'))?;

							result = Some(Atom::Constructor {
								def,
								generic_args,
								kind: XtorKind::Literal { fields: inits },
								placement,
							});
						} else if self.get_current()? == Token::Operator("(") {
							// Parse constructor call

							let mut args = vec![];

							if self.get_next()? != Token::Operator(")") {
								loop {
									args.push(self.parse_expression(scope)?);

									if self.get_current()? == Token::Other(',') {
										self.get_next()?;
									} else if self.get_current()? == Token::Operator(")") {
										break;
									} else {
										return self.err(ComuneErrCode::UnexpectedToken);
									}
								}
							}

							self.get_next()?;

							result = Some(Atom::Constructor {
								def,
								generic_args,
								kind: XtorKind::Constructor {
									args,
									resolved: FnRef::None,
								},
								placement,
							});
						} else {
							// Literal constructor with no fields
							result = Some(Atom::Constructor {
								def,
								generic_args,
								kind: XtorKind::Literal { fields: vec![] },
								placement,
							});
						}
					}

					"drop" => {
						self.get_next()?;

						let dropped = self.parse_expression(scope)?;

						result = Some(Atom::Drop(Box::new(dropped)));
					}

					"return" => {
						// Parse return statement
						let next = self.get_next()?;

						if next == Token::Other(';') || next == Token::Other('}') {
							result =
								Some(Atom::CtrlFlow(Box::new(ControlFlow::Return { expr: None })));
						} else {
							result = Some(Atom::CtrlFlow(Box::new(ControlFlow::Return {
								expr: Some(self.parse_expression(scope)?),
							})));
						}
					}

					"break" => {
						self.get_next()?;

						// TODO: Labeled break and continue

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::Break)));
					}

					"continue" => {
						self.get_next()?;

						// TODO: Labeled break and continue

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::Continue)));
					}

					"match" => {
						self.get_next()?;

						let scrutinee = self.parse_expression(scope)?;

						if self.get_current()? != Token::Other('{') {
							return self.err(ComuneErrCode::UnexpectedToken);
						}

						self.get_next()?;

						let mut branches = vec![];

						while self.get_current()? != Token::Other('}') {
							let branch_pat = self.parse_pattern(scope)?;
							let branch_block;

							if self.get_current()? != Token::Operator("=>") {
								return self.err(ComuneErrCode::UnexpectedToken);
							}

							if self.get_next()? == Token::Other('{') {
								branch_block = self.parse_block(scope)?;
							} else {
								branch_block = self.parse_expression(scope)?;

								// After a bare expression, a comma is required
								if self.get_current()? != Token::Other(',') {
									return self.err(ComuneErrCode::UnexpectedToken);
								}

								self.get_next()?;
							}

							while self.get_current()? == Token::Other(',') {
								self.get_next()?;
							}

							branches.push((branch_pat, branch_block));
						}

						self.get_next()?;

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::Match {
							scrutinee,
							branches,
						})));
					}

					"if" => {
						self.get_next()?;

						// Parse condition
						let cond = self.parse_expression(scope)?;

						// Parse body
						let body;
						let mut else_body = None;

						if token_compare(&self.get_current()?, "{") {
							body = self.parse_block(scope)?;
						} else {
							return self.err(ComuneErrCode::UnexpectedToken);
						}

						if token_compare(&self.get_current()?, "else") {
							self.get_next()?;

							match self.get_current()? {
								Token::Other('{') => else_body = Some(self.parse_block(scope)?),

								// Bit of a hack to get `else if` working
								Token::Keyword("if") => {
									else_body = Some(self.parse_expression(scope)?)
								}

								_ => return self.err(ComuneErrCode::UnexpectedToken),
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
						self.get_next()?;
						let cond = self.parse_expression(scope)?;
						let body = self.parse_block(scope)?;

						result = Some(Atom::CtrlFlow(Box::new(ControlFlow::While { cond, body })));
					}

					// Parse for loop
					"for" => {
						self.get_next()?;

						// Check opening brace
						self.consume(&Token::Operator("("))?;

						let mut init = None;
						let mut cond = None;
						let mut iter = None;

						if self.get_current()? == Token::Other(';') {
							// No init statement, skip
							self.get_next()?;
						} else {
							init = Some(self.parse_statement(scope)?); // TODO: Restrict to declaration?
							self.check_semicolon()?;
							self.get_current()?;
						}

						if self.get_current()? == Token::Other(';') {
							// No iter expression, skip
							self.get_next()?;
						} else {
							cond = Some(self.parse_expression(scope)?);
							self.check_semicolon()?;
						}

						if self.get_current()? == Token::Other(';') {
							// No cond expression, skip
							self.get_next()?;
						} else if self.get_current()? != Token::Other(')') {
							iter = Some(self.parse_expression(scope)?);
						}

						// Check closing brace
						self.consume(&Token::Operator(")"))?;

						// Parse body
						let body = self.parse_block(scope)?;

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

	// Returns true if the current token is the start of a Type.
	// In ambiguous contexts (i.e. function blocks), `resolve_idents` enables basic name resolution
	fn is_at_type_token(&self, scope: Option<&FnScope<'ctx>>) -> ComuneResult<bool> {
		let current = self.get_current()?;

		let current_idx = self.get_current_token_index();

		if current == Token::Operator("(") {
			// This might be the start of a tuple OR expression, so we gotta peek ahead whoops
			self.get_next()?;
		}

		if self.is_at_identifier_token()? {
			if let Some(scope) = scope {
				let typename = self.parse_identifier(Some(scope))?;

				self.lexer.borrow_mut().seek_token_idx(current_idx);

				Ok(scope.find_type(&typename).is_some())
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

	fn parse_identifier(&self, scope: Option<&FnScope<'ctx>>) -> ComuneResult<Identifier> {
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

			let ty = self.parse_type(scope)?;

			let tr = match self.get_current()? {
				Token::Operator("as") => {
					self.get_next()?;
					Some(Box::new(ItemRef::Unresolved {
						name: self.parse_identifier(scope)?,
						scope: self.current_scope.clone(),
						generic_args: vec![],
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

	fn parse_parameter_list(
		&self,
		self_ty: Option<&Type>,
		scope: Option<&FnScope<'ctx>>,
	) -> ComuneResult<FnParamList> {
		let mut result = FnParamList {
			params: vec![],
			variadic: false,
		};

		if token_compare(&self.get_current()?, "(") {
			self.get_next()?;
		} else {
			return self.err(ComuneErrCode::UnexpectedToken);
		}

		// Special case for self parameter
		if let Some(self_ty) = self_ty {
			let binding_props = self.parse_binding_props()?;
			let self_name = "self".into();

			if binding_props.is_some()
				|| matches!(self.get_current()?, Token::Name(name) if name == self_name)
			{
				let binding_props = binding_props.unwrap_or_default();

				result
					.params
					.push((self_ty.clone(), Some(self_name), binding_props));

				if self.get_next()? == Token::Other(',') {
					self.get_next()?;
				}
			}
		}

		while self.is_at_type_token(scope)? {
			let start = self.get_current_start_index();

			let mut param = (
				self.parse_type(scope)?,
				None,
				self.parse_binding_props()?.unwrap_or_default(),
			);

			// Check for param name
			let mut current = self.get_current()?;

			if let Token::Name(name) = current {
				param.1 = Some(name);
				self.get_next()?;
			}

			let end = self.get_prev_end_index();

			param.2.span = SrcSpan {
				start,
				len: end - start,
			};

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

	fn parse_type(&self, scope: Option<&FnScope<'ctx>>) -> ComuneResult<Type> {
		let mut result;

		if !self.is_at_type_token(scope)? {
			return self.err(ComuneErrCode::ExpectedIdentifier);
		}

		if self.get_current()? == Token::Operator("(") {
			let (kind, types) = self.parse_tuple_type(scope)?;

			Ok(Type::Tuple(kind, types))
		} else if self.is_at_identifier_token()? {
			result = self.parse_typeref(scope)?;

			loop {
				match self.get_current()? {
					Token::Operator("*") | Token::Keyword("mut") => {
						// Pointer type
						if self.get_current()? == Token::Keyword("mut") {
							let current_idx = self.get_current_token_index();

							if self.get_next()? == Token::Operator("*") {
								result = Type::Pointer {
									pointee: Box::new(result),
									mutable: true,
								};

								self.consume(&Token::Operator("*"))?;
							} else {
								self.lexer.borrow_mut().seek_token_idx(current_idx);
								break;
							}
						} else {
							result = Type::Pointer {
								pointee: Box::new(result),
								mutable: false,
							};

							self.get_next()?;
						}
					}

					Token::Operator("[") => {
						// Array or slice type
						if self.get_next()? == Token::Operator("]") {
							result = Type::Slice(Box::new(result));
						} else {
							let Some(scope) = scope else { panic!() };
							let const_expr = self.parse_expression(scope)?;

							result = Type::Array(
								Box::new(result),
								Arc::new(RwLock::new(ConstExpr::Expr(const_expr))),
							);
						}

						self.consume(&Token::Operator("]"))?;
					}

					Token::Operator("(") => {
						// Function type

						self.get_next()?;

						let ret = Box::new(result);
						let mut args = vec![];

						while self.get_current()? != Token::Operator(")") {
							let start = self.get_current_start_index();
							let ty = self.parse_type(scope)?;
							let mut props = self.parse_binding_props()?.unwrap_or_default();
							let end = self.get_prev_end_index();

							props.span = SrcSpan {
								start,
								len: end - start,
							};

							args.push((props, ty));

							match self.get_current()? {
								Token::Other(',') => self.get_next()?,

								Token::Operator(")") => break,

								_ => return self.err(ComuneErrCode::UnexpectedToken),
							};
						}

						self.get_next()?;

						result = Type::Function(ret, args);
					}

					_ => break,
				}
			}

			Ok(result)
		} else {
			self.err(ComuneErrCode::UnexpectedToken)
		}
	}

	// Parse a Type::TypeRef, like Vector<T>, Option<T>::None or <T as Add>::Result
	fn parse_typeref(&self, scope: Option<&FnScope<'ctx>>) -> ComuneResult<Type> {
		let mut result;
		let mut qualifier = None;
		let start_idx = self.get_current_start_index();

		let mut args_accum = vec![];

		loop {
			let mut typename = self.parse_identifier(scope)?;
			typename.qualifier.0 = qualifier;

			if let Some(scope) = scope {
				if let Some(ty) = scope.find_type(&typename) {
					result = ty;
				} else {
					return Err(ComuneError::new(
						ComuneErrCode::UnresolvedTypename(typename.to_string()),
						SrcSpan {
							start: start_idx,
							len: self.get_prev_end_index() - start_idx,
						},
					));
				}
			} else {
				result = Type::Unresolved {
					name: typename,
					scope: self.current_scope.clone(),
					generic_args: vec![],
					span: SrcSpan {
						start: start_idx,
						len: self.get_prev_end_index() - start_idx,
					},
				};
			}
			
			if self.get_current()? == Token::Operator("<") {				
				match self.parse_generic_arg_list(scope) {
					Ok(mut args) => {
						args_accum.append(&mut args);
					}

					Err(ComuneError {
						code: ComuneErrCode::RightShiftInGenericArgs(None, Some(mut args)),
						origin,
						span,
						..
					}) => {
						args_accum.append(&mut args);

						if !args_accum.is_empty() {
							let (Type::TypeRef { args, .. } | Type::Unresolved { generic_args: args, .. }) = &mut result else {
								panic!()
							};
			
							*args = args_accum.clone();
						}

						return Err(
							ComuneError {
								code: ComuneErrCode::RightShiftInGenericArgs(Some(result), None),
								span,
								origin,
								notes: vec![],
							}
						)
					}

					Err(err) => return Err(err)
				}
			}

			if !args_accum.is_empty() {
				let (Type::TypeRef { args, .. } | Type::Unresolved { generic_args: args, .. }) = &mut result else {
					panic!()
				};

				*args = args_accum.clone();
			}

			if self.get_current()? == Token::Operator("::") {
				qualifier = Some(Box::new(result));
				self.get_next()?;
			} else {
				break;
			}
		}

		Ok(result)
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

	fn parse_generic_param_list(&self, scope: Option<&FnScope<'ctx>>) -> ComuneResult<Generics> {
		if self.get_current()? != Token::Operator("<") {
			return Ok(Generics::new());
		}

		let mut result = vec![];
		let mut current = self.get_next()?;

		loop {
			match current {
				Token::Keyword("type") => {
					let Token::Name(name) = self.get_next()? else {
						return self.err(ComuneErrCode::UnexpectedToken)
					};

					let mut bounds = vec![];

					current = self.get_next()?;

					if let Token::Other(':') = current {
						current = self.get_next()?;

						// Collect trait bounds
						while self.is_at_identifier_token()? {
							let tr = self.parse_identifier(scope)?;

							bounds.push(ItemRef::Unresolved {
								name: tr,
								scope: self.current_scope.clone(),
								generic_args: vec![],
							});

							current = self.get_next()?;

							match current {
								Token::Operator("+") => current = self.get_next()?,

								Token::Other(',') => break,

								_ => return self.err(ComuneErrCode::UnexpectedToken),
							}
						}
					}

					result.push((name, GenericParam::Type { bounds, arg: None }));

					match &current {
						Token::Operator(">") => continue,
						Token::Other(',') => {
							current = self.get_next()?;
							continue;
						}

						_ => return self.err(ComuneErrCode::UnexpectedToken),
					}
				}

				Token::Keyword("const") => {
					todo!()
				}

				Token::Operator(">") => break,

				_ => {
					return self.err(ComuneErrCode::UnexpectedToken);
				}
			}
		}

		self.get_next()?;

		Ok(Generics::from_params(result))
	}

	fn parse_generic_arg_list(&self, scope: Option<&FnScope<'ctx>>) -> ComuneResult<GenericArgs> {
		self.get_next()?;

		let mut result = vec![];

		loop {
			let generic = match self.parse_type(scope) {
				Ok(generic) => generic,
				
				Err(ComuneError { 
					code: ComuneErrCode::RightShiftInGenericArgs(Some(ty), None), 
					.. 
				}) => {
					result.push(GenericArg::Type(ty));
					self.get_next()?;

					return Ok(result)
				},

				Err(err) => return Err(err),
			};

			result.push(GenericArg::Type(generic));

			if self.get_current()? == Token::Other(',') {
				self.get_next()?;
			} else {
				break;
			}
		}

		match self.get_current()? {
			Token::Operator(">") => {
				// consume closing angle bracket
				self.get_next()?;

				Ok(result)
			}

			Token::Operator(">>") => {
				self.err(ComuneErrCode::RightShiftInGenericArgs(None, Some(result)))
			}
			
			_ => {
				self.err(ComuneErrCode::UnexpectedToken)
			}
		}
	}

	fn parse_tuple_type(
		&self,
		scope: Option<&FnScope<'ctx>>,
	) -> ComuneResult<(TupleKind, Vec<Type>)> {
		let mut types = vec![];

		if self.get_current()? != Token::Operator("(") {
			return self.err(ComuneErrCode::UnexpectedToken);
		}

		let mut kind = None;

		if self.get_next()? == Token::Operator(")") {
			kind = Some(TupleKind::Empty);
		} else {
			loop {
				types.push(self.parse_type(scope)?);

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
		}

		self.get_next()?;

		match kind {
			Some(kind) => Ok((kind, types)),

			None => Ok((TupleKind::Newtype, types)),
		}
	}
}
