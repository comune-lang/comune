use std::{
	cell::RefCell,
	collections::HashMap,
	sync::{Arc, RwLock},
};

use types::{Basic, Type, TypeDef, Typed};

use crate::{
	constexpr::{ConstEval, ConstExpr},
	errors::{CMNError, CMNErrorCode},
	lexer::Token,
	parser::{ASTResult, ParseResult},
};

use self::{
	ast::{ASTElem, ASTNode, TokenData},
	controlflow::ControlFlow,
	expression::{Atom, Expr, Operator},
	namespace::{Identifier, Namespace, NamespaceASTElem, NamespaceItem},
};

pub mod ast;
pub mod controlflow;
pub mod expression;
pub mod namespace;
pub mod types;
pub mod value;

// SEMANTIC ANALYSIS
// This module contains structs and impls related to AST checking, name resolution, and type validation.

#[derive(PartialEq, Clone, Debug)]
pub struct Attribute {
	pub name: String,
	pub args: Vec<Vec<Token>>,
}

pub fn get_attribute<'a>(attributes: &'a Vec<Attribute>, attr_name: &str) -> Option<&'a Attribute> {
	attributes.iter().find(|a| a.name.as_str() == attr_name)
}

pub struct FnScope<'ctx> {
	context: &'ctx RefCell<Namespace>,
	parent: Option<&'ctx FnScope<'ctx>>,
	fn_return_type: Type,
	root_namespace: &'ctx RefCell<Namespace>,

	variables: HashMap<String, Type>,
}

impl<'ctx> FnScope<'ctx> {
	pub fn from_parent(parent: &'ctx FnScope) -> Self {
		FnScope {
			context: parent.context,
			parent: Some(parent),
			fn_return_type: parent.fn_return_type.clone(),
			root_namespace: parent.root_namespace,
			variables: HashMap::new(),
		}
	}

	pub fn new(
		context: &'ctx RefCell<Namespace>,
		root_namespace: &'ctx RefCell<Namespace>,
		return_type: Type,
	) -> Self {
		FnScope {
			context,
			parent: None,
			fn_return_type: return_type,
			root_namespace,
			variables: HashMap::new(),
		}
	}

	pub fn find_symbol(&self, id: &Identifier) -> Option<(Identifier, Type)> {
		let mut result = None;

		if !id.is_qualified() {
			// Unqualified name, perform scope-level lookup first
			let local_lookup;

			if self.variables.contains_key(id.name()) {
				local_lookup = Some((id.clone(), self.variables.get(id.name()).cloned().unwrap()));
			} else if let Some(parent) = self.parent {
				local_lookup = parent.find_symbol(id);
			} else {
				local_lookup = None;
			}

			if local_lookup.is_some() {
				
				result = local_lookup;
			}
		}

		if result.is_none() {
			// Look for it in the namespace tree
			let namespace = self.context.borrow();
			let root = self.root_namespace.borrow();

			namespace.with_item(&id, &root, |item, id| {
				if let NamespaceItem::Function(fn_type, _) = &item.0 {
					result = Some((id.clone(), Type::TypeRef(Arc::downgrade(fn_type), id.clone())));
				}
			});
		}

		return result;
	}

	pub fn add_variable(&mut self, t: Type, n: String) {
		self.variables.insert(n, t);
	}
}

pub fn validate_function(
	sym_type: &TypeDef,
	sym_elem: &RefCell<NamespaceASTElem>,
	namespace: &RefCell<Namespace>,
	root: &RefCell<Namespace>,
) -> ASTResult<()> {
	let mut scope;
	let ret;

	if let TypeDef::Function(fn_ret, args) = sym_type {
		ret = fn_ret.clone();
		scope = FnScope::new(namespace, root, ret.clone());

		for arg in args.iter() {
			scope.add_variable(arg.0.clone(), arg.1.clone().unwrap())
		}
	} else {
		panic!()
	}

	if let NamespaceASTElem::Parsed(elem) = &mut *sym_elem.borrow_mut() {
		// Validate function block & get return type, make sure it matches the signature
		let void = Type::Basic(Basic::VOID);
		let ret_type = elem.validate(&mut scope, &ret)?;

		if ret_type.is_none() {
			if ret != void {
				// No returns in non-void function
				return Err((
					CMNError::new(CMNErrorCode::ReturnTypeMismatch {
						expected: ret.clone(),
						got: void,
					}),
					elem.token_data,
				));
			} else {
				// Add implicit return statement to void fn
				if let ASTNode::Block(elems) = &mut elem.node {
					elems.push(ASTElem {
						node: ASTNode::ControlFlow(Box::new(ControlFlow::Return { expr: None })),
						token_data: (0, 0),
						type_info: RefCell::new(None),
					});
				}
			}
		} else if ret_type.is_some() && !ret_type.as_ref().unwrap().castable_to(&ret) {
			return Err((
				CMNError::new(CMNErrorCode::ReturnTypeMismatch {
					expected: ret.clone(),
					got: ret_type.unwrap(),
				}),
				elem.token_data,
			));
		}
	}
	Ok(())
}

pub fn validate_fn_call(
	ret: &Type,
	args: &Vec<ASTElem>,
	params: &Vec<(Type, Option<String>)>,
	scope: &FnScope,
	meta: TokenData,
) -> ASTResult<Type> {
	if args.len() == params.len() {
		for i in 0..args.len() {
			args[i].type_info.replace(Some(params[i].0.clone()));
			let arg_type = args[i]
				.get_expr()
				.borrow_mut()
				.validate(scope, None, meta)?;

			if !args[i]
				.get_expr()
				.borrow()
				.coercable_to(&arg_type, &params[i].0, scope)
			{
				return Err((
					CMNError::new(CMNErrorCode::InvalidCoercion {
						from: arg_type,
						to: params[i].0.clone(),
					}),
					args[i].token_data,
				));
			}

			if arg_type != params[i].0 {
				args[i].wrap_expr_in_cast(Some(arg_type), params[i].0.clone());
			}
		}
		// All good, return function's return type
		Ok(ret.clone())
	} else {
		Err((
			CMNError::new(CMNErrorCode::ParamCountMismatch {
				expected: params.len(),
				got: args.len(),
			}),
			meta,
		))
	}
}

pub fn validate_namespace(
	namespace: &RefCell<Namespace>,
	root_namespace: &RefCell<Namespace>,
) -> ASTResult<()> {
	for c in &namespace.borrow().children {
		match &c.1 .0 {
			// Validate child namespace
			NamespaceItem::Namespace(ns) => validate_namespace(ns, root_namespace)?,

			// Validate function
			NamespaceItem::Function(sym_type, sym_elem) => validate_function(
				&sym_type.read().unwrap(),
				sym_elem,
				namespace,
				root_namespace,
			)?,

			_ => {}
		}
	}

	for im in &namespace.borrow().impls {
		for item in im.1 {
			match &item.1.0 {
				NamespaceItem::Function(sym_type, sym_elem) => validate_function(
					&sym_type.read().unwrap(),
					sym_elem,
					namespace,
					root_namespace,
				)?,

				_ => panic!(),
			}
		}
	}

	Ok(())
}

pub fn resolve_type(
	ty: &mut Type,
	namespace: &Namespace,
	root: &RefCell<Namespace>,
) -> ParseResult<()> {
	match ty {
		Type::Pointer(ref mut pointee) => resolve_type(pointee, namespace, root),

		Type::Array(ref mut pointee, _size) => resolve_type(pointee, namespace, root),

		Type::Unresolved(ref id) => {
			let mut found = false;
			let id = id.clone();

			if let Some(b) = Basic::get_basic_type(id.name()) {
				if !id.is_qualified() {
					*ty = Type::Basic(b);
					found = true;
				}
			} else {
				namespace.with_item(&id.clone(), &root.borrow(), |item, id| {
					if let NamespaceItem::Type(t) = &item.0 {
						*ty = Type::TypeRef(Arc::downgrade(t), id.clone());
						found = true;
					}
				});
			}

			if found {
				Ok(())
			} else {
				Err(CMNError::new(CMNErrorCode::UnresolvedTypename(
					id.to_string(),
				)))
			}
		}

		Type::TypeRef(..) | Type::Basic(_) => Ok(()),
	}
}

pub fn resolve_type_def(
	ty: &mut TypeDef,
	attributes: &Vec<Attribute>,
	namespace: &Namespace,
	root: &RefCell<Namespace>,
) -> ParseResult<()> {
	match ty {
		TypeDef::Algebraic(ref mut agg) => {
			for item in &mut agg.items {
				match &mut item.1 .0 {
					NamespaceItem::Variable(t, _) => resolve_type(t, &namespace, root).unwrap(),
					NamespaceItem::Type(t) => {
						resolve_type_def(&mut t.write().unwrap(), &vec![], &namespace, root)
							.unwrap()
					}
					_ => (),
				}
			}

			if let Some(layout) = get_attribute(attributes, "layout") {
				if layout.args.len() != 1 {
					return Err(CMNError::new(CMNErrorCode::ParamCountMismatch {
						expected: 1,
						got: layout.args.len(),
					}));
				}
				if layout.args[0].len() != 1 {
					return Err(CMNError::new(CMNErrorCode::ParamCountMismatch {
						expected: 1,
						got: layout.args[0].len(),
					}));
				}

				if let Token::Identifier(layout_name) = &layout.args[0][0] {
					agg.layout = match layout_name.expect_scopeless().unwrap() {
						"declared" => types::DataLayout::Declared,
						"optimized" => types::DataLayout::Optimized,
						"packed" => types::DataLayout::Packed,
						_ => return Err(CMNError::new(CMNErrorCode::UnexpectedToken)),
					}
				}
			}
		}

		_ => todo!(),
	}

	Ok(())
}

pub fn resolve_namespace_types(
	namespace: &RefCell<Namespace>,
	root: &RefCell<Namespace>,
) -> ASTResult<()> {
	for child in &namespace.borrow().children {
		if let NamespaceItem::Namespace(ref ns) = child.1 .0 {
			resolve_namespace_types(ns, root)?;
		}
	}

	// Resolve types
	{
		let namespace = namespace.borrow();

		for child in &namespace.children {
			match &child.1 .0 {
				NamespaceItem::Function(ty, _) => {
					if let TypeDef::Function(ret, args) = &mut *ty.write().unwrap() {
						resolve_type(ret, &namespace, root).unwrap();

						for arg in args {
							resolve_type(&mut arg.0, &namespace, root).unwrap();
						}
					}
				}

				NamespaceItem::Namespace(_) => {}

				NamespaceItem::Type(t) => {
					resolve_type_def(&mut *t.write().unwrap(), &child.1 .1, &namespace, root)
						.unwrap()
				}

				NamespaceItem::Alias(_) => {}

				_ => todo!(),
			};
		}
	}
	Ok(())
}

pub fn check_cyclical_deps(
	ty: &Arc<RwLock<TypeDef>>,
	parent_types: &mut Vec<Arc<RwLock<TypeDef>>>,
) -> ASTResult<()> {
	if let TypeDef::Algebraic(agg) = &*ty.as_ref().read().unwrap() {
		for member in agg.items.iter() {
			match &member.1 .0 {
				NamespaceItem::Variable(t, _) => {
					if let Type::TypeRef(ref_t, _) = &t {
						// Check if
						if parent_types
							.iter()
							.find(|elem| Arc::ptr_eq(elem, &ref_t.upgrade().unwrap()))
							.is_some()
						{
							return Err((CMNError::new(CMNErrorCode::InfiniteSizeType), (0, 0)));
						}

						parent_types.push(ty.clone());
						check_cyclical_deps(&ref_t.upgrade().unwrap(), parent_types)?;
						parent_types.pop();
					}
				}

				NamespaceItem::Type(t) => {
					parent_types.push(ty.clone());
					check_cyclical_deps(t, parent_types)?;
					parent_types.pop();
				}

				_ => {}
			}
		}
	}
	Ok(())
}

pub fn check_namespace_cyclical_deps(namespace: &Namespace) -> ASTResult<()> {
	for item in &namespace.children {
		match &item.1 .0 {
			NamespaceItem::Type(ty) => check_cyclical_deps(&ty, &mut vec![])?,
			NamespaceItem::Namespace(ns) => check_namespace_cyclical_deps(&ns.as_ref().borrow())?,
			_ => {}
		}
	}
	Ok(())
}

pub fn register_impls(namespace: &RefCell<Namespace>, root: &RefCell<Namespace>) -> ASTResult<()> {
	let mut impls_remapped = HashMap::new();

	for im in &namespace.borrow().impls {
		// Impls can be defined with relative Identifiers, so we make them all fully-qualified members of the root namespace here

		namespace
			.borrow()
			.with_item(&im.0, &root.borrow(), |item, id| {
				if let NamespaceItem::Type(t_def) = &item.0 {
					if let TypeDef::Algebraic(_alg) = &mut *t_def.write().unwrap() {
						let mut this_impl = HashMap::new();

						for elem in im.1 {
							// Match impl item
							match &elem.1.0 {
								NamespaceItem::Function(func, ast) => {
								// Resolve function types
									if let TypeDef::Function(ret, args) = &mut *func.write().unwrap() {
										resolve_type(ret, &namespace.borrow(), root).unwrap();

										for arg in args {
											resolve_type(&mut arg.0, &namespace.borrow(), root).unwrap();
										}
									}

									this_impl.insert(
										elem.0.clone(),
										(NamespaceItem::Function(func.clone(), ast.clone()), elem.1.1.clone(), None)
									);
								}

								_ => todo!()
							}
						}
						impls_remapped.insert(id.clone(), this_impl);
					}
				}
			}).unwrap();
	}

	root.borrow_mut().impls = impls_remapped;

	Ok(())
}

impl ASTElem {
	// Recursively validate ASTNode types and check if blocks have matching return types
	pub fn validate(&self, scope: &mut FnScope, ret: &Type) -> ASTResult<Option<Type>> {
		let result = match &self.node {
			ASTNode::Block(elems) => {
				let mut subscope = FnScope::from_parent(scope);
				let mut last_ret = None;

				for elem in elems {
					let t = elem.validate(&mut subscope, ret)?;

					if let Some(t) = t {
						// Only compare against return type for control flow nodes
						if let ASTNode::ControlFlow(_) = elem.node {
							if t != *ret {
								return Err((
									CMNError::new(CMNErrorCode::ReturnTypeMismatch {
										got: t,
										expected: ret.clone(),
									}),
									elem.token_data,
								));
							}
							last_ret = Some(t);
						}
					}
				}
				Ok(last_ret)
			}

			ASTNode::Expression(e) => Ok(Some(e.borrow_mut().validate(
				scope,
				None,
				self.token_data,
			)?)),

			ASTNode::Declaration(t, n, e) => {
				t.validate(&scope, self.token_data)?;

				if let Some(expr) = e {
					expr.type_info.replace(Some(t.clone()));

					let expr_type = expr.get_type(scope)?;

					if expr_type != *t {
						if expr.get_expr().borrow().coercable_to(&expr_type, t, scope) {
							expr.wrap_expr_in_cast(Some(expr_type), t.clone());
						} else {
							return Err((
								CMNError::new(CMNErrorCode::AssignTypeMismatch {
									expr: expr_type,
									to: t.clone(),
								}),
								self.token_data,
							));
						}
					}
				}

				scope.add_variable(t.clone(), n.to_string());

				Ok(None)
			}

			ASTNode::ControlFlow(ctrl) => match ctrl.as_ref() {
				ControlFlow::If {
					cond,
					body,
					else_body,
				} => {
					cond.type_info.replace(Some(Type::Basic(Basic::BOOL)));
					let cond_type = cond.get_type(scope)?;
					let bool_t = Type::Basic(Basic::BOOL);

					if cond_type != bool_t {
						if cond_type.castable_to(&bool_t) {
							cond.wrap_expr_in_cast(Some(cond_type), bool_t);
						} else {
							return Err((
								CMNError::new(CMNErrorCode::InvalidCast {
									from: cond_type,
									to: bool_t,
								}),
								self.token_data,
							));
						}
					}

					let t = body.validate(scope, ret)?;

					if let Some(else_body) = else_body {
						else_body.validate(scope, ret)?;
					}

					Ok(t)
				}

				ControlFlow::While { cond, body } => {
					cond.type_info.replace(Some(Type::Basic(Basic::BOOL)));
					let cond_type = cond.get_type(scope)?;
					let bool_t = Type::Basic(Basic::BOOL);

					if cond_type != bool_t {
						if cond_type.castable_to(&bool_t) {
							cond.wrap_expr_in_cast(Some(cond_type), bool_t);
						} else {
							return Err((
								CMNError::new(CMNErrorCode::InvalidCast {
									from: cond_type,
									to: bool_t,
								}),
								self.token_data,
							));
						}
					}

					let t = body.validate(scope, ret)?;
					Ok(t)
				}

				ControlFlow::For {
					cond,
					body,
					init,
					iter,
				} => {
					let mut subscope = FnScope::from_parent(&scope);

					if let Some(init) = init {
						init.validate(&mut subscope, ret)?;
					}

					// Check if condition is coercable to bool
					if let Some(cond) = cond {
						let bool_t = Type::Basic(Basic::BOOL);

						cond.type_info.replace(Some(bool_t.clone()));
						let cond_type = cond.get_type(&mut subscope)?;

						if cond_type != bool_t {
							if cond_type.castable_to(&bool_t) {
								cond.wrap_expr_in_cast(Some(cond_type), bool_t);
							} else {
								return Err((
									CMNError::new(CMNErrorCode::InvalidCast {
										from: cond_type,
										to: bool_t,
									}),
									self.token_data,
								));
							}
						}
					}

					if let Some(iter) = iter {
						iter.validate(&mut subscope, ret)?;
					}

					let t = body.validate(&mut subscope, ret)?;
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
							if t == *ret {
								Ok(Some(t))
							} else if expr.get_expr().borrow().coercable_to(&t, ret, scope) {
								expr.wrap_expr_in_cast(Some(t), ret.clone());
								Ok(Some(ret.clone()))
							} else {
								Err((
									CMNError::new(CMNErrorCode::ReturnTypeMismatch {
										expected: ret.clone(),
										got: t,
									}),
									self.token_data,
								))
							}
						} else {
							Ok(None)
						}
					} else {
						Ok(Some(Type::Basic(Basic::VOID))) // Return with no expression is of type void
					}
				}

				_ => Ok(None),
			},
		};

		match result {
			Ok(ref r) => self.type_info.replace(r.clone()),
			Err(e) => return Err(e),
		};
		result
	}
}

impl Expr {
	pub fn create_cast(expr: Expr, from: Option<Type>, to: Type, meta: TokenData) -> Expr {
		Expr::Atom(
			Atom::Cast(
				Box::new(ASTElem {
					node: ASTNode::Expression(RefCell::new(expr)),
					type_info: RefCell::new(from),
					token_data: meta,
				}),
				to.clone(),
			),
			meta,
		)
	}

	pub fn validate<'ctx>(
		&mut self,
		scope: &'ctx FnScope<'ctx>,
		goal_t: Option<&Type>,
		meta: TokenData,
	) -> ASTResult<Type> {
		// Validate Atom or sub-expressions
		match self {
			Expr::Atom(a, _) => a.validate(scope, goal_t, meta),

			Expr::Cons(op, elems, meta) => {
				match op {
					// Special cases for member access and scope resolution
					Operator::MemberAccess => {
						let meta = meta.clone();
						self.validate_lvalue(scope, meta)
					}

					// General case for unary & binary expressions
					_ => {
						let first = elems.get_mut(0).unwrap();
						let first_t = first.0.validate(scope, None, first.2)?;
						let mut second_t = None;

						elems[0].1 = Some(first_t.clone());

						if let Some(item) = elems.get_mut(1) {
							second_t = Some(item.0.validate(scope, None, item.2)?);

							if first_t != *second_t.as_ref().unwrap() {
								return Err((
									CMNError::new(CMNErrorCode::ExprTypeMismatch(
										first_t,
										second_t.unwrap(),
										op.clone(),
									)),
									*meta,
								));
							}
							elems[1].1 = second_t.clone();
						}

						// Handle operators that change the expression's type here
						match op {
							Operator::Ref => Ok(first_t.ptr_type()),

							Operator::Deref => match first_t {
								Type::Pointer(t) => Ok(*t.clone()),
								_ => return Err((CMNError::new(CMNErrorCode::NonPtrDeref), *meta)),
							},

							Operator::Eq
							| Operator::NotEq
							| Operator::Less
							| Operator::Greater
							| Operator::LessEq
							| Operator::GreaterEq => return Ok(Type::Basic(Basic::BOOL)),

							_ => Ok(second_t.unwrap()),
						}
					}
				}
			}
		}
	}

	// Check whether an Expr is coercable to a type
	pub fn coercable_to(&self, from: &Type, target: &Type, scope: &FnScope) -> bool {
		match self {
			Expr::Atom(a, _) => match a {
				Atom::IntegerLit(_, t) | Atom::FloatLit(_, t) => {
					if t.is_some() {
						*target == Type::Basic(t.unwrap())
					} else {
						target.is_numeric()
					}
				}

				Atom::BoolLit(_) => target.is_boolean(),

				Atom::StringLit(_) => {
					if let Type::Pointer(other_p) = &target {
						if let Type::Basic(other_b) = **other_p {
							if let Basic::CHAR = other_b {
								return true;
							}
						}
					}

					false
				}

				Atom::Identifier(i) => scope.find_symbol(i).unwrap().1 == *target,

				Atom::FnCall { name, .. } => match scope.find_symbol(name).unwrap() {
					(_, Type::TypeRef(r, _)) => {
						if let TypeDef::Function(ret, _) =
							&*r.upgrade().unwrap().as_ref().read().unwrap()
						{
							*ret == *target
						} else {
							false
						}
					}

					_ => panic!(),
				},

				Atom::Cast(_, cast_t) => *target == *cast_t,
				Atom::AlgebraicLit(_, _) => todo!(),
				Atom::ArrayLit(_) => todo!(),
			},

			Expr::Cons(_, _, _) => from == target,
		}
	}

	pub fn validate_lvalue<'ctx>(
		&mut self,
		scope: &'ctx FnScope<'ctx>,
		meta: TokenData,
	) -> ASTResult<Type> {
		match self {
			Expr::Atom(a, _) => {
				a.validate(scope, None, meta)?;
				return a.get_lvalue_type(scope);
			}

			Expr::Cons(op, elems, _) => match op {
				// Only these operators can result in lvalues
				Operator::Deref => {
					return match elems[0].0.validate(scope, None, meta).unwrap() {
						Type::Pointer(t) => {
							elems[0].1 = Some(Type::Pointer(t.clone()));
							Ok(*t)
						}
						_ => Err((CMNError::new(CMNErrorCode::NonPtrDeref), meta)),
					}
				}

				Operator::MemberAccess => {
					if let Type::TypeRef(r, t_id) = elems[0].0.validate_lvalue(scope, meta).unwrap() {
						if let (lhs, [rhs, ..]) = elems.split_first_mut().unwrap() {
							match &mut *r.upgrade().unwrap().write().unwrap() {
								// Dot operator is on an algebraic type, so check if it's a member access or method call
								TypeDef::Algebraic(t) => match &mut rhs.0 {
									// Member access on algebraic type
									Expr::Atom(Atom::Identifier(ref mut id), _) => {
										if let Some((_, m)) = t.get_member(id.name()) {
											lhs.1 = Some(Type::TypeRef(r.clone(), t_id.clone()));
											rhs.1 = Some(m.clone());
											return Ok(m.clone());
										}
									}

									// Method call on algebraic type
									Expr::Atom(Atom::FnCall { name, args, .. }, _) => {
										// jesse. we have to call METHods

										if let Some((_, (NamespaceItem::Function(method, _), _, _))) = scope
											.root_namespace
											.borrow()
											.impls
											.get(&t_id)
											.unwrap_or(&HashMap::new())
											.iter()
											.find(|meth| meth.0 == name.name())
										{
											if let TypeDef::Function(ret, params) = &*method.read().unwrap()
											{
												// Insert `this` into the arg list
												args.insert(
													0,
													ASTElem {
														node: ASTNode::Expression(RefCell::new(
															lhs.0.clone(),
														)),
														token_data: (0, 0),
														type_info: RefCell::new(Some(
															Type::TypeRef(r.clone(), t_id.clone()),
														)),
													},
												);

												match validate_fn_call(
													ret,
													&args,
													params,
													scope,
													meta.clone(),
												) {
													Ok(res) => {
														// Method call OK
														lhs.1 = Some(Type::TypeRef(
															r.clone(),
															t_id.clone(),
														));
														rhs.1 = Some(ret.clone());

														let method_name = name.path.pop().unwrap();
														*name = t_id.clone();
														name.path.push(method_name);
														
														return Ok(res);
													}

													Err(e) => {
														match e.0.code {
															// If the parameter count doesn't match, adjust the message for the implicit `self` param
															CMNErrorCode::ParamCountMismatch {
																expected,
																got,
															} => {
																let mut err = e.clone();
																err.0.code = CMNErrorCode::ParamCountMismatch { expected: expected - 1, got: got - 1 };
																return Err(err);
															}

															_ => return Err(e),
														}
													}
												}
											}
										}
									}

									_ => {}
								},
								_ => {}
							}
						}
					}
				}
				_ => {}
			},
		};
		return Err((CMNError::new(CMNErrorCode::InvalidLValue), meta));
	}
}

impl Atom {
	pub fn validate<'ctx>(
		&mut self,
		scope: &'ctx FnScope<'ctx>,
		goal_t: Option<&Type>,
		meta: TokenData,
	) -> ASTResult<Type> {
		match self {
			Atom::IntegerLit(_, t) => {
				if let Some(t) = t {
					Ok(Type::Basic(t.clone()))
				} else {
					if let Some(Type::Basic(b)) = goal_t {
						*t = Some(b.clone());
						Ok(goal_t.unwrap().clone())
					} else {
						*t = Some(Basic::INTEGRAL {
							signed: true,
							size_bytes: 4,
						});
						Ok(Type::Basic(t.unwrap().clone()))
					}
				}
			}

			Atom::FloatLit(_, t) => {
				if let Some(t) = t {
					Ok(Type::Basic(t.clone()))
				} else {
					if let Some(Type::Basic(b)) = goal_t {
						*t = Some(b.clone());
						Ok(goal_t.unwrap().clone())
					} else {
						*t = Some(Basic::FLOAT { size_bytes: 4 });
						Ok(Type::Basic(t.unwrap().clone()))
					}
				}
			}

			Atom::BoolLit(_) => Ok(Type::Basic(Basic::BOOL)),
			Atom::StringLit(_) => Ok(Type::Basic(Basic::STR)),

			Atom::Identifier(name) => {
				if let Some((id, ty)) = scope.find_symbol(name) {
					// Replace name with fully-qualified ID
					*name = id;
					Ok(ty)
				} else {
					Err((CMNError::new(CMNErrorCode::UndeclaredIdentifier(name.to_string())), meta))
				}
			},

			Atom::Cast(a, t) => {
				if let ASTNode::Expression(expr) = &a.node {
					let a_t = expr.borrow_mut().validate(scope, None, meta)?;

					if a_t.castable_to(t) {
						if let Expr::Atom(a, _) = &mut *expr.borrow_mut() {
							a.check_cast(&a_t, t, scope, &meta)?;
						}

						a.type_info.replace(Some(t.clone()));
						Ok(t.clone())
					} else {
						Err((
							CMNError::new(CMNErrorCode::InvalidCast {
								from: a_t,
								to: t.clone(),
							}),
							meta,
						))
					}
				} else {
					panic!();
				}
			}

			Atom::FnCall { name, args, ret } => {
				if let Some((full_id, Type::TypeRef(t, _))) = scope.find_symbol(name) {
					if let TypeDef::Function(t_ret, params) =
						&*t.upgrade().unwrap().as_ref().read().unwrap()
					{
						// Identifier is a function, check parameter types
						*ret = Some(validate_fn_call(t_ret, args, params, scope, meta.clone())?);
						*name = full_id;

						Ok(ret.as_ref().unwrap().clone())
					} else {
						Err((
							CMNError::new(CMNErrorCode::NotCallable(name.to_string())),
							meta,
						)) // Trying to call a non-function
					}
				} else {
					Err((
						CMNError::new(CMNErrorCode::UndeclaredIdentifier(name.to_string())),
						meta,
					))
					// Couldn't find symbol!
				}
			}

			Atom::ArrayLit(_) => todo!(),

			Atom::AlgebraicLit(ty, elems) => {
				if let Type::TypeRef(alg, _) = ty {
					if let TypeDef::Algebraic(alg) = &*alg.upgrade().unwrap().read().unwrap() {
						for elem in elems {
							let member_ty =
								if let Some((_, ty)) = alg.get_member(elem.0.as_ref().unwrap()) {
									ty
								} else {
									// Invalid member in strenum literal
									todo!()
								};

							let expr_ty =
								elem.1.get_expr().borrow_mut().validate(scope, Some(member_ty), elem.2)?;
							
							elem.1.type_info.borrow_mut().replace(expr_ty.clone());

							if !elem.1.get_expr().borrow().coercable_to(&expr_ty, member_ty, scope) {
								return Err((
									CMNError::new(CMNErrorCode::AssignTypeMismatch {
										expr: expr_ty,
										to: member_ty.clone(),
									}),
									elem.2,
								));
							}
						}

						return Ok(ty.clone());
					}
				}

				todo!()
			}
		}
	}

	// Check if we should issue any warnings or errors when casting
	pub fn check_cast(
		&mut self,
		from: &Type,
		to: &Type,
		_scope: &FnScope,
		_meta: &TokenData,
	) -> ASTResult<()> {
		match from {
			Type::Basic(b) => match b {
				Basic::STR => {
					match to {
						Type::Pointer(to_ptr) => {
							if let Type::Basic(Basic::CHAR) = **to_ptr {
								if let Atom::StringLit(s) = self {
									if s.chars().last() != Some('\0') {
										s.push('\0');
										todo!();
										// TODO: Pass down Parser ref through functions?
										//lexer::log_msg_at(meta.0, meta.1, CMNMessage::Warning(CMNWarning::CharPtrNoNull));
									}
								}
							}
						}

						_ => {}
					}
					Ok(())
				}

				_ => Ok(()),
			},

			_ => todo!(),
		}
	}

	pub fn get_lvalue_type<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> ASTResult<Type> {
		match self {
			Atom::Identifier(id) => match scope.find_symbol(id) {
				Some(t) => return Ok(t.1),
				None => Err((
					CMNError::new(CMNErrorCode::UndeclaredIdentifier(id.to_string())),
					(0, 0),
				)),
			},
			_ => Err((CMNError::new(CMNErrorCode::InvalidLValue), (0, 0))),
		}
	}
}

impl Type {
	pub fn validate<'ctx>(&self, scope: &'ctx FnScope<'ctx>, _meta: TokenData) -> ASTResult<()> {
		match self {
			Type::Array(_, n) => {
				// Old fashioned way to make life easier with the RefCell
				let mut idx = 0;
				let len = n.read().unwrap().len();

				while idx < len {
					let mut result = None;

					if let ConstExpr::Expr(e) = &n.read().unwrap()[idx] {
						result = Some(ConstExpr::Result(e.eval_const(scope)?));
					}

					if let Some(result) = result {
						n.write().unwrap()[idx] = result;
					}

					idx += 1;
				}
			}

			_ => {}
		}

		Ok(())
	}
}
