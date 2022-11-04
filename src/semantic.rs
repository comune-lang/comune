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
	parser::{AnalyzeResult, ParseResult},
};

use self::{
	ast::{ASTElem, ASTNode, TokenData},
	controlflow::ControlFlow,
	expression::{Atom, Expr, Operator},
	namespace::{Identifier, Name, Namespace, NamespaceASTElem, NamespaceItem},
	types::{FnDef, TypeParamList},
};

pub mod ast;
pub mod controlflow;
pub mod expression;
pub mod namespace;
pub mod types;

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

	variables: HashMap<Name, Type>,
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
					result = Some((
						id.clone(),
						todo!(), // Implement function types
					));
				}
			});
		}

		return result;
	}

	pub fn add_variable(&mut self, t: Type, n: Name) {
		self.variables.insert(n, t);
	}
}

pub fn validate_function(
	func: &FnDef,
	elem: &RefCell<NamespaceASTElem>,
	namespace: &RefCell<Namespace>,
	root: &RefCell<Namespace>,
) -> AnalyzeResult<()> {
	let mut scope;
	let ret;

	ret = func.ret.clone();
	scope = FnScope::new(namespace, root, ret.clone());

	for arg in &func.args {
		scope.add_variable(arg.0.clone(), arg.1.clone().unwrap())
	}

	if let NamespaceASTElem::Parsed(elem) = &mut *elem.borrow_mut() {
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
	params: &Vec<(Type, Option<Name>)>,
	scope: &FnScope,
	meta: TokenData,
) -> AnalyzeResult<Type> {
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
) -> AnalyzeResult<()> {
	for c in &namespace.borrow().children {
		match &c.1 .0 {
			// Validate child namespace
			NamespaceItem::Namespace(ns) => validate_namespace(ns, root_namespace)?,

			// Validate function
			NamespaceItem::Function(func, elem) => {
				validate_function(&func.read().unwrap(), elem, namespace, root_namespace)?
			}

			_ => {}
		}
	}

	for im in &namespace.borrow().impls {
		for item in im.1 {
			match &item.1 .0 {
				NamespaceItem::Function(func, elem) => {
					validate_function(&func.read().unwrap(), elem, namespace, root_namespace)?
				}

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
	generics: &TypeParamList,
) -> ParseResult<()> {
	match ty {
		Type::Pointer(pointee) => resolve_type(pointee, namespace, root, generics),

		Type::Reference(refee) => resolve_type(refee, namespace, root, generics),

		Type::Array(pointee, _size) => resolve_type(pointee, namespace, root, generics),

		Type::Unresolved(ref id) => {
			let id = id.clone();

			let mut result = None;

			if let Some(b) = Basic::get_basic_type(id.name()) {
				if !id.is_qualified() {
					result = Some(Type::Basic(b));
				}
			} else if !id.is_qualified() && generics.contains_key(id.name()) {
				// Generic type parameter
				result = Some(Type::TypeParam(id.name().clone()));
			} else {
				namespace.with_item(&id.clone(), &root.borrow(), |item, id| {
					if let NamespaceItem::Type(t) = &item.0 {
						result = Some(Type::TypeRef {
							def: Arc::downgrade(t),
							name: id.clone(),
							params: HashMap::new(),
						});
					}
				});
			}
			if let Some(result) = result {
				*ty = result;
				Ok(())
			} else {
				Err(CMNError::new(CMNErrorCode::UnresolvedTypename(
					id.to_string(),
				)))
			}
		}

		Type::TypeRef { .. } | Type::Basic(_) | Type::TypeParam(_) => Ok(()),
	}
}

pub fn resolve_type_def(
	ty: &mut TypeDef,
	attributes: &Vec<Attribute>,
	namespace: &Namespace,
	root: &RefCell<Namespace>,
	base_generics: &TypeParamList,
) -> ParseResult<()> {
	match ty {
		TypeDef::Algebraic(agg) => {
			let mut generics = base_generics.clone();
			generics.extend(agg.params.clone());

			for item in &mut agg.items {
				match &mut item.1 .0 {
					NamespaceItem::Variable(t, _) => resolve_type(t, &namespace, root, &generics)?,
					NamespaceItem::Type(t) => resolve_type_def(
						&mut t.write().unwrap(),
						&vec![],
						&namespace,
						root,
						&generics,
					)?,
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
					agg.layout = match &**layout_name.expect_scopeless()? {
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
) -> ParseResult<()> {
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
				NamespaceItem::Function(func, _) => {
					let FnDef {
						ret,
						args,
						generics,
					} = &mut *func.write().unwrap();

					resolve_type(ret, &namespace, root, &generics)?;

					for arg in args {
						resolve_type(&mut arg.0, &namespace, root, &generics)?;
					}
				}

				NamespaceItem::Namespace(_) => {}

				NamespaceItem::Type(t) => resolve_type_def(
					&mut *t.write().unwrap(),
					&child.1 .1,
					&namespace,
					root,
					&HashMap::new(),
				)?,

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
) -> ParseResult<()> {
	if let TypeDef::Algebraic(agg) = &*ty.as_ref().read().unwrap() {
		for member in agg.items.iter() {
			match &member.1 .0 {
				NamespaceItem::Variable(t, _) => {
					if let Type::TypeRef { def: ref_t, .. } = &t {
						// Check if
						if parent_types
							.iter()
							.find(|elem| Arc::ptr_eq(elem, &ref_t.upgrade().unwrap()))
							.is_some()
						{
							return Err(CMNError::new(CMNErrorCode::InfiniteSizeType));
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

pub fn check_namespace_cyclical_deps(namespace: &Namespace) -> ParseResult<()> {
	for item in &namespace.children {
		match &item.1 .0 {
			NamespaceItem::Type(ty) => check_cyclical_deps(&ty, &mut vec![])?,
			NamespaceItem::Namespace(ns) => check_namespace_cyclical_deps(&ns.as_ref().borrow())?,
			_ => {}
		}
	}
	Ok(())
}

pub fn register_impls(
	namespace: &RefCell<Namespace>,
	root: &RefCell<Namespace>,
) -> ParseResult<()> {
	let mut impls_remapped = HashMap::new();

	for im in &namespace.borrow().impls {
		// Impls can be defined with relative Identifiers, so we make them all fully-qualified members of the root namespace here

		namespace
			.borrow()
			.with_item(&im.0, &root.borrow(), |item, id| {
				if let NamespaceItem::Type(t_def) = &item.0 {
					if let TypeDef::Algebraic(_) = &mut *t_def.write().unwrap() {
						let mut this_impl = HashMap::new();

						for elem in im.1 {
							// Match impl item
							match &elem.1 .0 {
								NamespaceItem::Function(func_lock, ast) => {
									// Resolve function types
									let FnDef {
										ret,
										args,
										generics,
									} = &mut *func_lock.write().unwrap();

									resolve_type(ret, &namespace.borrow(), root, &generics)?;

									for arg in args {
										resolve_type(
											&mut arg.0,
											&namespace.borrow(),
											root,
											&generics,
										)?;
									}

									this_impl.insert(
										elem.0.clone(),
										(
											NamespaceItem::Function(func_lock.clone(), ast.clone()),
											elem.1 .1.clone(),
											None,
										),
									);
								}

								_ => todo!(),
							}
						}
						impls_remapped.insert(id.clone(), this_impl);
					}
				}
				Ok(())
			})
			.unwrap()?;
	}

	root.borrow_mut().impls = impls_remapped;

	Ok(())
}

impl ASTElem {
	// Recursively validate ASTNode types and check if blocks have matching return types
	pub fn validate(&self, scope: &mut FnScope, ret: &Type) -> AnalyzeResult<Option<Type>> {
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

				scope.add_variable(t.clone(), n.clone().into());

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
	) -> AnalyzeResult<Type> {
		// Validate Atom or sub-expressions
		match self {
			Expr::Atom(a, _) => a.validate(scope, goal_t, meta),

			Expr::Cons(op, elems, meta) => {
				match op {
					// Special cases for type-asymmetric operators
					Operator::MemberAccess => {
						let meta = meta.clone();
						self.validate_lvalue(scope, meta)
					}

					Operator::Subscr => {
						let idx_type = Type::Basic(Basic::SIZEINT { signed: false });

						let first_meta = elems[0].2;
						let first_t = elems
							.get_mut(0)
							.unwrap()
							.0
							.validate(scope, None, first_meta)?;
						let second_meta = elems[1].2;
						let second_t = elems.get_mut(1).unwrap().0.validate(
							scope,
							Some(&idx_type),
							second_meta,
						)?;

						if let Type::Array(ty, _) = &first_t {
							if second_t == idx_type {
								elems[0].1 = Some(first_t.clone());
								elems[1].1 = Some(second_t.clone());

								return Ok(*ty.clone());
							} else {
								return Err((
									CMNError::new(CMNErrorCode::InvalidSubscriptRHS {
										t: second_t,
									}),
									*meta,
								));
							}
						} else {
							return Err((
								CMNError::new(CMNErrorCode::InvalidSubscriptLHS { t: first_t }),
								*meta,
							));
						}
					}

					// General case for unary & binary expressions
					_ => {
						let first_meta = elems[0].2;
						let mut first_t = elems
							.get_mut(0)
							.unwrap()
							.0
							.validate(scope, None, first_meta)?;
						let mut second_t = None;

						elems[0].1 = Some(first_t.clone());

						if let Some(item) = elems.get_mut(1) {
							second_t = Some(item.0.validate(scope, None, item.2)?);

							if first_t != *second_t.as_ref().unwrap() {
								// Try to coerce one to the other

								if let Ok(try_coerce_rhs) =
									item.0.validate(scope, Some(&first_t), item.2)
								{
									if first_t == try_coerce_rhs {
										second_t = Some(try_coerce_rhs);
									}
								} else {
									let first = elems.get_mut(0).unwrap();
									if let Ok(try_coerce_lhs) =
										first.0.validate(scope, Some(&first_t), first.2)
									{
										if *second_t.as_ref().unwrap() == try_coerce_lhs {
											first_t = try_coerce_lhs;
										}
									} else {
										return Err((
											CMNError::new(CMNErrorCode::ExprTypeMismatch(
												first_t,
												second_t.unwrap(),
												op.clone(),
											)),
											*meta,
										));
									}
								}
							}

							elems[1].1 = second_t.clone();
						}

						// Handle operators that change the expression's type here
						match op {
							Operator::Ref => {
								match goal_t {
									// Default to creating a reference, unless explicitly asking for a pointer
									Some(Type::Pointer(_)) => Ok(first_t.ptr_type()),

									_ => Ok(first_t.ref_type()),
								}
							}

							Operator::Deref => match first_t {
								Type::Pointer(t) | Type::Reference(t) => Ok(*t.clone()),
								_ => {
									return Err((
										CMNError::new(CMNErrorCode::InvalidDeref(first_t)),
										*meta,
									))
								}
							},

							Operator::Eq
							| Operator::NotEq
							| Operator::Less
							| Operator::Greater
							| Operator::LessEq
							| Operator::GreaterEq => return Ok(Type::Basic(Basic::BOOL)),

							Operator::PostDec | Operator::PostInc => return Ok(first_t),

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

				Atom::FnCall { ret, .. } => {
					if let Some(ret) = ret {
						*ret == *target
					} else {
						false
					}
				}

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
	) -> AnalyzeResult<Type> {
		match self {
			Expr::Atom(a, _) => {
				a.validate(scope, None, meta)?;
				return a.get_lvalue_type(scope);
			}

			Expr::Cons(op, elems, _) => {
				match op {
					// Only these operators can result in lvalues
					Operator::Deref => {
						return match elems[0].0.validate(scope, None, meta).unwrap() {
							Type::Pointer(t) => {
								elems[0].1 = Some(Type::Pointer(t.clone()));
								Ok(*t)
							}

							Type::Reference(t) => {
								elems[0].1 = Some(Type::Reference(t.clone()));
								Ok(*t)
							}

							other => Err((CMNError::new(CMNErrorCode::InvalidDeref(other)), meta)),
						}
					}

					Operator::MemberAccess => {
						if let Type::TypeRef {
							def: r,
							name: t_id,
							params,
						} = elems[0].0.validate_lvalue(scope, meta).unwrap()
						{
							if let (lhs, [rhs, ..]) = elems.split_first_mut().unwrap() {
								match &mut *r.upgrade().unwrap().write().unwrap() {
									// Dot operator is on an algebraic type, so check if it's a member access or method call
									TypeDef::Algebraic(t) => match &mut rhs.0 {
										// Member access on algebraic type
										Expr::Atom(Atom::Identifier(id), _) => {
											if let Some((_, m)) =
												t.get_member(id.name(), Some(&params))
											{
												lhs.1 = Some(Type::TypeRef {
													def: r.clone(),
													name: t_id.clone(),
													params: params.clone(),
												});
												rhs.1 = Some(m.clone());
												return Ok(m.clone());
											}
										}

										// Method call on algebraic type
										Expr::Atom(Atom::FnCall { name, args, .. }, _) => {
											// jesse. we have to call METHods
											// TODO: Factor this out into a proper call resolution module
											if let Some((
												_,
												(NamespaceItem::Function(method, _), _, _),
											)) = scope
												.root_namespace
												.borrow()
												.impls
												.get(&t_id)
												.unwrap_or(&HashMap::new())
												.iter()
												.find(|meth| meth.0 == name.name())
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
															Type::TypeRef {
																def: r.clone(),
																name: t_id.clone(),
																params: HashMap::new(),
															},
														)),
													},
												);

												let method = method.read().unwrap();

												match validate_fn_call(
													&method.ret,
													&args,
													&method.args,
													scope,
													meta.clone(),
												) {
													Ok(res) => {
														// Method call OK
														lhs.1 = Some(Type::TypeRef {
															def: r.clone(),
															name: t_id.clone(),
															params: HashMap::new(),
														});
														rhs.1 = Some(method.ret.clone());

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

										_ => {}
									},
									_ => {}
								}
							}
						}
					}
					_ => {}
				}
			}
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
	) -> AnalyzeResult<Type> {
		match self {
			Atom::IntegerLit(_, t) => {
				if let Some(t) = t {
					Ok(Type::Basic(t.clone()))
				} else {
					if let Some(Type::Basic(_)) = goal_t {
						Ok(goal_t.unwrap().clone())
					} else {
						Ok(Type::Basic(Basic::INTEGRAL {
							signed: true,
							size_bytes: 4,
						}))
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
					Err((
						CMNError::new(CMNErrorCode::UndeclaredIdentifier(name.to_string())),
						meta,
					))
				}
			}

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
				scope
					.context
					.borrow()
					.with_item(name, &scope.root_namespace.borrow(), |item, _| {
						if let NamespaceItem::Function(func, _) = &item.0 {
							let func = func.read().unwrap();

							*ret = Some(validate_fn_call(
								&func.ret,
								args,
								&func.args,
								scope,
								meta.clone(),
							)?);

							Ok(ret.as_ref().unwrap().clone())
						} else {
							// Trying to call a non-function
							Err((
								CMNError::new(CMNErrorCode::NotCallable(name.to_string())),
								meta,
							))
						}
					})
					.ok_or_else(|| {
						(
							CMNError::new(CMNErrorCode::UndeclaredIdentifier(name.to_string())),
							meta,
						)
					})?
			}

			Atom::ArrayLit(_) => todo!(),

			Atom::AlgebraicLit(ty, elems) => {
				if let Type::TypeRef { def, params, .. } = ty {
					if let TypeDef::Algebraic(alg) = &*def.upgrade().unwrap().read().unwrap() {
						for elem in elems {
							let member_ty = if let Some((_, ty)) =
								alg.get_member(elem.0.as_ref().unwrap(), Some(&params))
							{
								ty
							} else {
								// Invalid member in strenum literal
								todo!()
							};

							let expr_ty = elem.1.get_expr().borrow_mut().validate(
								scope,
								Some(&member_ty),
								elem.2,
							)?;

							elem.1.type_info.borrow_mut().replace(expr_ty.clone());

							if !elem
								.1
								.get_expr()
								.borrow()
								.coercable_to(&expr_ty, &member_ty, scope)
							{
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
	) -> AnalyzeResult<()> {
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

			Type::Pointer(_) => Ok(()),

			_ => todo!(),
		}
	}

	pub fn get_lvalue_type<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> AnalyzeResult<Type> {
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
	pub fn validate<'ctx>(
		&self,
		scope: &'ctx FnScope<'ctx>,
		_meta: TokenData,
	) -> AnalyzeResult<()> {
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
