use std::{
	cell::RefCell,
	collections::HashMap,
	sync::{Arc, RwLock},
};

use types::{Basic, Type, TypeDef};

use crate::{
	constexpr::{ConstEval, ConstExpr},
	errors::{CMNError, CMNErrorCode},
	lexer::Token,
	parser::{AnalyzeResult, ParseResult},
};

use self::{
	controlflow::ControlFlow,
	expression::{Atom, Expr, NodeData, Operator},
	namespace::{Identifier, ItemRef, Name, Namespace, NamespaceASTElem, NamespaceItem},
	types::{FnDef, TypeParamList, TypeRef},
};

pub mod controlflow;
pub mod expression;
pub mod namespace;
pub mod statement;
pub mod traits;
pub mod types;

// SEMANTIC ANALYSIS
// This module contains structs and impls related to AST checking, name resolution, and type validation.

pub type TokenData = (usize, usize); // idx, len

#[derive(PartialEq, Clone, Debug)]
pub struct Attribute {
	pub name: String,
	pub args: Vec<Vec<Token>>,
}

pub fn get_attribute<'a>(attributes: &'a Vec<Attribute>, attr_name: &str) -> Option<&'a Attribute> {
	attributes.iter().find(|a| a.name.as_str() == attr_name)
}

pub struct FnScope<'ctx> {
	context: &'ctx Namespace,
	scope: Identifier,
	parent: Option<&'ctx FnScope<'ctx>>,
	fn_return_type: Type,
	variables: HashMap<Name, Type>,
}

impl<'ctx> FnScope<'ctx> {
	pub fn from_parent(parent: &'ctx FnScope) -> Self {
		FnScope {
			context: parent.context,
			scope: parent.scope.clone(),
			parent: Some(parent),
			fn_return_type: parent.fn_return_type.clone(),
			variables: HashMap::new(),
		}
	}

	pub fn new(context: &'ctx Namespace, scope: Identifier, return_type: Type) -> Self {
		FnScope {
			context,
			scope,
			parent: None,
			fn_return_type: return_type,
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
			self.context.with_item(&id, &self.scope, |item, id| {
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
	name: &Identifier,
	func: &FnDef,
	elem: &RefCell<NamespaceASTElem>,
	namespace: &Namespace,
) -> AnalyzeResult<()> {
	let mut ctx_scope = name.clone();
	ctx_scope.path.pop();

	let mut scope = FnScope::new(namespace, ctx_scope, func.ret.clone());

	for param in &func.params.params {
		scope.add_variable(param.0.clone(), param.1.clone().unwrap())
	}

	if let NamespaceASTElem::Parsed(elem) = &mut *elem.borrow_mut() {
		// Validate function block & get return type, make sure it matches the signature
		let void = Type::Basic(Basic::VOID);
		let expr_ty = elem.validate(&mut scope)?;
		/*
		if ret != void {
			// No returns in non-void function
			return Err((
				CMNError::new(CMNErrorCode::ReturnTypeMismatch {
					expected: ret.clone(),
					got: void,
				}),
				elem.get_node_data().tk,
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
		*/
		if !expr_ty.castable_to(&scope.fn_return_type) {
			return Err((
				CMNError::new(CMNErrorCode::ReturnTypeMismatch {
					expected: scope.fn_return_type.clone(),
					got: expr_ty,
				}),
				elem.get_node_data().tk,
			));
		}
	}
	Ok(())
}

pub fn validate_fn_call(
	func: &FnDef,
	args: &mut Vec<Expr>,
	type_args: &Vec<(Arc<str>, Type)>,
	scope: &mut FnScope,
	meta: TokenData,
) -> AnalyzeResult<Type> {
	let params = &func.params.params;

	// check for param count mismatch
	if args.len() < params.len() || (args.len() > params.len() && !func.params.variadic) {
		return Err((
			CMNError::new(CMNErrorCode::ParamCountMismatch {
				expected: params.len(),
				got: args.len(),
			}),
			meta,
		));
	}

	for i in 0..args.len() {
		// add parameter's type info to argument
		if let Some((param_ty, _)) = params.get(i) {
			args[i]
				.get_node_data_mut()
				.ty
				.replace(param_ty.get_concrete_type(type_args));
		}

		let arg_type = args[i].validate(scope)?;

		if let Some((param_ty, _)) = params.get(i) {
			let concrete = param_ty.get_concrete_type(type_args);

			if !args[i].coercable_to(&arg_type, &concrete, scope) {
				return Err((
					CMNError::new(CMNErrorCode::InvalidCoercion {
						from: arg_type,
						to: concrete.clone(),
					}),
					args[i].get_node_data().tk,
				));
			}

			if arg_type != concrete {
				args[i].wrap_in_cast(concrete);
			}
		} else {
			// no parameter type for this argument (possible for varadiac functions)
			// so just set the type info to the provided argument's type
			args[i].get_node_data_mut().ty.replace(arg_type);
		}
	}

	// All good, return function's return type
	Ok(func.ret.get_concrete_type(type_args))
}

pub fn validate_namespace(namespace: &mut Namespace) -> AnalyzeResult<()> {
	for (id, child) in &namespace.children {
		match &child.0 {
			// Validate function
			NamespaceItem::Function(func, elem) => {
				validate_function(id, &func.read().unwrap(), elem, namespace)?
			}

			_ => {}
		}
	}

	for im in &namespace.impls {
		for item in im.1 {
			match &item.1 .0 {
				NamespaceItem::Function(func, elem) => {
					validate_function(&im.0, &func.read().unwrap(), elem, namespace)?
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
	generics: &TypeParamList,
) -> ParseResult<()> {
	match ty {
		Type::Pointer(pointee) => resolve_type(pointee, namespace, generics),

		Type::Reference(refee) => resolve_type(refee, namespace, generics),

		Type::Array(pointee, _size) => resolve_type(pointee, namespace, generics),

		Type::TypeRef(ItemRef::Unresolved { name: id, scope }) => {
			let mut result = None;
			let generic_pos = generics.iter().position(|(name, _)| name == id.name());

			if let Some(b) = Basic::get_basic_type(id.name()) {
				if !id.is_qualified() {
					result = Some(Type::Basic(b));
				}
			} else if !id.is_qualified() && generic_pos.is_some() {
				// Generic type parameter
				result = Some(Type::TypeParam(generic_pos.unwrap()));
			} else {
				namespace.with_item(id, scope, |item, id| {
					if let NamespaceItem::Type(t) = &item.0 {
						result = Some(Type::TypeRef(ItemRef::Resolved(TypeRef {
							def: Arc::downgrade(t),
							name: id.clone(),
							args: vec![],
						})));
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

		Type::TypeRef { .. } | Type::Basic(_) | Type::TypeParam(_) | Type::Never => Ok(()),
	}
}

pub fn resolve_type_def(
	ty: &mut TypeDef,
	attributes: &Vec<Attribute>,
	namespace: &Namespace,
	base_generics: &TypeParamList,
) -> ParseResult<()> {
	match ty {
		TypeDef::Algebraic(agg) => {
			let mut generics = base_generics.clone();
			generics.extend(agg.params.clone());

			for item in &mut agg.items {
				match &mut item.1 .0 {
					NamespaceItem::Variable(t, _) => resolve_type(t, &namespace, &generics)?,
					NamespaceItem::Type(t) => {
						resolve_type_def(&mut t.write().unwrap(), &vec![], &namespace, &generics)?
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

pub fn resolve_namespace_types(namespace: &Namespace) -> ParseResult<()> {
	// Resolve types

	for child in &namespace.children {
		match &child.1 .0 {
			NamespaceItem::Function(func, _) => {
				let FnDef {
					ret,
					params,
					type_params: generics,
				} = &mut *func.write().unwrap();

				resolve_type(ret, &namespace, &generics)?;

				for param in &mut params.params {
					resolve_type(&mut param.0, &namespace, &generics)?;
				}
			}

			NamespaceItem::Type(t) => {
				resolve_type_def(&mut *t.write().unwrap(), &child.1 .1, &namespace, &vec![])?
			}

			NamespaceItem::Alias(_) => {}

			_ => todo!(),
		};
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
					if let Type::TypeRef(ItemRef::Resolved(TypeRef { def: ref_t, .. })) = &t {
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
			_ => {}
		}
	}
	Ok(())
}

pub fn register_impls(namespace: &mut Namespace) -> ParseResult<()> {
	let mut impls_remapped = HashMap::new();

	for im in &namespace.impls {
		// Impls can be defined with relative Identifiers, so we make them all fully-qualified members of the root namespace here

		namespace
			.with_item(&im.0, &Identifier::new(true), |item, id| {
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
										params,
										type_params,
									} = &mut *func_lock.write().unwrap();

									resolve_type(ret, namespace, &type_params)?;

									for param in &mut params.params {
										resolve_type(&mut param.0, namespace, &type_params)?;
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

	namespace.impls = impls_remapped;

	Ok(())
}

/*
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
}*/

impl Expr {
	pub fn create_cast(expr: Expr, from: Option<Type>, to: Type, meta: NodeData) -> Expr {
		Expr::Atom(Atom::Cast(Box::new(expr), to.clone()), meta)
	}

	pub fn validate<'ctx>(
		&mut self,
		scope: &mut FnScope<'ctx>,
	) -> AnalyzeResult<Type> {
		let result = match self {
			Expr::Atom(a, meta) => {
				let ty = a.validate(scope, meta)?;
				meta.ty = Some(ty.clone());
				Ok(ty)
			}

			Expr::Cons([lhs, rhs], op, meta) => {
				match op {
					// Special cases for type-asymmetric operators
					Operator::MemberAccess => {
						let tk = meta.tk;
						self.validate_lvalue(scope, tk)
					}

					Operator::Subscr => {
						let idx_type = Type::Basic(Basic::SIZEINT { signed: false });

						let first_t = lhs.validate(scope)?;
						let second_t = rhs.validate(scope)?;

						if let Type::Array(ty, _) = &first_t {
							if second_t == idx_type {
								lhs.get_node_data_mut().ty = Some(first_t.clone());
								rhs.get_node_data_mut().ty = Some(second_t);

								return Ok(*ty.clone());
							} else {
								return Err((
									CMNError::new(CMNErrorCode::InvalidSubscriptRHS {
										t: second_t,
									}),
									meta.tk,
								));
							}
						} else {
							return Err((
								CMNError::new(CMNErrorCode::InvalidSubscriptLHS { t: first_t }),
								meta.tk,
							));
						}
					}

					// General case for binary expressions
					_ => {
						let first_t = lhs.validate(scope)?;
						let second_t = rhs.validate(scope)?;

						lhs.get_node_data_mut().ty = Some(first_t.clone());
						rhs.get_node_data_mut().ty = Some(second_t.clone());

						if first_t != second_t {
							// Try to coerce one to the other

							if lhs.coercable_to(&first_t, &second_t, scope) {
								todo!()
							} else if rhs.coercable_to(&second_t, &first_t, scope) {
								todo!()
							} else {
								return Err((
									CMNError::new(CMNErrorCode::ExprTypeMismatch(
										first_t,
										second_t,
										op.clone(),
									)),
									meta.tk,
								));
							}
						}

						// Handle operators that change the expression's type here
						match op {
							Operator::Eq
							| Operator::NotEq
							| Operator::Less
							| Operator::Greater
							| Operator::LessEq
							| Operator::GreaterEq => return Ok(Type::Basic(Basic::BOOL)),

							Operator::PostDec | Operator::PostInc => return Ok(first_t),

							_ => Ok(second_t),
						}
					}
				}
			}

			Expr::Unary(expr, op, meta) => {
				let expr_ty = expr.validate(scope)?;

				match op {
					Operator::Ref => {
						match meta.ty {
							// Default to creating a reference, unless explicitly asking for a pointer
							Some(Type::Pointer(_)) => Ok(expr_ty.ptr_type()),

							_ => Ok(expr_ty.ref_type()),
						}
					}

					Operator::Deref => match expr_ty {
						Type::Pointer(t) | Type::Reference(t) => Ok(*t.clone()),

						_ => {
							return Err((
								CMNError::new(CMNErrorCode::InvalidDeref(expr_ty)),
								meta.tk,
							))
						}
					}

					_ => Ok(expr_ty),
				}
			},
		}?;

		if self.get_node_data().ty.is_none() {
			self.get_node_data_mut().ty.replace(result.clone());
		}

		Ok(result)
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
				Atom::Block { .. } => todo!(),
				Atom::CtrlFlow(_) => todo!(),
			},

			Expr::Cons(_, _, _) => from == target,
			Expr::Unary(_, _, _) => from == target,
		}
	}

	pub fn validate_lvalue<'ctx>(
		&mut self,
		scope: &mut FnScope<'ctx>,
		meta: TokenData,
	) -> AnalyzeResult<Type> {
		match self {
			Expr::Atom(a, meta) => {
				a.validate(scope, meta)?;
				return a.get_lvalue_type(scope);
			}

			Expr::Unary(e, op, meta) => match op {
				Operator::Deref => {
					return match e.validate(scope).unwrap() {
						Type::Pointer(t) => {
							e.get_node_data_mut().ty = Some(Type::Pointer(t.clone()));
							Ok(*t)
						}

						Type::Reference(t) => {
							e.get_node_data_mut().ty = Some(Type::Reference(t.clone()));
							Ok(*t)
						}

						other => Err((CMNError::new(CMNErrorCode::InvalidDeref(other)), meta.tk)),
					}
				}

				_ => panic!(),
			},

			Expr::Cons([lhs, rhs], op, _) => {
				match op {
					// Only these operators can result in lvalues
					Operator::MemberAccess => {
						let Type::TypeRef(ItemRef::Resolved(lhs_ref)) = lhs.validate_lvalue(scope, meta)? else {
							todo!("error reporting")
						};

						match &mut *lhs_ref.def.upgrade().unwrap().write().unwrap() {
							// Dot operator is on an algebraic type, so check if it's a member access or method call
							TypeDef::Algebraic(t) => match &mut **rhs {
								// Member access on algebraic type
								Expr::Atom(Atom::Identifier(id), _) => {
									if let Some((_, m)) =
										t.get_member(id.name(), Some(&lhs_ref.args))
									{
										lhs.get_node_data_mut().ty =
											Some(Type::TypeRef(ItemRef::Resolved(lhs_ref.clone())));

										rhs.get_node_data_mut().ty = Some(m.clone());
										return Ok(m.clone());
									}
								}

								// Method call on algebraic type
								Expr::Atom(
									Atom::FnCall {
										name,
										args,
										type_args,
										..
									},
									_,
								) => {
									// jesse. we have to call METHods
									// TODO: Factor this out into a proper call resolution module
									if let Some((_, (NamespaceItem::Function(method, _), _, _))) =
										scope
											.context
											.impls
											.get(&lhs_ref.name)
											.unwrap_or(&HashMap::new())
											.iter()
											.find(|meth| meth.0 == name.name())
									{
										// Insert `this` into the arg list
										args.insert(0, *lhs.clone());

										let method = method.read().unwrap();

										match validate_fn_call(
											&method,
											args,
											type_args,
											scope,
											meta.clone(),
										) {
											Ok(res) => {
												// Method call OK
												lhs.get_node_data_mut().ty = Some(Type::TypeRef(
													ItemRef::Resolved(lhs_ref.clone()),
												));

												let method_name = name.path.pop().unwrap();
												*name = lhs_ref.name.clone();
												name.path.push(method_name);

												rhs.get_node_data_mut().ty =
													Some(method.ret.clone());

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
														err.0.code =
															CMNErrorCode::ParamCountMismatch {
																expected: expected - 1,
																got: got - 1,
															};
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
		scope: &mut FnScope<'ctx>,
		meta: &NodeData,
	) -> AnalyzeResult<Type> {
		match self {
			Atom::IntegerLit(_, t) => {
				if let Some(t) = t {
					Ok(Type::Basic(t.clone()))
				} else {
					if let Some(Type::Basic(_)) = meta.ty {
						Ok(meta.ty.as_ref().unwrap().clone())
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
					if let Some(Type::Basic(b)) = meta.ty {
						*t = Some(b.clone());
						Ok(meta.ty.as_ref().unwrap().clone())
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
						meta.tk,
					))
				}
			}

			Atom::Cast(expr, to) => {
				let expr_t = expr.validate(scope)?;

				if expr_t.castable_to(to) {
					if let Expr::Atom(a, meta) = &mut **expr {
						a.check_cast(&expr_t, to, scope, &meta.tk)?;
					}

					expr.get_node_data_mut().ty.replace(to.clone());
					Ok(to.clone())
				} else {
					Err((
						CMNError::new(CMNErrorCode::InvalidCast {
							from: expr_t,
							to: to.clone(),
						}),
						expr.get_node_data().tk,
					))
				}
			}

			Atom::FnCall {
				name,
				args,
				type_args,
				ret,
			} => {
				scope
					.context
					.with_item(name, &scope.scope.clone(), |item, _| {
						if let NamespaceItem::Function(func, _) = &item.0 {
							let func = func.read().unwrap();

							*ret = Some(validate_fn_call(
								&func,
								args,
								type_args,
								scope,
								meta.tk.clone(),
							)?);

							Ok(ret.as_ref().unwrap().clone())
						} else {
							// Trying to call a non-function
							Err((
								CMNError::new(CMNErrorCode::NotCallable(name.to_string())),
								meta.tk,
							))
						}
					})
					.ok_or_else(|| {
						(
							CMNError::new(CMNErrorCode::UndeclaredIdentifier(name.to_string())),
							meta.tk,
						)
					})?
			}

			Atom::ArrayLit(_) => todo!(),

			Atom::AlgebraicLit(ty, elems) => {
				if let Type::TypeRef(ItemRef::Resolved(TypeRef { def, args, .. })) = ty {
					if let TypeDef::Algebraic(alg) = &*def.upgrade().unwrap().read().unwrap() {
						for elem in elems {
							let member_ty = if let Some((_, ty)) =
								alg.get_member(elem.0.as_ref().unwrap(), Some(&args))
							{
								ty
							} else {
								// Invalid member in strenum literal
								todo!()
							};

							elem.1.get_node_data_mut().ty.replace(member_ty.clone());
							let expr_ty = elem.1.validate(scope)?;

							if !elem.1.coercable_to(&expr_ty, &member_ty, scope) {
								return Err((
									CMNError::new(CMNErrorCode::AssignTypeMismatch {
										expr: expr_ty,
										to: member_ty.clone(),
									}),
									elem.1.get_node_data().tk,
								));
							}
						}

						return Ok(ty.clone());
					}
				}

				todo!()
			}

			Atom::Block { items, result } => {
				for item in items {
					item.validate(scope)?;
				}
				
				if let Some(result) = result {
					result.validate(scope)
				} else {
					Ok(Type::Basic(Basic::VOID))
				}
			}
			
			Atom::CtrlFlow(ctrl) => {
				match &mut **ctrl {
					ControlFlow::If { cond, body, else_body } => {
						let bool_ty = Type::Basic(Basic::BOOL);
						let mut subscope = FnScope::from_parent(scope);

						let cond_ty = cond.validate(&mut subscope)?;
						
						if cond_ty != bool_ty {
							if cond_ty.castable_to(&bool_ty) {
								cond.wrap_in_cast(bool_ty.clone());
							} else {
								todo!()
							}
						}
						
						let body_ty = body.validate(&mut subscope)?;

						if let Some(else_body) = else_body {
							let else_ty = else_body.validate(&mut subscope)?;

							if body_ty == else_ty {
								Ok(body_ty)
							} else {
								todo!()
							}
						} else {
							Ok(body_ty)
						}

					}

					ControlFlow::While { cond, body } => {
						let bool_ty = Type::Basic(Basic::BOOL);
						let mut subscope = FnScope::from_parent(scope);

						let cond_ty = cond.validate(&mut subscope)?;
						
						if cond_ty != bool_ty {
							if cond_ty.castable_to(&bool_ty) {
								cond.wrap_in_cast(bool_ty.clone());
							} else {
								todo!()
							}
						}

						body.validate(&mut subscope)
					}

					ControlFlow::For { init, cond, iter, body } => todo!(),
					ControlFlow::Return { expr } => {
						if let Some(expr) = expr {
							let expr_ty = expr.validate(scope)?;
							
							if expr_ty == scope.fn_return_type {
								Ok(Type::Never)
							} else if expr.coercable_to(&expr_ty, &scope.fn_return_type, scope) {
								expr.wrap_in_cast(scope.fn_return_type.clone());
								Ok(Type::Never)
							} else {
								Err((CMNError::new(CMNErrorCode::ReturnTypeMismatch { expected: scope.fn_return_type.clone(), got: expr_ty }), meta.tk))
							}
						} else {
							if scope.fn_return_type == Type::Basic(Basic::VOID) {
								Ok(Type::Never)
							} else {
								Err((CMNError::new(CMNErrorCode::ReturnTypeMismatch { expected: scope.fn_return_type.clone(), got: Type::Basic(Basic::VOID) }), meta.tk))
							}
						}
					}
					ControlFlow::Break => todo!(),
					ControlFlow::Continue => todo!(),
				}
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
