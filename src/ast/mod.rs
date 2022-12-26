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
	expression::{Atom, Expr, NodeData, Operator, OnceAtom},
	namespace::{Identifier, ItemRef, Name, Namespace, NamespaceASTElem, NamespaceItem},
	statement::Stmt,
	types::{AlgebraicDef, FnDef, TupleKind, TypeParamList, TypeRef}, pattern::Binding,
};

pub mod controlflow;
pub mod expression;
pub mod namespace;
pub mod pattern;
pub mod statement;
pub mod traits;
pub mod types;

// AST & SEMANTIC ANALYSIS
// This module contains structs and impls related to the AST, name resolution, and type validation.
// TODO: This module is pretty big, the semantic analysis code could probably be organized better

pub type TokenData = (usize, usize); // idx, len

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Attribute {
	pub name: String,
	pub args: Vec<Vec<Token>>,
}

pub fn get_attribute<'a>(attributes: &'a [Attribute], attr_name: &str) -> Option<&'a Attribute> {
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
			self.context.with_item(id, &self.scope, |item, id| {
				if let NamespaceItem::Function(fn_type, _) = &item.0 {
					result = Some((
						id.clone(),
						todo!(), // Implement function types
					));
				}
			});
		}

		result
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
		elem.validate(&mut scope)?;

		let Expr::Atom(Atom::Block { items, result }, _) = elem else { panic!() };

		// Turn result values into explicit return expressions
		if result.is_some() {
			let expr = *result.take().unwrap();
			let node_data = expr.get_node_data().clone();
			items.push(Stmt::Expr(Expr::Atom(
				Atom::CtrlFlow(Box::new(ControlFlow::Return { expr: Some(expr) })),
				node_data,
			)));
		}

		match items.last() {
			Some(Stmt::Decl(_, Some(expr), _) | Stmt::Expr(expr)) => {
				let expr_ty = expr.get_type();

				if !expr_ty.castable_to(&scope.fn_return_type) {
					return Err((
						CMNError::new(CMNErrorCode::ReturnTypeMismatch {
							expected: scope.fn_return_type,
							got: expr_ty.clone(),
						}),
						elem.get_node_data().tk,
					));
				}
			}

			_ => todo!(),
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

	for (i, arg) in args.iter_mut().enumerate() {
		// add parameter's type info to argument
		if let Some((param_ty, _)) = params.get(i) {
			arg.get_node_data_mut()
				.ty
				.replace(param_ty.get_concrete_type(type_args));
		}

		let arg_type = arg.validate(scope)?;

		if let Some((param_ty, _)) = params.get(i) {
			let concrete = param_ty.get_concrete_type(type_args);

			if !arg.coercable_to(&arg_type, &concrete, scope) {
				return Err((
					CMNError::new(CMNErrorCode::InvalidCoercion {
						from: arg_type,
						to: concrete,
					}),
					args[i].get_node_data().tk,
				));
			}

			if arg_type != concrete {
				arg.wrap_in_cast(concrete);
			}
		} else {
			// no parameter type for this argument (possible for varadiac functions)
			// so just set the type info to the provided argument's type
			arg.get_node_data_mut().ty.replace(arg_type.clone());

			// also if it's a float we promote it to a double because presumably
			// ken and dennis were high on crack for 30 years straight or smth
			// https://stackoverflow.com/questions/63144506/printf-doesnt-work-for-floats-in-llvm-ir
			if arg_type == Type::Basic(Basic::Float { size_bytes: 4 }) {
				arg.wrap_in_cast(Type::Basic(Basic::Float { size_bytes: 8 }));
			}
		}
	}

	// All good, return function's return type
	Ok(func.ret.get_concrete_type(type_args))
}

pub fn validate_namespace(namespace: &mut Namespace) -> AnalyzeResult<()> {
	for (id, child) in &namespace.children {
		if let NamespaceItem::Function(func, elem) = &child.0 {
			validate_function(id, &func.read().unwrap(), elem, namespace)?
		}
	}

	for im in &namespace.impls {
		for item in im.1 {
			match &item.1 .0 {
				NamespaceItem::Function(func, elem) => {
					validate_function(im.0, &func.read().unwrap(), elem, namespace)?
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

		Type::Tuple(_, types) => {
			for ty in types {
				resolve_type(ty, namespace, generics)?;
			}

			Ok(())
		}

		Type::TypeRef { .. } | Type::Basic(_) | Type::TypeParam(_) | Type::Never => Ok(()),
	}
}

pub fn resolve_algebraic_def(
	agg: &mut AlgebraicDef,
	attributes: &[Attribute],
	namespace: &Namespace,
	base_generics: &TypeParamList,
) -> ParseResult<()> {
	let mut generics = base_generics.clone();
	generics.extend(agg.params.clone());

	for (_, variant) in &mut agg.variants {
		resolve_algebraic_def(variant, attributes, namespace, base_generics)?;
	}

	for (_, ty, _) in &mut agg.members {
		resolve_type(ty, namespace, &generics)?;
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

	Ok(())
}

pub fn resolve_type_def(
	ty: &mut TypeDef,
	attributes: &[Attribute],
	namespace: &Namespace,
	base_generics: &TypeParamList,
) -> ParseResult<()> {
	match ty {
		TypeDef::Algebraic(agg) => resolve_algebraic_def(agg, attributes, namespace, base_generics),

		_ => todo!(),
	}
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

				resolve_type(ret, namespace, generics)?;

				for param in &mut params.params {
					resolve_type(&mut param.0, namespace, generics)?;
				}
			}

			NamespaceItem::Type(t) => {
				resolve_type_def(&mut t.write().unwrap(), &child.1 .1, namespace, &vec![])?
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
		for member in agg.members.iter() {
			if let Type::TypeRef(ItemRef::Resolved(TypeRef { def: ref_t, .. })) = &member.1 {
				if parent_types
					.iter()
					.any(|elem| Arc::ptr_eq(elem, &ref_t.upgrade().unwrap()))
				{
					return Err(CMNError::new(CMNErrorCode::InfiniteSizeType));
				}

				parent_types.push(ty.clone());
				check_cyclical_deps(&ref_t.upgrade().unwrap(), parent_types)?;
				parent_types.pop();
			}
		}
	}
	Ok(())
}

pub fn check_namespace_cyclical_deps(namespace: &Namespace) -> ParseResult<()> {
	for item in &namespace.children {
		if let NamespaceItem::Type(ty) = &item.1 .0 {
			check_cyclical_deps(ty, &mut vec![])?
		}
	}

	Ok(())
}

pub fn register_impls(namespace: &mut Namespace) -> ParseResult<()> {
	let mut impls_remapped = HashMap::new();

	for im in &namespace.impls {
		// Impls can be defined with relative Identifiers, so we make them all fully-qualified members of the root namespace here

		namespace
			.with_item(im.0, &Identifier::new(true), |item, id| {
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

									resolve_type(ret, namespace, type_params)?;

									for param in &mut params.params {
										resolve_type(&mut param.0, namespace, type_params)?;
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

impl Expr {
	pub fn create_cast(expr: Expr, to: Type, meta: NodeData) -> Expr {
		Expr::Atom(Atom::Cast(Box::new(expr), to), meta)
	}

	pub fn validate<'ctx>(&mut self, scope: &mut FnScope<'ctx>) -> AnalyzeResult<Type> {
		let result = match self {
			Expr::Atom(a, meta) => a.validate(scope, meta),

			Expr::Cons([lhs, rhs], op, meta) => {
				match op {
					// Special cases for type-asymmetric operators
					Operator::MemberAccess => {
						let lhs_ty = lhs.validate(scope)?;
						
						if !lhs.is_lvalue() {
							// If lhs is an rvalue, wrap it in an Atom::Once 
							// to prevent it being evaluated multiple times 
							lhs.wrap_in_once_atom();
						}
						Self::validate_member_access(&lhs_ty, lhs, rhs, scope, meta)
					}

					Operator::Subscr => {
						let idx_type = Type::Basic(Basic::PtrSizeInt { signed: false });

						let first_t = lhs.validate(scope)?;
						let second_t = rhs.validate(scope)?;

						if let Type::Array(ty, _) = &first_t {
							if second_t != idx_type {
								if rhs.coercable_to(&second_t, &idx_type, scope) {
									rhs.wrap_in_cast(idx_type);
								} else {
									return Err((
										CMNError::new(CMNErrorCode::InvalidSubscriptRHS {
											t: second_t,
										}),
										meta.tk,
									));
								}
							}

							Ok(*ty.clone())
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

						if first_t != second_t {
							// Try to coerce one to the other

							if lhs.coercable_to(&first_t, &second_t, scope) {
								lhs.wrap_in_cast(second_t.clone());
							} else if rhs.coercable_to(&second_t, &first_t, scope) {
								rhs.wrap_in_cast(first_t.clone());
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
							| Operator::GreaterEq => Ok(Type::Basic(Basic::Bool)),

							Operator::PostDec | Operator::PostInc => Ok(first_t),

							_ => Ok(second_t),
						}
					}
				}
			}

			Expr::Unary(expr, op, meta) => {
				let expr_ty = expr.validate(scope)?;

				match op {
					Operator::Ref => Ok(expr_ty.ptr_type()),

					Operator::Deref => match expr_ty {
						Type::Pointer(t) => Ok(*t),

						_ => {
							return Err((
								CMNError::new(CMNErrorCode::InvalidDeref(expr_ty)),
								meta.tk,
							))
						}
					},

					_ => Ok(expr_ty),
				}
			}
		}?;

		result.validate(scope)?;

		self.get_node_data_mut().ty.replace(result.clone());

		Ok(result)
	}

	// Check whether an Expr is coercable to a type
	pub fn coercable_to(&self, from: &Type, target: &Type, scope: &FnScope) -> bool {
		match target {
			Type::Tuple(TupleKind::Sum, types) => {
				let tuple_matches = types
					.iter()
					.filter(|ty| self.coercable_to(from, ty, scope))
					.count();

				match tuple_matches {
					0 => false,
					1 => true,
					_ => false, // TODO: Error reporting for ambiguous tuple conversion
				}
			}

			_ => match self {
				Expr::Atom(a, _) => match a {
					Atom::IntegerLit(_, t) => {
						if t.is_some() {
							*target == Type::Basic(t.unwrap())
						} else {
							target.is_integral()
						}
					}

					Atom::FloatLit(_, t) => {
						if t.is_some() {
							*target == Type::Basic(t.unwrap())
						} else {
							target.is_floating_point()
						}
					}

					Atom::BoolLit(_) => target.is_boolean(),

					Atom::CStringLit(_) => {
						if let Type::Pointer(other_p) = &target {
							if **other_p
								== Type::Basic(Basic::Integral {
									signed: false,
									size_bytes: 1,
								}) {
								return true;
							}
						}

						false
					}

					Atom::StringLit(_) => target == &Type::Basic(Basic::Str),

					Atom::Identifier(i) => scope.find_symbol(i).unwrap().1 == *target,

					Atom::FnCall { ret, .. } => {
						if let Some(ret) = ret {
							*ret == *target
						} else {
							false
						}
					}

					Atom::Cast(_, cast_t) => target == cast_t,
					Atom::AlgebraicLit(alg_ty, _) => target == alg_ty,
					Atom::ArrayLit(_) => todo!(),
					Atom::Block { .. } => todo!(),
					Atom::CtrlFlow(_) => todo!(),
					
					Atom::Once(once) => if let OnceAtom::Uneval(expr) = &*once.read().unwrap() {
						expr.coercable_to(from, target, scope)
					} else {
						false
					}
				},

				Expr::Cons(_, _, _) => from == target,
				Expr::Unary(_, _, _) => from == target,
			},
		}
	}

	pub fn validate_lvalue<'ctx>(&mut self, scope: &mut FnScope<'ctx>) -> AnalyzeResult<Type> {
		let result = match self {
			Expr::Atom(a, meta) => {
				a.validate(scope, meta)?;
				a.get_lvalue_type(scope, &meta.tk)?
			}

			Expr::Unary(e, Operator::Deref, meta) => match e.validate(scope).unwrap() {
				Type::Pointer(t) => *t,

				other => return Err((CMNError::new(CMNErrorCode::InvalidDeref(other)), meta.tk)),
			},

			Expr::Cons(_, Operator::Subscr, _) => self.validate(scope)?,

			Expr::Cons([lhs, rhs], Operator::MemberAccess, meta) => {
				let lhs_ty = lhs.validate_lvalue(scope)?;
				Self::validate_member_access(&lhs_ty, lhs, rhs, scope, meta)?
			}
			_ => panic!(),
		};

		result.validate(scope)?;

		self.get_node_data_mut().ty = Some(result.clone());

		Ok(result)
	}

	fn is_lvalue(&self) -> bool {
		match self {
			Expr::Atom(atom, _) => matches!(atom, Atom::Identifier(_) | Atom::Once(_)),

			Expr::Cons([_, _], op, _) => matches!(op, Operator::MemberAccess | Operator::Subscr),

			Expr::Unary(_, op, _) => matches!(op, Operator::Deref),
		}
	}

	fn validate_member_access(
		lhs_ty: &Type,
		lhs: &Expr,
		rhs: &mut Expr,
		scope: &mut FnScope,
		meta: &NodeData,
	) -> AnalyzeResult<Type> {
		let Type::TypeRef(ItemRef::Resolved(lhs_ref)) = lhs_ty else {
			return Err((CMNError::new(CMNErrorCode::InvalidSubscriptLHS { t: lhs_ty.clone() }), meta.tk));
		};

		match &*lhs_ref.def.upgrade().unwrap().read().unwrap() {
			// Dot operator is on an algebraic type, so check if it's a member access or method call
			TypeDef::Algebraic(t) => match rhs {
				// Member access on algebraic type
				Expr::Atom(Atom::Identifier(id), _) => {
					if let Some((_, m)) = t.get_member(id.name(), Some(&lhs_ref.args)) {
						//lhs.get_node_data_mut().ty = Some(Type::TypeRef(ItemRef::Resolved(lhs_ref)));

						rhs.get_node_data_mut().ty = Some(m.clone());

						Ok(m)
					} else {
						panic!()
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
					if let Some((_, (NamespaceItem::Function(method, _), _, _))) = scope
						.context
						.impls
						.get(&lhs_ref.name)
						.unwrap_or(&HashMap::new())
						.iter()
						.find(|meth| meth.0 == name.name())
					{
						// Insert `this` into the arg list
						// TODO: For method calls on literals, this will probably call
						// the literal's constructor twice. Maybe promote it to a local?
						args.insert(0, lhs.clone());

						let method = method.read().unwrap();

						match validate_fn_call(&method, args, type_args, scope, meta.tk) {
							Ok(res) => {
								// Method call OK
								let method_name = name.path.pop().unwrap();
								*name = lhs_ref.name.clone();
								name.path.push(method_name);

								rhs.get_node_data_mut().ty = Some(method.ret.clone());

								Ok(res)
							}

							Err(mut err) => {
								match err.0.code {
									// If the parameter count doesn't match, adjust the message for the implicit `self` param
									CMNErrorCode::ParamCountMismatch { expected, got } => {
										err.0.code = CMNErrorCode::ParamCountMismatch {
											expected: expected - 1,
											got: got - 1,
										};
										Err(err)
									}

									_ => Err(err),
								}
							}
						}
					} else {
						panic!()
					}
				}

				_ => panic!(),
			},
			_ => panic!(),
		}
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
					Ok(Type::Basic(*t))
				} else if let Some(Type::Basic(_)) = meta.ty {
					Ok(meta.ty.as_ref().unwrap().clone())
				} else {
					Ok(Type::Basic(Basic::Integral {
						signed: true,
						size_bytes: 4,
					}))
				}
			}

			Atom::FloatLit(_, t) => {
				if let Some(t) = t {
					Ok(Type::Basic(*t))
				} else if let Some(Type::Basic(b)) = meta.ty {
					*t = Some(b);
					Ok(meta.ty.as_ref().unwrap().clone())
				} else {
					*t = Some(Basic::Float { size_bytes: 4 });
					Ok(Type::Basic(t.unwrap()))
				}
			}

			Atom::BoolLit(_) => Ok(Type::Basic(Basic::Bool)),
			Atom::StringLit(_) => Ok(Type::Basic(Basic::Str)),

			Atom::CStringLit(_) => Ok(Type::Pointer(Box::new(Type::Basic(Basic::Integral {
				signed: false,
				size_bytes: 1,
			})))),

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

							*ret = Some(validate_fn_call(&func, args, type_args, scope, meta.tk)?);

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
								alg.get_member(elem.0.as_ref().unwrap(), Some(args))
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
										to: member_ty,
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
				let mut subscope = FnScope::from_parent(scope);

				for item in items {
					item.validate(&mut subscope)?;
				}

				if let Some(result) = result {
					result.validate(&mut subscope)
				} else {
					Ok(Type::Basic(Basic::Void))
				}
			}

			Atom::CtrlFlow(ctrl) => match &mut **ctrl {
				ControlFlow::If {
					cond,
					body,
					else_body,
				} => {
					let bool_ty = Type::Basic(Basic::Bool);
					let mut subscope = FnScope::from_parent(scope);

					let cond_ty = cond.validate(&mut subscope)?;

					if cond_ty != bool_ty {
						if cond_ty.castable_to(&bool_ty) {
							cond.wrap_in_cast(bool_ty);
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
					let bool_ty = Type::Basic(Basic::Bool);
					let mut subscope = FnScope::from_parent(scope);

					let cond_ty = cond.validate(&mut subscope)?;

					if cond_ty != bool_ty {
						if cond_ty.castable_to(&bool_ty) {
							cond.wrap_in_cast(bool_ty);
						} else {
							todo!()
						}
					}

					body.validate(&mut subscope)
				}

				ControlFlow::For {
					init,
					cond,
					iter,
					body,
				} => {
					let bool_ty = Type::Basic(Basic::Bool);
					let mut subscope = FnScope::from_parent(scope);

					if let Some(init) = init {
						init.validate(&mut subscope)?;
					}

					if let Some(cond) = cond {
						let cond_ty = cond.validate(&mut subscope)?;

						if cond_ty != bool_ty {
							if cond_ty.castable_to(&bool_ty) {
								cond.wrap_in_cast(bool_ty);
							} else {
								todo!()
							}
						}
					}

					if let Some(iter) = iter {
						iter.validate(&mut subscope)?;
					}

					body.validate(&mut subscope)
				}

				ControlFlow::Return { expr } => {
					if let Some(expr) = expr {
						let expr_ty = expr.validate(scope)?;

						if expr_ty == scope.fn_return_type {
							Ok(Type::Never)
						} else if expr.coercable_to(&expr_ty, &scope.fn_return_type, scope) {
							expr.wrap_in_cast(scope.fn_return_type.clone());
							Ok(Type::Never)
						} else {
							Err((
								CMNError::new(CMNErrorCode::ReturnTypeMismatch {
									expected: scope.fn_return_type.clone(),
									got: expr_ty,
								}),
								meta.tk,
							))
						}
					} else if scope.fn_return_type == Type::Basic(Basic::Void) {
						Ok(Type::Never)
					} else {
						Err((
							CMNError::new(CMNErrorCode::ReturnTypeMismatch {
								expected: scope.fn_return_type.clone(),
								got: Type::Basic(Basic::Void),
							}),
							meta.tk,
						))
					}
				}

				ControlFlow::Break => todo!(),
				ControlFlow::Continue => todo!(),

				ControlFlow::Match {
					scrutinee,
					branches,
				} => {
					if branches.is_empty() {
						return Ok(Type::Basic(Basic::Void));
					}

					let mut last_branch_type = None;
					let scrutinee_type = scrutinee.validate(scope)?;

					for branch in branches {
						let mut subscope = FnScope::from_parent(scope);

						for binding in branch.0.get_bindings() {
							if let Binding { name: Some(name), ty, .. } = binding {
								subscope.add_variable(ty.clone(), name.clone());
							}
						}

						let branch_ty = branch.1.validate(&mut subscope)?;

						if let Some(last_branch_type) = last_branch_type {
							if branch_ty != last_branch_type {
								todo!()
							}
						}

						last_branch_type = Some(branch_ty);

						if !branch.0.get_type().is_subtype_of(&scrutinee_type) {
							todo!()
						}
					}

					Ok(last_branch_type.unwrap()) // TODO: This'll panic with an empty match expression
				}
			},

			Atom::Once(once) => if let OnceAtom::Uneval(expr) = &mut *once.write().unwrap() {
				expr.validate(scope)
			} else {
				panic!() // i dunno
			},
		}
	}


	pub fn get_lvalue_type<'ctx>(
		&self,
		scope: &'ctx FnScope<'ctx>,
		meta: &TokenData,
	) -> AnalyzeResult<Type> {
		match self {
			Atom::Identifier(id) => match scope.find_symbol(id) {
				Some(t) => Ok(t.1),
				None => Err((
					CMNError::new(CMNErrorCode::UndeclaredIdentifier(id.to_string())),
					*meta,
				)),
			},
			_ => Err((CMNError::new(CMNErrorCode::InvalidLValue), *meta)),
		}
	}
}

impl Type {
	pub fn validate<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> AnalyzeResult<()> {
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

			Type::Tuple(_, types) => {
				for ty in types {
					ty.validate(scope)?;
				}
			}

			_ => {}
		}

		Ok(())
	}
}
