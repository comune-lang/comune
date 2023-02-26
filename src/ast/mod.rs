use std::{
	cmp::Ordering,
	collections::HashMap,
	sync::{Arc, RwLock},
};

use types::{Basic, Type, TypeDef};

use crate::{
	constexpr::{ConstEval, ConstExpr, ConstValue},
	errors::{ComuneErrCode, ComuneError},
	lexer::{SrcSpan, Token},
	parser::ComuneResult,
};

use self::{
	controlflow::ControlFlow,
	expression::{Atom, Expr, FnRef, NodeData, OnceAtom, Operator},
	module::{
		Identifier, ItemRef, ModuleASTElem, ModuleImpl, ModuleInterface, ModuleItemInterface, Name,
	},
	pattern::Binding,
	statement::Stmt,
	traits::{TraitInterface, TraitRef},
	types::{AlgebraicDef, BindingProps, FnPrototype, TupleKind, GenericParamList, TypeRef, TypeDefKind},
};

pub mod controlflow;
pub mod expression;
pub mod module;
pub mod pattern;
pub mod statement;
pub mod traits;
pub mod types;

// AST & SEMANTIC ANALYSIS
// This module contains structs and impls related to the AST, name resolution, and type validation.
// TODO: This module is pretty big, the semantic analysis code could probably be organized better

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct Attribute {
	pub name: String,
	pub args: Vec<Vec<Token>>,
}

pub fn get_attribute<'a>(attributes: &'a [Attribute], attr_name: &str) -> Option<&'a Attribute> {
	attributes.iter().find(|a| a.name.as_str() == attr_name)
}

pub struct FnScope<'ctx> {
	context: &'ctx ModuleInterface,
	scope: Identifier,
	parent: Option<&'ctx FnScope<'ctx>>,
	fn_return_type: Type,
	variables: HashMap<Name, (Type, BindingProps)>,
	is_inside_loop: bool,
}

impl<'ctx> FnScope<'ctx> {
	pub fn from_parent(parent: &'ctx FnScope, is_loop_block: bool) -> Self {
		FnScope {
			context: parent.context,
			scope: parent.scope.clone(),
			parent: Some(parent),
			fn_return_type: parent.fn_return_type.clone(),
			variables: HashMap::new(),
			is_inside_loop: is_loop_block | parent.is_inside_loop
		}
	}

	pub fn new(context: &'ctx ModuleInterface, scope: Identifier, return_type: Type) -> Self {
		FnScope {
			context,
			scope,
			parent: None,
			fn_return_type: return_type,
			variables: HashMap::new(),
			is_inside_loop: false,
		}
	}

	pub fn find_symbol(
		&self,
		id: &Identifier,
		search_namespace: bool,
	) -> Option<(Identifier, Type)> {
		let mut result = None;

		if !id.is_qualified() {
			// Unqualified name, perform scope-level lookup first
			let local_lookup;

			if self.variables.contains_key(id.name()) {
				local_lookup = Some((
					id.clone(),
					self.variables.get(id.name()).cloned().unwrap().0,
				));
			} else if let Some(parent) = self.parent {
				local_lookup = parent.find_symbol(id, search_namespace);
			} else {
				local_lookup = None;
			}

			if local_lookup.is_some() {
				result = local_lookup;
			}
		}

		if result.is_none() && search_namespace {
			// Look for it in the namespace tree
			self.context.with_item(id, &self.scope, |item, id| {
				if let ModuleItemInterface::Functions(fns) = item {
					if fns.len() == 1 {
						let func = &*fns[0].read().unwrap();

						result = Some((
							id.clone(),

							Type::Function(
								Box::new(func.ret.clone()), 
								func.params.params.iter().map(|(ty, _, props)| (*props, ty.clone())).collect()
							)
						));
					} else {
						todo!("taking address of overloaded function is not yet supported")
					}
				}
			});
		}

		result
	}

	pub fn add_variable(&mut self, t: Type, n: Name, p: BindingProps) {
		self.variables.insert(n, (t, p));
	}
}

pub fn validate_function_body(
	scope: Identifier,
	func: &FnPrototype,
	elem: &mut ModuleASTElem,
	namespace: &ModuleInterface,
) -> ComuneResult<()> {
	let mut scope = FnScope::new(namespace, scope, func.ret.clone());

	for (param, name, props) in &func.params.params {
		scope.add_variable(param.clone(), name.clone().unwrap(), *props)
	}

	if let ModuleASTElem::Parsed(elem) = elem {
		let elem_node_data = elem.get_node_data().clone();

		// Validate function block & get return type, make sure it matches the signature
		elem.validate(&mut scope)?;

		let Expr::Atom(Atom::Block { items, result }, _) = elem else { panic!() };

		// Turn result values into explicit return expressions
		let has_result = result.is_some();

		if has_result {
			let expr = *result.take().unwrap();
			let node_data = expr.get_node_data().clone();

			items.push(Stmt::Expr(Expr::Atom(
				Atom::CtrlFlow(Box::new(ControlFlow::Return { expr: Some(expr) })),
				node_data,
			)));
		}

		let mut has_return = false;

		if has_result {
			if let Some(Stmt::Expr(expr)) = items.last() {
				let expr_ty = expr.get_type();

				if !expr_ty.castable_to(&scope.fn_return_type) {
					return Err(ComuneError::new(
						ComuneErrCode::ReturnTypeMismatch {
							expected: scope.fn_return_type,
							got: expr_ty.clone(),
						},
						elem.get_node_data().tk,
					));
				}
			}
		}

		if let Some(Stmt::Expr(Expr::Atom(Atom::CtrlFlow(ctrl), _))) = items.last() {
			has_return = matches!(&**ctrl, ControlFlow::Return { .. })
		}

		if !has_return {
			if scope.fn_return_type != Type::Basic(Basic::Void) {
				return Err(ComuneError::new(
					ComuneErrCode::ReturnTypeMismatch {
						expected: scope.fn_return_type.clone(),
						got: Type::Basic(Basic::Void),
					},
					elem_node_data.tk,
				));
			}

			items.push(Stmt::Expr(Expr::Atom(
				Atom::CtrlFlow(Box::new(ControlFlow::Return { expr: None })),
				NodeData {
					ty: Some(Type::Basic(Basic::Void)),
					tk: elem_node_data.tk,
				},
			)))
		}
	}

	Ok(())
}

pub fn is_candidate_viable(args: &Vec<Expr>, type_args: &Vec<Type>, func: &FnPrototype) -> bool {
	let params = &func.params.params;

	if args.len() < params.len() || (args.len() > params.len() && !func.params.variadic) {
		return false;
	}

	// TODO: Type arg deduction
	if type_args.len() != func.type_params.len() {
		return false;
	}

	for (i, (param, ..)) in params.iter().enumerate() {
		if let Some(arg) = args.get(i) {
			if !arg
				.get_type()
				.castable_to(&param.get_concrete_type(type_args))
			{
				return false;
			}
		}
	}

	true
}

fn candidate_compare(args: &[Expr], l: &FnPrototype, r: &FnPrototype, scope: &FnScope) -> Ordering {
	// Rank candidates

	let mut l_coerces = 0;
	let mut l_casts = 0;
	let mut r_coerces = 0;
	let mut r_casts = 0;

	// TODO: Support type arg substitution
	for (i, arg) in args.iter().enumerate() {
		let arg_ty = arg.get_type();

		if let Some((l_ty, ..)) = l.params.params.get(i) {
			if arg_ty != l_ty {
				if arg.coercable_to(arg_ty, l_ty, scope) {
					l_coerces += 1
				} else {
					l_casts += 1
				}
			}
		}

		if let Some((r_ty, ..)) = r.params.params.get(i) {
			if arg_ty != r_ty {
				if arg.coercable_to(arg_ty, r_ty, scope) {
					r_coerces += 1
				} else {
					r_casts += 1
				}
			}
		}
	}

	if l_casts > r_casts {
		Ordering::Greater
	} else if l_casts < r_casts {
		Ordering::Less
	} else if l_coerces > r_coerces {
		Ordering::Greater
	} else if l_coerces < r_coerces {
		Ordering::Less
	} else {
		Ordering::Equal
	}
}

pub fn validate_fn_call(
	call: &mut Atom,
	scope: &mut FnScope,
	node_data: &NodeData,
) -> ComuneResult<Type> {
	let mut candidates = vec![];
	let Atom::FnCall { name, args, type_args, resolved } = call else { panic!() };

	if let FnRef::Direct(resolved) = resolved {
		return Ok(resolved.read().unwrap().ret.clone());
	}

	if let FnRef::Indirect(expr) = resolved {
		let Some(Type::Function(ret, _)) = &expr.get_node_data().ty else {
			panic!()
		};

		return Ok(*ret.clone());
	}

	if let Some((local_name, local_ty)) = scope.find_symbol(name, false) {
		// Local function pointer
		if let Type::Function(ty_ret, ty_args) = local_ty {			
			for (arg, (_, param)) in args.iter_mut().zip(ty_args.iter()){
				arg.get_node_data_mut().ty = Some(param.clone());
				arg.validate(scope)?;
			}

			*resolved = FnRef::Indirect(Box::new(Expr::Atom(
				Atom::Identifier(local_name), 
				NodeData { 
					ty: Some(Type::Function(ty_ret.clone(), ty_args)), 
					tk: node_data.tk,
				}
			)));


			
			return Ok(*ty_ret);
		}
	}

	// Collect function candidates
	if !name.absolute {
		let mut name_unwrap = name.clone();

		name_unwrap.absolute = true;

		let mut scope_len = scope.scope.path.len();

		for (i, elem) in scope.scope.path.iter().enumerate() {
			name_unwrap.path.insert(i, elem.clone());
		}

		loop {
			if let Some((name, ModuleItemInterface::Functions(fns))) =
				scope.context.get_item(&name_unwrap)
			{
				for func in fns.iter() {
					candidates.push((name.clone(), func));
				}
			}

			if scope_len == 0 {
				break;
			} else {
				scope_len -= 1;
				name_unwrap.path.remove(scope_len);
			}
		}
	}

	for arg in args.iter_mut() {
		arg.validate(scope)?;
	}

	if candidates.is_empty() {
		return Err(ComuneError::new(
			ComuneErrCode::UndeclaredIdentifier(name.to_string()),
			node_data.tk,
		));
	}

	let mut candidates: Vec<_> = candidates
		.into_iter()
		.filter(|(_, func)| is_candidate_viable(args, type_args, &*func.read().unwrap()))
		.collect();

	let (selected_name, selected_candidate) = match candidates.len() {
		0 => {
			return Err(ComuneError::new(
				ComuneErrCode::NoCandidateFound {
					args: args.iter().map(|arg| arg.get_type().clone()).collect(),
					type_args: type_args.clone(),
					name: name.clone(),
				},
				node_data.tk,
			))
		} // No viable candidate

		1 => candidates[0].clone(),

		// More than one viable candidate
		_ => {
			// Sort candidates by cost
			candidates.sort_unstable_by(|(_, l), (_, r)| {
				candidate_compare(args, &*l.read().unwrap(), &*r.read().unwrap(), scope)
			});

			match candidate_compare(
				args,
				&*candidates[0].1.read().unwrap(),
				&*candidates[1].1.read().unwrap(),
				scope,
			) {
				Ordering::Less => candidates[0].clone(),

				Ordering::Equal => {
					return Err(ComuneError::new(ComuneErrCode::AmbiguousCall, node_data.tk))
				} // Ambiguous call

				_ => unreachable!(), // Not possible, just sorted it
			}
		}
	};

	let func = &*selected_candidate.read().unwrap();
	validate_arg_list(args, &func.params.params, type_args, scope)?;

	*resolved = FnRef::Direct(selected_candidate.clone());
	*name = selected_name;

	Ok(func.ret.get_concrete_type(type_args))
}

fn resolve_method_call(
	receiver: &Type,
	lhs: &Expr,
	fn_call: &mut Atom,
	scope: &mut FnScope,
) -> ComuneResult<Type> {
	let Atom::FnCall { name, args, type_args, resolved } = fn_call else { panic!() };

	// Already validated
	if let FnRef::Direct(resolved) = resolved {
		return Ok(resolved.read().unwrap().ret.clone());
	}

	if let FnRef::Indirect(expr) = resolved {
		let Some(Type::Function(ret, _)) = &expr.get_node_data().ty else {
			panic!()
		};

		return Ok(*ret.clone());
	}

	args.insert(0, lhs.clone());
	type_args.insert(0, receiver.clone());

	for arg in args.iter_mut() {
		arg.validate(scope)?;
	}

	// List of method candidates matched to their implementing types
	let mut candidates = vec![];

	// Go through all the impls in scope and find method candidates
	for (ty, im) in &scope.context.trait_solver.local_impls {
		let name = name.expect_scopeless().unwrap();

		let im = &*im.read().unwrap();

		if let Some(fns) = im.functions.get(name) {
			if receiver.fits_generic(&*ty.read().unwrap()) {
				for func in fns {
					candidates.push((
						ty.clone(),
						Identifier::from_parent(&im.canonical_root, name.clone()),
						func.clone(),
					));
				}
			}
		}
	}

	let mut candidates: Vec<_> = candidates
		.into_iter()
		.filter(|(_, _, func)| is_candidate_viable(args, type_args, &*func.read().unwrap()))
		.collect();

	let (_, selected_name, selected_candidate) = match candidates.len() {
		0 => panic!("no viable method candidate found"), // TODO: Proper error handling

		1 => candidates[0].clone(),

		// More than one viable candidate
		_ => {
			// Sort candidates by cost
			candidates.sort_unstable_by(|(_, _, l), (_, _, r)| {
				candidate_compare(args, &*l.read().unwrap(), &*r.read().unwrap(), scope)
			});

			// Compare the top two candidates
			match candidate_compare(
				args,
				&*candidates[0].2.read().unwrap(),
				&*candidates[1].2.read().unwrap(),
				scope,
			) {
				Ordering::Less => candidates[0].clone(),

				Ordering::Equal => {
					return Err(ComuneError::new(
						ComuneErrCode::AmbiguousCall,
						lhs.get_node_data().tk,
					))
				} // Ambiguous call

				_ => unreachable!(), // Not possible
			}
		}
	};

	let func = &*selected_candidate.read().unwrap();

	validate_arg_list(args, &func.params.params, type_args, scope)?;

	*resolved = FnRef::Direct(selected_candidate.clone());
	*name = selected_name;

	Ok(func.ret.clone())
}

fn validate_arg_list(
	args: &mut [Expr],
	params: &[(Type, Option<Name>, BindingProps)],
	type_args: &Vec<Type>,
	scope: &mut FnScope,
) -> ComuneResult<()> {
	for (i, arg) in args.iter_mut().enumerate() {
		// add parameter's type info to argument
		if let Some((param_ty, ..)) = params.get(i) {
			let param_concrete = param_ty.get_concrete_type(type_args);

			arg.get_node_data_mut().ty.replace(param_concrete.clone());

			let arg_type = arg.validate(scope)?;

			if !arg.coercable_to(&arg_type, &param_concrete, scope) {
				return Err(ComuneError::new(
					ComuneErrCode::InvalidCoercion {
						from: arg_type,
						to: param_concrete,
					},
					args[i].get_node_data().tk,
				));
			}

			if arg_type != param_concrete {
				arg.wrap_in_cast(param_concrete);
			}
		} else {
			// no parameter type for this argument (possible for varadiac functions)
			// so just validate it on its own
			let arg_type = arg.validate(scope)?;

			// also if it's a float we promote it to a double because presumably
			// ken and dennis were high on crack for 30 years straight or something
			// https://stackoverflow.com/questions/63144506/printf-doesnt-work-for-floats-in-llvm-ir
			if arg_type == Type::Basic(Basic::Float { size_bytes: 4 }) {
				arg.wrap_in_cast(Type::Basic(Basic::Float { size_bytes: 8 }));
			}
		}
	}

	Ok(())
}

pub fn validate_module_impl(
	interface: &ModuleInterface,
	module_impl: &mut ModuleImpl,
) -> ComuneResult<()> {
	for (proto, ast) in &mut module_impl.fn_impls {
		let mut scope = proto.read().unwrap().path.clone();
		scope.path.pop();

		validate_function_body(scope.clone(), &*proto.read().unwrap(), ast, interface)?
	}

	Ok(())
}

pub fn resolve_type(
	ty: &mut Type,
	namespace: &ModuleInterface,
	generics: &GenericParamList,
) -> ComuneResult<()> {
	match ty {
		Type::Pointer { pointee, .. } => resolve_type(pointee, namespace, generics),

		Type::Array(pointee, _size) => resolve_type(pointee, namespace, generics),

		Type::TypeRef(ItemRef::Unresolved {
			name: id,
			scope,
			type_args,
		}) => {
			let result;
			let generic_pos = generics.iter().position(|(name, ..)| name == id.name());

			if let Some(generic_pos) = generic_pos {
				// Generic type parameter
				result = Some(Type::TypeParam(generic_pos));
			} else {
				result = namespace.resolve_type(id, scope);
			}

			if let Some(Type::TypeRef(ItemRef::Resolved(TypeRef {
				def,
				mut args,
			}))) = result
			{
				args.append(type_args);
				*ty = Type::TypeRef(ItemRef::Resolved(TypeRef { def, args }));
				Ok(())
			} else if let Some(resolved) = result {
				*ty = resolved;
				Ok(())
			} else {
				Err(ComuneError::new(
					ComuneErrCode::UnresolvedTypename(id.to_string()),
					SrcSpan::new(),
				))
			}
		}

		Type::Tuple(_, types) => {
			for ty in types {
				resolve_type(ty, namespace, generics)?;
			}

			Ok(())
		}

		Type::TypeRef { .. } | Type::Basic(_) | Type::TypeParam(_) | Type::Never => Ok(()),

		Type::Function(ret, args) => {
			resolve_type(ret, namespace, generics)?;

			for (_, arg) in args {
				resolve_type(arg, namespace, generics)?;
			}

			Ok(())
		}
	}
}

pub fn resolve_algebraic_def(
	agg: &mut AlgebraicDef,
	namespace: &ModuleInterface,
	base_generics: &GenericParamList,
) -> ComuneResult<()> {
	let mut generics = base_generics.clone();
	generics.extend(agg.params.clone());

	for (_, types) in &mut agg.variants {
		for ty in types {
			resolve_type(ty, namespace, base_generics)?;
		}
	}

	for (_, ty, _) in &mut agg.members {
		resolve_type(ty, namespace, &generics)?;
	}

	if let Some(layout) = get_attribute(&agg.attributes, "layout") {
		if layout.args.len() != 1 {
			return Err(ComuneError::new(
				ComuneErrCode::ParamCountMismatch {
					expected: 1,
					got: layout.args.len(),
				},
				SrcSpan::new(),
			));
		}
		if layout.args[0].len() != 1 {
			return Err(ComuneError::new(
				ComuneErrCode::ParamCountMismatch {
					expected: 1,
					got: layout.args[0].len(),
				},
				SrcSpan::new(),
			));
		}

		if let Token::Name(layout_name) = &layout.args[0][0] {
			agg.layout = match &**layout_name {
				"declared" => types::DataLayout::Declared,
				"optimized" => types::DataLayout::Optimized,
				"packed" => types::DataLayout::Packed,
				_ => {
					return Err(ComuneError::new(
						ComuneErrCode::UnexpectedToken,
						SrcSpan::new(),
					))
				}
			}
		}
	}

	Ok(())
}

pub fn resolve_type_def(
	ty: &mut TypeDefKind,
	namespace: &ModuleInterface,
	base_generics: &GenericParamList,
) -> ComuneResult<()> {
	match ty {
		TypeDefKind::Algebraic(agg) => resolve_algebraic_def(agg, namespace, base_generics),

		_ => todo!(),
	}
}

pub fn resolve_namespace_types(interface: &ModuleInterface) -> ComuneResult<()> {
	// Resolve types

	for child in interface.children.values() {
		if let ModuleItemInterface::TypeAlias(alias) = child {
			resolve_type(&mut *alias.write().unwrap(), interface, &vec![])?;
		}
	}

	for child in interface.children.values() {
		match child {
			ModuleItemInterface::Functions(fns) => {
				for func in fns.iter() {
					let FnPrototype {
						ret,
						params,
						type_params: generics,
						path: _,
						attributes: _,
					} = &mut *func.write().unwrap();

					resolve_type(ret, interface, generics)?;

					for param in &mut params.params {
						resolve_type(&mut param.0, interface, generics)?;
					}
				}
			}

			ModuleItemInterface::Type(t) => {
				resolve_type_def(&mut t.write().unwrap().def, interface, &vec![])?
			}

			ModuleItemInterface::TypeAlias(ty) => {
				resolve_type(&mut *ty.write().unwrap(), interface, &vec![])?
			}

			ModuleItemInterface::Alias(_) => {}

			ModuleItemInterface::Trait(tr) => {
				let TraitInterface {
					items,
					supers: _,
					types: _,
					attributes: _,
				} = &mut *tr.write().unwrap();

				for fns in items.values_mut() {
					for func in fns {
						let FnPrototype {
							ret,
							params,
							type_params: generics,
							path: _,
							attributes: _,
						} = &mut *func.write().unwrap();

						generics.insert(0, ("Self".into(), vec![], None));

						resolve_type(ret, interface, generics)?;

						for param in &mut params.params {
							resolve_type(&mut param.0, interface, generics)?;
						}
					}
				}
			}

			_ => todo!(),
		};
	}

	for (ty, im) in &interface.trait_solver.local_impls {
		resolve_type(&mut *ty.write().unwrap(), interface, &vec![])?;

		// Resolve item references in canonical root

		let resolved_trait = if let Some(ItemRef::Unresolved {
			name,
			scope,
			type_args,
		}) = &im.read().unwrap().implements
		{
			interface.with_item(&name, &scope, |item, name| match item {
				ModuleItemInterface::Trait(tr) => Box::new(ItemRef::Resolved(TraitRef {
					def: Arc::downgrade(tr),
					name: name.clone(),
					args: type_args.clone(),
				})),

				_ => panic!(),
			})
		} else {
			None
		};

		let trait_qualif = (Some(Box::new(ty.read().unwrap().clone())), resolved_trait);

		im.write().unwrap().canonical_root.qualifier = trait_qualif.clone();

		for fns in im.read().unwrap().functions.values() {
			for func in fns {
				let FnPrototype {
					ret,
					params,
					type_params: generics,
					path,
					attributes: _,
				} = &mut *func.write().unwrap();

				path.qualifier = trait_qualif.clone();

				generics.insert(0, ("Self".into(), vec![], None));

				resolve_type(ret, interface, generics)?;

				for param in &mut params.params {
					resolve_type(&mut param.0, interface, generics)?;
				}
			}
		}
	}

	Ok(())
}

pub fn check_cyclical_deps(
	ty: &Arc<RwLock<TypeDef>>,
	parent_types: &mut Vec<Arc<RwLock<TypeDef>>>,
) -> ComuneResult<()> {
	if let TypeDefKind::Algebraic(agg) = &ty.read().unwrap().def {
		for member in agg.members.iter() {
			if let Type::TypeRef(ItemRef::Resolved(TypeRef { def: ref_t, .. })) = &member.1 {
				// Member is of a user-defined type

				if parent_types
					.iter()
					.any(|elem| Arc::ptr_eq(elem, &ref_t.upgrade().unwrap()))
				{
					return Err(ComuneError::new(
						ComuneErrCode::InfiniteSizeType,
						SrcSpan::new(),
					));
				}

				parent_types.push(ty.clone());
				check_cyclical_deps(&ref_t.upgrade().unwrap(), parent_types)?;
				parent_types.pop();
			}
		}
	}
	Ok(())
}

pub fn check_module_cyclical_deps(module: &ModuleInterface) -> ComuneResult<()> {
	for item in module.children.values() {
		if let ModuleItemInterface::Type(ty) = item {
			check_cyclical_deps(ty, &mut vec![])?
		}
	}

	Ok(())
}

impl Expr {
	pub fn create_cast(expr: Expr, to: Type, meta: NodeData) -> Expr {
		Expr::Atom(Atom::Cast(Box::new(expr), to), meta)
	}

	pub fn validate<'ctx>(&mut self, scope: &mut FnScope<'ctx>) -> ComuneResult<Type> {
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
									return Err(ComuneError::new(
										ComuneErrCode::InvalidSubscriptRHS { t: second_t },
										meta.tk,
									));
								}
							}

							Ok(*ty.clone())
						} else {
							Err(ComuneError::new(
								ComuneErrCode::InvalidSubscriptLHS { t: first_t },
								meta.tk,
							))
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
								return Err(ComuneError::new(
									ComuneErrCode::ExprTypeMismatch(first_t, second_t, op.clone()),
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
					Operator::Ref => Ok(expr_ty.ptr_type(true)),

					Operator::Deref => match expr_ty {
						Type::Pointer { pointee, .. } => Ok(*pointee),

						_ => Err(ComuneError::new(
							ComuneErrCode::InvalidDeref(expr_ty),
							meta.tk,
						)),
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
						if let Type::Pointer { pointee: other_p, mutable: other_m } = &target {
							if !other_m && **other_p
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

					Atom::Identifier(i) => scope.find_symbol(i, true).unwrap().1 == *target,

					Atom::FnCall { resolved, .. } => {
						if let FnRef::Direct(resolved) = resolved {
							resolved.read().unwrap().ret == *target
						} else if let FnRef::Indirect(expr) = resolved {
							let Some(Type::Function(ret, _)) = &expr.get_node_data().ty else {
								panic!()
							};

							&**ret == target
						} else {
							false
						}
					}

					Atom::Cast(_, cast_t) => target == cast_t,
					Atom::AlgebraicLit(alg_ty, _) => target == alg_ty,
					Atom::ArrayLit(_) => todo!(),
					Atom::Block { .. } => todo!(),
					Atom::CtrlFlow(_) => todo!(),

					Atom::Once(once) => {
						if let OnceAtom::Uneval(expr) = &*once.read().unwrap() {
							expr.coercable_to(from, target, scope)
						} else {
							false
						}
					}
				},

				Expr::Cons(_, _, _) => from == target,
				Expr::Unary(_, _, _) => from == target,
			},
		}
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
	) -> ComuneResult<Type> {
		let Type::TypeRef(ItemRef::Resolved(lhs_ref)) = lhs_ty else {
			return Err(ComuneError::new(ComuneErrCode::InvalidSubscriptLHS { t: lhs_ty.clone() }, meta.tk));
		};

		match &lhs_ref.def.upgrade().unwrap().read().unwrap().def {
			// Dot operator is on an algebraic type, so check if it's a member access or method call
			TypeDefKind::Algebraic(t) => match rhs {
				// Member access on algebraic type
				Expr::Atom(Atom::Identifier(id), _) => {
					if let Some((_, m)) = t.get_member(id.name(), Some(&lhs_ref.args)) {
						rhs.get_node_data_mut().ty = Some(m.clone());

						Ok(m)
					} else {
						panic!()
					}
				}

				// Method call on algebraic type
				// jesse. we have to call METHods
				Expr::Atom(Atom::FnCall { .. }, _) => {
					let Expr::Atom(rhs_atom, ..) = rhs else { panic!() };
					let ret = resolve_method_call(lhs_ty, lhs, rhs_atom, scope)?;

					rhs.get_node_data_mut().ty = Some(ret.clone());

					Ok(ret)
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
	) -> ComuneResult<Type> {
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

			Atom::CStringLit(_) => Ok(Type::Pointer { pointee: Box::new(Type::Basic(Basic::Integral {
				signed: false,
				size_bytes: 1,
			})), mutable: false }),

			Atom::Identifier(name) => {
				if let Some((id, ty)) = scope.find_symbol(name, true) {
					// Replace name with fully-qualified ID
					*name = id;
					Ok(ty)
				} else {
					Err(ComuneError::new(
						ComuneErrCode::UndeclaredIdentifier(name.to_string()),
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
					Err(ComuneError::new(
						ComuneErrCode::InvalidCast {
							from: expr_t,
							to: to.clone(),
						},
						expr.get_node_data().tk,
					))
				}
			}

			Atom::FnCall { .. } => validate_fn_call(self, scope, meta),

			Atom::ArrayLit(elems) => {
				let array_len =
					Arc::new(RwLock::new(vec![ConstExpr::Result(ConstValue::Integral(
						elems.len() as i128,
						Some(Basic::PtrSizeInt { signed: false }),
					))]));

				match &meta.ty {
					Some(Type::Array(ty, _)) => {
						for elem in elems {
							elem.get_node_data_mut().ty = Some(*ty.clone());

							elem.validate(scope)?;
						}

						Ok(Type::Array(ty.clone(), array_len))
					}

					_ => {
						let mut last_ty = None;

						for elem in elems {
							let current_ty = elem.validate(scope)?;

							if let Some(last_ty) = &last_ty {
								if &current_ty != last_ty {
									todo!()
								}
							} else {
								last_ty = Some(current_ty.clone());
							}
						}
						if let Some(ty) = &meta.ty {
							// Type hint is not an array type
							Err(ComuneError::new(
								ComuneErrCode::AssignTypeMismatch {
									expr: Type::Array(Box::new(last_ty.unwrap()), array_len),
									to: ty.clone(),
								},
								meta.tk,
							))
						} else {
							Ok(Type::Array(Box::new(last_ty.unwrap()), array_len))
						}
					}
				}
			}

			Atom::AlgebraicLit(ty, elems) => {
				if let Type::TypeRef(ItemRef::Resolved(TypeRef { def, args, .. })) = ty {
					if let TypeDefKind::Algebraic(alg) = &def.upgrade().unwrap().read().unwrap().def {
						for (name, expr) in elems.iter_mut() {
							let member_ty = if let Some((_, ty)) = alg.get_member(name, Some(args))
							{
								ty
							} else {
								// Invalid member in strenum literal
								todo!()
							};

							expr.get_node_data_mut().ty.replace(member_ty.clone());
							let expr_ty = expr.validate(scope)?;

							if !expr.coercable_to(&expr_ty, &member_ty, scope) {
								return Err(ComuneError::new(
									ComuneErrCode::AssignTypeMismatch {
										expr: expr_ty,
										to: member_ty,
									},
									expr.get_node_data().tk,
								));
							}
						}
						let mut missing_members = vec![];

						for (member, ..) in &alg.members {
							if !elems.iter().any(|(m, _)| member == m) {
								missing_members.push(member.clone());
							}
						}

						if !missing_members.is_empty() {
							return Err(ComuneError::new(
								ComuneErrCode::MissingInitializers {
									ty: ty.clone(),
									members: missing_members,
								},
								meta.tk,
							));
						}

						return Ok(ty.clone());
					}
				}

				todo!()
			}

			Atom::Block { items, result } => {
				let mut subscope = FnScope::from_parent(scope, false);

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
					let mut subscope = FnScope::from_parent(scope, false);

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
					let mut subscope = FnScope::from_parent(scope, true);

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
					let mut subscope = FnScope::from_parent(scope, true);

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
							Err(ComuneError::new(
								ComuneErrCode::ReturnTypeMismatch {
									expected: scope.fn_return_type.clone(),
									got: expr_ty,
								},
								meta.tk,
							))
						}
					} else if scope.fn_return_type == Type::Basic(Basic::Void) {
						Ok(Type::Never)
					} else {
						Err(ComuneError::new(
							ComuneErrCode::ReturnTypeMismatch {
								expected: scope.fn_return_type.clone(),
								got: Type::Basic(Basic::Void),
							},
							meta.tk,
						))
					}
				}

				ControlFlow::Break | ControlFlow::Continue => 
					if scope.is_inside_loop {
						Ok(Type::Never)
					} else {
						Err(ComuneError::new(
							ComuneErrCode::LoopCtrlOutsideLoop(
								if **ctrl == ControlFlow::Break { "break" } else { "continue" }
							), 
							meta.tk
						))
					},

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
						let mut subscope = FnScope::from_parent(scope, false);

						for binding in branch.0.get_bindings() {
							if let Binding {
								name: Some(name),
								ty,
								props,
							} = binding
							{
								subscope.add_variable(ty.clone(), name.clone(), *props);
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

			Atom::Once(once) => {
				if let OnceAtom::Uneval(expr) = &mut *once.write().unwrap() {
					expr.validate(scope)
				} else {
					panic!() // i dunno
				}
			}
		}
	}
}

impl Type {
	pub fn validate<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> ComuneResult<()> {
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
