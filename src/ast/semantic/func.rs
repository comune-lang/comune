use std::{cmp::Ordering, collections::HashSet, sync::Arc};

use itertools::Itertools;

use crate::{
	ast::{
		controlflow::ControlFlow,
		expression::{Atom, Expr, FnRef, NodeData},
		module::{
			Identifier, ModuleASTElem, ModuleImportKind, ModuleInterface, ModuleItemInterface, Name,
		},
		statement::Stmt,
		types::{Basic, FnPrototype, GenericArgs, Type, FnParamList, GenericArg},
		FnScope,
	},
	errors::{ComuneErrCode, ComuneError},
	lexer::SrcSpan,
	parser::ComuneResult,
};

use super::ty::find_unsatisfied_trait_bounds;

pub fn validate_function_body(
	scope: Identifier,
	func: &FnPrototype,
	elem: &mut ModuleASTElem,
	namespace: &ModuleInterface,
) -> ComuneResult<()> {
	let mut scope = FnScope::new(namespace, scope, func.ret.clone(), &func.generics);

	for (param, name, props) in &func.params.params {
		scope.add_variable(param.clone(), name.clone().unwrap(), *props)
	}

	let ModuleASTElem::Parsed(elem) = elem else {
		panic!("unparsed function body in semantic phase!")
	};

	// Validate function block & get return type, make sure it matches the signature
	elem.validate(&mut scope)?;

	let Expr::Atom(Atom::Block { items, result, .. }, meta) = elem else { panic!() };

	// Turn result values into explicit return expressions
	if let Some(expr) = result {
		let expr_ty = expr.get_type();

		if !expr.coercable_to(&scope.ret.1, &scope) && !scope.ret.1.is_void() {
			return Err(ComuneError::new(
				ComuneErrCode::ReturnTypeMismatch {
					expected: scope.ret.1,
					got: expr_ty.clone(),
				},
				meta.span,
			));
		}

		let mut expr = *result.take().unwrap();
		let expr_meta = expr.get_node_data().clone();

		expr.try_wrap_in_cast(scope.ret.1.clone())?;

		if scope.ret.1.is_void() {
			items.push(Stmt::Expr(expr));

			items.push(Stmt::Expr(Expr::Atom(
				Atom::CtrlFlow(Box::new(ControlFlow::Return { expr: None })),
				expr_meta,
			)));
		} else {
			items.push(Stmt::Expr(Expr::Atom(
				Atom::CtrlFlow(Box::new(ControlFlow::Return { expr: Some(expr) })),
				expr_meta,
			)));
		}
	}

	let has_return = if let Some(Stmt::Expr(Expr::Atom(Atom::CtrlFlow(ctrl), _))) = items.last() {
		matches!(&**ctrl, ControlFlow::Return { .. })
	} else {
		false
	};

	if !has_return {
		if scope.ret.1 != Type::Basic(Basic::Void) {
			return Err(ComuneError::new(
				ComuneErrCode::ReturnTypeMismatch {
					expected: scope.ret.1.clone(),
					got: Type::Basic(Basic::Void),
				},
				meta.span,
			));
		}

		items.push(Stmt::Expr(Expr::Atom(
			Atom::CtrlFlow(Box::new(ControlFlow::Return { expr: None })),
			NodeData {
				ty: Some(Type::Basic(Basic::Void)),
				span: meta.span,
			},
		)))
	}

	Ok(())
}

pub fn validate_fn_call(
	call: &mut Atom,
	scope: &mut FnScope,
	node_data: &NodeData,
) -> ComuneResult<Type> {
	let mut candidates = vec![];
	let Atom::FnCall { name, args, generic_args, resolved } = call else { panic!() };

	if let FnRef::Direct(resolved) = resolved {
		return Ok(resolved.ret.1.get_concrete_type(generic_args));
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
			for (arg, (_, param)) in args.iter_mut().zip(ty_args.iter()) {
				arg.set_type_hint(param.clone());
				arg.validate(scope)?;
			}

			*resolved = FnRef::Indirect(Box::new(Expr::Atom(
				Atom::Identifier(local_name),
				NodeData {
					ty: Some(Type::Function(ty_ret.clone(), ty_args)),
					span: node_data.span,
				},
			)));

			return Ok(*ty_ret);
		}
	}

	// Collect function candidates
	if !name.absolute {
		let mut name_unwrap = scope.scope.clone();

		name_unwrap.absolute = true;

		let mut scope_len = scope.scope.path.len();

		name_unwrap.path.append(&mut name.path.clone());

		loop {
			if let Some((_, ModuleItemInterface::Functions(fns))) =
				scope.context.get_item(&name_unwrap)
			{
				for func in fns.read().unwrap().iter() {
					candidates.push(func.clone());
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
			node_data.span,
		));
	}

	let mut candidates_filtered: Vec<_> = candidates
		.clone()
		.into_iter()
		.unique()
		.filter(|func| is_candidate_viable(args, generic_args, func, &scope))
		.collect();

	let func = try_select_candidate(
		name,
		args,
		generic_args,
		&mut candidates_filtered,
		node_data.span,
		scope,
	)?;

	validate_arg_list(args, &func.params, generic_args, scope)?;

	if func.is_unsafe && !scope.is_unsafe {
		return Err(ComuneError::new(
			ComuneErrCode::UnsafeCall(func.clone()),
			node_data.span,
		));
	}

	*resolved = FnRef::Direct(func.clone());
	*name = func.path.clone();

	Ok(func.ret.1.get_concrete_type(generic_args))
}

pub fn resolve_method_call(
	receiver: &Type,
	lhs: &Expr,
	fn_call: &mut Atom,
	scope: &mut FnScope,
	span: SrcSpan,
) -> ComuneResult<Type> {
	let Atom::FnCall { name, args, generic_args, resolved } = fn_call else { panic!() };

	// Already validated
	if let FnRef::Direct(resolved) = resolved {
		return Ok(resolved.ret.1.clone());
	}

	if let FnRef::Indirect(expr) = resolved {
		let Some(Type::Function(ret, _)) = &expr.get_node_data().ty else {
			panic!()
		};

		return Ok(*ret.clone());
	}

	args.insert(0, lhs.clone());

	//if let Type::TypeRef { args, .. } = receiver {
	//	generic_args.append(&mut args.clone());
	//};

	//generic_args.push(GenericArg::Type(receiver.clone()));

	for arg in args.iter_mut() {
		arg.validate(scope)?;
	}

	// List of method candidates matched to their implementing types
	let candidates =
		collect_impl_candidates(&scope.context, name.expect_scopeless().unwrap(), receiver);

	let candidates: Vec<_> = candidates
		.into_iter()
		.filter_map(|(impl_ty, func)| {
			let mut generic_args = vec![];
			
			receiver.extract_generic_args(&impl_ty, &mut generic_args);
			generic_args.push(GenericArg::Type(receiver.clone()));
			
			if is_candidate_viable(args, &generic_args, &func, &scope) {
				Some((generic_args, func))
			} else {
				None
			}
		})
		.collect();
	
	let mut candidates_rhs = candidates.iter().map(|(_, func)| func.clone()).collect_vec();
	let func = try_select_candidate(name, args, generic_args, &mut candidates_rhs, span, scope)?;
	
	*generic_args = candidates.into_iter().find(|(_, fun)| fun == &func).unwrap().0;

	validate_arg_list(args, &func.params, generic_args, scope)?;

	if func.is_unsafe && !scope.is_unsafe {
		return Err(ComuneError::new(
			ComuneErrCode::UnsafeCall(func.clone()),
			span,
		));
	}

	*resolved = FnRef::Direct(func.clone());
	*name = func.path.clone();

	Ok(func.ret.1.get_concrete_type(&generic_args))
}

pub fn try_select_candidate(
	name: &Identifier,
	args: &[Expr],
	generic_args: &GenericArgs,
	candidates: &mut [Arc<FnPrototype>],
	span: SrcSpan,
	scope: &FnScope,
) -> ComuneResult<Arc<FnPrototype>> {
	match candidates.len() {
		0 => Err(ComuneError::new(
			ComuneErrCode::NoCandidateFound {
				args: args.iter().map(|arg| arg.get_type().clone()).collect(),
				generic_args: generic_args.clone(),
				name: name.clone(),
			},
			span,
		)),

		1 => Ok(candidates[0].clone()),

		// More than one viable candidate
		_ => {
			// Sort candidates by cost
			candidates.sort_unstable_by(|l, r| candidate_compare(args, l, r, scope));

			// Compare the top two candidates
			match candidate_compare(args, &candidates[0], &candidates[1], scope) {
				Ordering::Less => Ok(candidates[0].clone()),

				Ordering::Equal => Err(ComuneError::new(ComuneErrCode::AmbiguousCall, span)), // Ambiguous call

				_ => unreachable!(), // Not possible
			}
		}
	}
}

pub fn is_candidate_viable(
	args: &Vec<Expr>,
	generic_args: &GenericArgs,
	func: &FnPrototype,
	scope: &FnScope,
) -> bool {
	let params = &func.params.params;

	if args.len() < params.len() || (args.len() > params.len() && !func.params.variadic) {
		return false;
	}

	// TODO: Type arg deduction
	if generic_args.len() < func.generics.non_defaulted_count() {
		return false;
	}

	let impl_solver = &scope.context.impl_solver;

	for (arg, (_, generic)) in generic_args.iter().zip(func.generics.params.iter()) {
		let bounds = find_unsatisfied_trait_bounds(arg, generic, &func.generics, impl_solver);

		if bounds.is_some() {
			return false;
		}
	}

	for (i, (param, ..)) in params.iter().enumerate() {
		if let Some(arg) = args.get(i) {
			let arg_concrete = arg.get_type();
			let param_concrete = param.get_concrete_type(generic_args);

			if !arg_concrete.castable_to(&param_concrete) {
				return false
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
				if arg.coercable_to(l_ty, scope) {
					l_coerces += 1
				} else {
					l_casts += 1
				}
			}
		}

		if let Some((r_ty, ..)) = r.params.params.get(i) {
			if arg_ty != r_ty {
				if arg.coercable_to(r_ty, scope) {
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

pub fn validate_arg_list(
	args: &mut [Expr],
	params: &FnParamList,
	generic_args: &GenericArgs,
	scope: &mut FnScope,
) -> ComuneResult<()> {
	for (i, arg) in args.iter_mut().enumerate() {
		// add parameter's type info to argument
		if let Some((param_ty, ..)) = params.params.get(i) {
			let param_concrete = param_ty.get_concrete_type(generic_args);

			arg.set_type_hint(param_concrete.clone());

			let arg_type = arg.validate(scope)?;

			if !arg.coercable_to(&param_concrete, scope) {
				return Err(ComuneError::new(
					ComuneErrCode::InvalidCoercion {
						from: arg_type,
						to: param_concrete,
					},
					args[i].get_node_data().span,
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
			if arg_type == Type::f32_type() {
				arg.wrap_in_cast(Type::f64_type());
			}
		}
	}

	Ok(())
}

fn collect_impl_candidates(
	interface: &ModuleInterface,
	name: &Name,
	receiver: &Type,
) -> Vec<(Type, Arc<FnPrototype>)> {
	let mut result = vec![];

	collect_impl_candidates_recursive(
		interface,
		name,
		receiver,
		&mut result,
		&mut HashSet::new(),
		true,
	);

	result
}

fn collect_impl_candidates_recursive(
	interface: &ModuleInterface,
	name: &Name,
	receiver: &Type,
	candidates: &mut Vec<(Type, Arc<FnPrototype>)>,
	already_visited: &mut HashSet<Identifier>,
	collect_imports: bool,
) {
	if already_visited.contains(&interface.name) {
		return;
	}

	already_visited.insert(interface.name.clone());

	for (ty, im) in &interface.impl_solver.impls {
		let im = &*im.read().unwrap();
		let ty = &*ty.read().unwrap();

		if let Some(fns) = im.functions.get(name) {
			if receiver.fits_generic(ty) {
				for func in fns {
					candidates.push((ty.clone(), func.clone()));
				}
			}
		}
	}

	for (_, import) in &interface.imported {
		if collect_imports || matches!(&import.import_kind, ModuleImportKind::Child(_)) {
			collect_impl_candidates_recursive(
				&import.interface,
				name,
				receiver,
				candidates,
				already_visited,
				false,
			)
		}
	}
}
