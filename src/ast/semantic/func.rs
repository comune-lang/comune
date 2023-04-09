use std::cmp::Ordering;

use crate::{
	ast::{
		controlflow::ControlFlow,
		expression::{Atom, Expr, FnRef, NodeData},
		module::{Identifier, ModuleASTElem, ModuleInterface, ModuleItemInterface, Name},
		statement::Stmt,
		types::{Basic, BindingProps, FnPrototype, Type},
		FnScope,
	},
	errors::{ComuneErrCode, ComuneError},
	parser::ComuneResult,
};

pub fn validate_function_body(
	scope: Identifier,
	func: &FnPrototype,
	elem: &mut ModuleASTElem,
	namespace: &ModuleInterface,
) -> ComuneResult<()> {
	let mut scope =
		FnScope::new(namespace, scope, func.ret.clone()).with_params(func.generics.clone());

	for (param, name, props) in &func.params.params {
		scope.add_variable(param.clone(), name.clone().unwrap(), *props)
	}

	if let ModuleASTElem::Parsed(elem) = elem {
		let elem_node_data = elem.get_node_data().clone();

		// Validate function block & get return type, make sure it matches the signature
		elem.validate(&mut scope)?;

		let Expr::Atom(Atom::Block { items, result, .. }, _) = elem else { panic!() };

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

				if !expr_ty.castable_to(&scope.fn_return_type.1) {
					return Err(ComuneError::new(
						ComuneErrCode::ReturnTypeMismatch {
							expected: scope.fn_return_type.1,
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
			if scope.fn_return_type.1 != Type::Basic(Basic::Void) {
				return Err(ComuneError::new(
					ComuneErrCode::ReturnTypeMismatch {
						expected: scope.fn_return_type.1.clone(),
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

pub fn validate_fn_call(
	call: &mut Atom,
	scope: &mut FnScope,
	node_data: &NodeData,
) -> ComuneResult<Type> {
	let mut candidates = vec![];
	let Atom::FnCall { name, args, type_args, resolved } = call else { panic!() };

	if let FnRef::Direct(resolved) = resolved {
		return Ok(resolved.read().unwrap().ret.1.clone());
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
				arg.get_node_data_mut().ty = Some(param.clone());
				arg.validate(scope)?;
			}

			*resolved = FnRef::Indirect(Box::new(Expr::Atom(
				Atom::Identifier(local_name),
				NodeData {
					ty: Some(Type::Function(ty_ret.clone(), ty_args)),
					tk: node_data.tk,
				},
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

	Ok(func.ret.1.get_concrete_type(type_args))
}

pub fn resolve_method_call(
	receiver: &Type,
	lhs: &Expr,
	fn_call: &mut Atom,
	scope: &mut FnScope,
) -> ComuneResult<Type> {
	let Atom::FnCall { name, args, type_args, resolved } = fn_call else { panic!() };

	// Already validated
	if let FnRef::Direct(resolved) = resolved {
		return Ok(resolved.read().unwrap().ret.1.clone());
	}

	if let FnRef::Indirect(expr) = resolved {
		let Some(Type::Function(ret, _)) = &expr.get_node_data().ty else {
			panic!()
		};

		return Ok(*ret.clone());
	}

	args.insert(0, lhs.clone());

	type_args.insert(0, receiver.clone());

	if let Type::TypeRef { args, .. } = receiver {
		type_args.reserve(args.len());

		for (i, arg) in args.iter().enumerate() {
			type_args.insert(i+1, arg.clone());
		}
	};

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
		0 => {
			return Err(ComuneError::new(
				ComuneErrCode::NoCandidateFound {
					args: args.iter().map(|arg| arg.get_type().clone()).collect(),
					type_args: type_args.clone(),
					name: name.clone(),
				},
				lhs.get_node_data().tk,
			))
		} // TODO: Proper error handling

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

	Ok(func.ret.1.get_concrete_type(&type_args))
}

pub fn is_candidate_viable(args: &Vec<Expr>, type_args: &Vec<Type>, func: &FnPrototype) -> bool {
	let params = &func.params.params;

	if args.len() < params.len() || (args.len() > params.len() && !func.params.variadic) {
		return false;
	}

	// TODO: Type arg deduction
	if type_args.len() != func.generics.len() {
		return false;
	}

	for (i, (param, ..)) in params.iter().enumerate() {
		if let Some(arg) = args.get(i) {
			if !arg
				.get_type()
				.get_concrete_type(type_args)
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

			let arg_type = arg.validate(scope)?.get_concrete_type(type_args);

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
