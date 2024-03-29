use std::{
	collections::HashSet,
	sync::{Arc, RwLock},
};

use crate::{
	ast::{
		get_attribute,
		module::{ModuleImpl, ModuleInterface, ModuleItemInterface},
		traits::{TraitInterface, TraitRef, ImplSolver},
		types::{
			self, BindingProps, FnPrototype, GenericArg, GenericParam, Generics, Type, TypeDef, Basic, TupleKind,
		},
		FnScope, Attribute,
	},
	constexpr::{ConstEval, ConstExpr},
	errors::{ComuneErrCode, ComuneError},
	lexer::{SrcSpan, Token},
	parser::{ComuneResult, Parser},
};

pub fn resolve_interface_types(parser: &mut Parser) -> ComuneResult<()> {
	// Resolve types
	let interface = &parser.interface;
	let module_impl = &mut parser.module_impl;

	// Resolve type aliases before everything else, for Annoying Reasons
	for child in interface.children.values() {
		if let ModuleItemInterface::TypeAlias(ty) = child {
			let (ty, generics) = &mut *ty.write().unwrap();

			resolve_type(ty, interface, generics)?;
			check_dst_indirection(ty, &BindingProps::default())?;
		}
	}

	for child in interface.children.values() {
		match child {
			ModuleItemInterface::Functions(fns) => {
				for func in fns.write().unwrap().iter_mut() {
					resolve_function_prototype(func, interface, module_impl)?;
				}
			}

			ModuleItemInterface::Type(t) => resolve_type_def(t.clone(), interface, module_impl)?,

			// Type aliases are resolved in the prev loop
			ModuleItemInterface::TypeAlias(_) => {}

			// Regular aliases are resolved on-the-fly, but we 
			// do check if they actually point to anything here
			ModuleItemInterface::Alias(alias) => {
				if alias.is_scoped() || Basic::get_basic_type(alias.name().as_str()).is_none() {
					let mut alias = alias.clone();
					
					alias.absolute = true;
					

					if !interface.get_item(&alias).is_some() {
						return Err(ComuneError::new(
							ComuneErrCode::UndeclaredIdentifier(alias.to_string()),
							SrcSpan::new()
						))
					}
				}
			}

			ModuleItemInterface::Trait(tr) => {
				let TraitInterface { functions: items, generics: trait_gens, .. } = &mut *tr.write().unwrap();

				for fns in items.values_mut() {
					for func_og in fns {
						let mut func_arc = Arc::new(func_og.as_ref().clone());
						let func = Arc::get_mut(&mut func_arc).unwrap();

						let FnPrototype {
							ret,
							params,
							generics,
							..
						} = func;

						generics.add_base_generics(trait_gens.clone());
						generics.insert_self_type();

						resolve_type(&mut ret.1, interface, generics)?;
						check_dst_indirection(&ret.1, &BindingProps::default())?;

						for param in &mut params.params {
							resolve_type(&mut param.0, interface, generics)?;
							check_dst_indirection(&param.0, &BindingProps::default())?;
						}

						// Update the module impl's version of the prototype
						// because everything is terrible and i hate my past self
						let fn_body = module_impl.fn_impls.remove(func_og).unwrap();
						module_impl.fn_impls.insert(func_arc.clone(), fn_body);
						*func_og = func_arc;
					}
				}
			}

			ModuleItemInterface::Variable(ty) => {
				resolve_type(&mut ty.write().unwrap(), interface, &Generics::new())?
			}
		};
	}

	for (ty, im) in &interface.impl_solver.impls {
		// Create type parameter list with empty Self param
		let mut generics = im.read().unwrap().params.clone();
		generics.insert_self_type();

		// Resolve the implementing type
		resolve_type(&mut *ty.write().unwrap(), interface, &generics)?;

		// Then use it to fill in the Self param's type
		*generics.get_mut("Self").unwrap().get_type_arg_mut() = Some(ty.read().unwrap().clone());

		resolve_generic_params(&mut generics, interface)?;

		// Resolve item references in canonical root
		if let Some(tr) = &mut im.write().unwrap().implements {
			resolve_trait_ref(tr, interface)?
		};
		
		let resolved_trait = if let Some(tr) = &im.read().unwrap().implements {
			Some(Box::new(tr.clone()))
		} else {
			None
		};

		let trait_qualif = (
			Some(Box::new(ty.read().unwrap().clone())),
			resolved_trait.clone(),
		);

		im.write().unwrap().canonical_root.qualifier = trait_qualif.clone();

		let mut trait_functions_found = HashSet::new();
		let mut im = im.write().unwrap();

		for (fn_name, fns) in &mut im.functions {
			for func_og in fns {
				let mut func_arc = Arc::new(func_og.as_ref().clone());
				let func = Arc::get_mut(&mut func_arc).unwrap();

				// Add impl's generics to function prototype

				let FnPrototype {
					generics: fn_generics,
					path,
					ret,
					params,
					..
				} = func;

				path.qualifier = trait_qualif.clone();

				fn_generics.add_base_generics(generics.clone());

				resolve_type(&mut ret.1, interface, &fn_generics)?;
				check_dst_indirection(&ret.1, &BindingProps::default())?;

				for (param, _, props) in &mut params.params {
					resolve_type(param, interface, &fn_generics)?;
					check_dst_indirection(param, props)?;
				}

				if let Some(tr) = &resolved_trait {
					// Check if the function signature matches a declaration in the trait

					let TraitRef { def: Some(def), args, .. } = &**tr else {
						panic!()
					};

					let mut args = args.clone();
					args.push(GenericArg::Type(ty.read().unwrap().clone()));

					let def = def.upgrade().unwrap();
					let def = def.read().unwrap();

					let mut found_match = false;

					if let Some(trait_fns) = def.functions.get(fn_name) {
						// Go through the overloads in the trait definition
						// and look for one that matches this impl function

						'overloads: for trait_fn in trait_fns {
							if trait_fn.params.params.len() != params.params.len() {
								continue 'overloads;
							}

							if trait_fn.params.variadic != params.variadic {
								continue 'overloads;
							}

							if ret.1 != trait_fn.ret.1.get_concrete_type(&args) {
								continue 'overloads;
							}

							for (i, (ty, _, props)) in trait_fn.params.params.iter().enumerate() {
								if params.params[i].2 != *props {
									continue 'overloads;
								}

								let concrete_self = params.params[i].0.get_concrete_type(&args);
								let concrete_other = ty.get_concrete_type(&args);

								if concrete_self != concrete_other {
									continue 'overloads;
								}
							}

							// Checks out!
							found_match = true;
							trait_functions_found.insert(trait_fn.clone());
							break;
						}
					}

					if !found_match {
						return Err(ComuneError::new(
							ComuneErrCode::TraitFunctionMismatch,
							SrcSpan::new(),
						));
					}
				}

				// Update the module impl's version of the prototype
				let fn_body = module_impl.fn_impls.remove(func_og).unwrap();
				module_impl.fn_impls.insert(func_arc.clone(), fn_body);
				*func_og = func_arc;
			}
		}

		if let Some(tr) = &resolved_trait.and_then(|t| Some(*t)) {
			// Now go through all the trait's functions and check for missing impls
			for (_, funcs) in &tr.unwrap_def().read().unwrap().functions {
				for func in funcs {
					if !trait_functions_found.contains(func) {
						return Err(ComuneError::new(
							ComuneErrCode::MissingTraitFuncImpl(func.to_string()),
							SrcSpan::new(),
						));
					}
				}
			}
		}
	}

	Ok(())
}

pub fn check_dst_indirection(ty: &Type, props: &BindingProps) -> ComuneResult<()> {
	match ty {
		Type::Slice(slicee) => {
			if !props.is_ref {
				return Err(ComuneError::new(
					ComuneErrCode::DSTWithoutIndirection,
					props.span,
				));
			}

			check_dst_indirection(&slicee, &BindingProps::default())
		}

		Type::Tuple(_, types) => {
			for ty in types {
				check_dst_indirection(ty, &BindingProps::default())?;
			}

			Ok(())
		}

		_ => Ok(()),
	}
}

pub fn find_unsatisfied_trait_bounds(
	arg: &GenericArg,
	param: &GenericParam,
	generics: &Generics,
	solver: &ImplSolver
) -> Option<(Type, Vec<TraitRef>)> {
	let mut result = vec![];

	match (arg, param) {
		(GenericArg::Type(ty), GenericParam::Type { bounds, .. }) => {
			for tr in bounds {
				assert!(tr.is_resolved(), "unresolved trait bound!");

				if !solver.is_trait_implemented(ty, tr, generics) {
					result.push(tr.clone());
				}
			}

			if !result.is_empty() {
				return Some((ty.clone(), result))
			}
		}
	}

	None
}

pub fn resolve_generic_arg(
	arg: &mut GenericArg,
	namespace: &ModuleInterface,
	generics: &Generics,
) -> ComuneResult<()> {
	match arg {
		GenericArg::Type(ty) => resolve_type(ty, namespace, generics),
	}
}

pub fn resolve_type(
	ty: &mut Type,
	namespace: &ModuleInterface,
	generics: &Generics,
) -> ComuneResult<()> {
	match ty {
		Type::Pointer(pointee, _) => resolve_type(pointee, namespace, generics),

		Type::Array(pointee, _size) => resolve_type(pointee, namespace, generics),

		Type::Slice(slicee) => resolve_type(slicee, namespace, generics),

		Type::Unresolved {
			name: id,
			scope,
			generic_args,
			span,
		} => {
			for arg in generic_args.iter_mut() {
				resolve_generic_arg(arg, namespace, generics)?;
			}

			let generic_pos = generics
				.params
				.iter()
				.position(|(name, ..)| name == id.name());

			let result = if let Some(generic_pos) = generic_pos {
				// Generic type parameter
				Some(Type::TypeParam(generic_pos))
			} else {
				namespace.resolve_type(id, scope)
			};

			if let Some(Type::TypeRef { def, mut args }) = result {
				generic_args.append(&mut args);

				*ty = Type::TypeRef {
					def,
					args: generic_args.drain(..).collect(),
				};

				Ok(())
			} else if let Some(resolved) = result {
				*ty = resolved;

				Ok(())
			} else {
				Err(ComuneError::new(
					ComuneErrCode::UnresolvedTypename(id.to_string()),
					*span,
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

		Type::Infer(span) => return Err(
			ComuneError::new(
				ComuneErrCode::UnsupportedInference,
				*span
			)
		),

		Type::Function(ret, args) => {
			resolve_type(ret, namespace, generics)?;

			for (_, arg) in args {
				resolve_type(arg, namespace, generics)?;
			}

			Ok(())
		}
	}
}

pub fn resolve_type_def(
	ty_def: Arc<RwLock<TypeDef>>,
	interface: &ModuleInterface,
	module_impl: &mut ModuleImpl,
) -> ComuneResult<()> {
	let ty_lock = &mut *ty_def.write().unwrap();

	resolve_generic_params(&mut ty_lock.generics, interface)?;

	let ty_has_drop = ty_lock.drop.is_some();

	for (_, variant) in &mut ty_lock.variants {
		resolve_type_def(variant.clone(), interface, module_impl)?;

		if ty_has_drop && variant.read().unwrap().drop.is_some() {
			return Err(ComuneError::new(
				ComuneErrCode::DtorDefOverlap,
				SrcSpan::new(),
			));
		}
	}

	for (_, ty, _) in &mut ty_lock.members {
		resolve_type(ty, interface, &ty_lock.generics)?;
	}

	// This part is ugly as hell. sorry

	if let Some(drop) = &mut ty_lock.drop {
		resolve_function_prototype(drop, interface, module_impl)?;

		// Check whether the first parameter exists and is `mut& self`
		let Some((Type::TypeRef { def, .. }, _, props)) = drop.params.params.get(0) else {
			return Err(ComuneError::new(
				ComuneErrCode::DtorSelfParam(ty_lock.name.clone()),
				SrcSpan::new(),
			))
		};

		if !Arc::ptr_eq(&ty_def, &def.upgrade().unwrap()) || !props.is_mut || !props.is_ref {
			return Err(ComuneError::new(
				ComuneErrCode::DtorSelfParam(ty_lock.name.clone()),
				SrcSpan::new(),
			));
		}
	}

	for init in &mut ty_lock.init {
		resolve_function_prototype(init, interface, module_impl)?;

		// Check whether the first parameter exists and is `new& self`
		let Some((Type::TypeRef { def, .. }, _, props)) = init.params.params.get(0) else {
			return Err(ComuneError::new(
				ComuneErrCode::CtorSelfParam(ty_lock.name.clone()),
				SrcSpan::new(),
			))
		};

		if !Arc::ptr_eq(&ty_def, &def.upgrade().unwrap()) || !props.is_new {
			return Err(ComuneError::new(
				ComuneErrCode::CtorSelfParam(ty_lock.name.clone()),
				SrcSpan::new(),
			));
		}
	}

	if let Some(layout) = get_attribute(&ty_lock.attributes, "layout") {
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
			ty_lock.layout = match layout_name.as_str() {
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

pub fn resolve_function_prototype(
	func_og: &mut Arc<FnPrototype>,
	interface: &ModuleInterface,
	module_impl: &mut ModuleImpl,
) -> ComuneResult<()> {
	let mut func = func_og.as_ref().clone();

	resolve_generic_params(&mut func.generics, interface)?;

	resolve_type(&mut func.ret.1, interface, &func.generics)?;
	check_dst_indirection(&func.ret.1, &BindingProps::default())?;

	for (param, _, props) in &mut func.params.params {
		resolve_type(param, interface, &func.generics)?;
		check_dst_indirection(param, props)?;
	}

	let mut og_path = func.path.path;
	func.path.path = interface.name.path.clone();
	func.path.path.append(&mut og_path);

	if func.path.path.len() == 2 && func.path.name().as_str() == "main" {
		func.attributes.push(Attribute {
			name: "no_mangle".to_string(),
			args: vec![],
		});
	}

	let func_arc = Arc::new(func);

	// Update the module impl's version of the prototype
	let fn_body = module_impl.fn_impls.remove(func_og).unwrap();
	module_impl.fn_impls.insert(func_arc.clone(), fn_body);

	*func_og = func_arc;

	Ok(())
}

fn resolve_generic_params(
	generics: &mut Generics,
	interface: &ModuleInterface,
) -> ComuneResult<()> {
	for (_, generic) in &mut generics.params {
		match generic {
			GenericParam::Type { bounds, .. } => {
				for bound in bounds {
					resolve_trait_ref(bound, interface)?;
				}
			}
		}
	}

	Ok(())
}

fn resolve_trait_ref(tr: &mut TraitRef, interface: &ModuleInterface) -> ComuneResult<()> {
	let TraitRef { def: def @ None, name, scope, .. } = tr else {
		return Ok(())
	};
	
	let found = interface.with_item(&name, &scope, |item, name| match item {
		ModuleItemInterface::Trait(tr) => Some((Arc::downgrade(tr), name.clone())),

		_ => None,
	});

	if let Some(Some(found)) = found {
		*def = Some(found.0);
		*name = found.1;
		Ok(())
	} else {
		Err(ComuneError::new(
			ComuneErrCode::UnresolvedTrait(name.clone()),
			SrcSpan::new(),
		))
	}
}

pub fn check_cyclical_deps(
	ty: &Arc<RwLock<TypeDef>>,
	parent_types: &mut Vec<Arc<RwLock<TypeDef>>>,
) -> ComuneResult<()> {
	let def = ty.read().unwrap();

	for member in def.members.iter() {
		if let Type::TypeRef { def: ref_t, .. } = &member.1 {
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

impl Type {
	pub fn validate(&mut self, scope: &FnScope, span: SrcSpan) -> ComuneResult<()> {
		match self {
			Type::Array(ty, n) => {
				ty.validate(scope, span)?;

				let result = if let ConstExpr::Expr(e) = &*n.read().unwrap() {
					ConstExpr::Result(e.eval_const(scope)?)
				} else {
					panic!()
				};

				*n.write().unwrap() = result;
			}

			Type::Tuple(kind, types) => {
				for ty in types.iter_mut() {
					ty.validate(scope, span)?;
				}

				if *kind == TupleKind::Sum {
					types.retain(|ty| !ty.is_never());

					if types.len() == 1 {
						let ty = types.pop().unwrap();
						*self = ty;
					}
				}
			}

			Type::TypeRef { def, args } => {
				let def = def.upgrade().unwrap();
				let def = def.read().unwrap();

				// check if type arguments satisfy trait bounds
				for (arg, (_, param)) in args.iter().zip(def.generics.params.iter()) {
					let bounds = find_unsatisfied_trait_bounds(arg, param, &scope.generics, &scope.context.impl_solver);

					if let Some((ty, bounds)) = bounds {
						return Err(ComuneError::new(
							ComuneErrCode::UnsatisfiedTraitBounds(ty, bounds),
							span
						))
					}
				}
			}

			Type::Pointer(ty, _) => ty.validate(scope, span)?,

			Type::Slice(ty) => ty.validate(scope, span)?,


			_ => {}
		}

		Ok(())
	}

	pub fn resolve_inference_vars(&mut self, hint: Type, span: SrcSpan) -> ComuneResult<()> {
		match self {
			Type::Infer(_) => { *self = hint; Ok(()) }

			Type::TypeRef { args, .. } => {
				let Type::TypeRef { args: other_args, .. } = hint else {
					return Ok(());
				};

				if args.len() < other_args.len() {
					for _ in 0..other_args.len()-args.len() {
						args.push(GenericArg::Type(Type::Infer(span)));
					}
				}

				for (GenericArg::Type(lhs), GenericArg::Type(rhs)) in args.iter_mut().zip(other_args.into_iter()) {
					lhs.resolve_inference_vars(rhs, span)?;
				}

				Ok(())			
			}

			Type::Pointer(pointee, kind) => {
				match hint {
					Type::Pointer(other, other_kind) if *kind == other_kind => {
						pointee.resolve_inference_vars(*other, span)
					}

					_ => Ok(()),
				}
			}

			Type::Tuple(kind, types) => {
				match hint {
					Type::Tuple(other_kind, other_types) if *kind == other_kind => {
						for (lhs, rhs) in types.iter_mut().zip(other_types.into_iter()) {
							lhs.resolve_inference_vars(rhs, span)?;
						}
						
						Ok(())
					}

					_ => Err(ComuneError::new(
						ComuneErrCode::AssignTypeMismatch { expr: hint, to: self.clone() },
						span
					))
				}
			}
			
			_ => Ok(())
		}
	}
}
