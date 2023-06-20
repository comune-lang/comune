use std::{
	collections::HashSet,
	sync::{Arc, RwLock},
};

use crate::{
	ast::{
		get_attribute,
		module::{ItemRef, ModuleInterface, ModuleItemInterface},
		traits::{TraitInterface, TraitRef},
		types::{self, BindingProps, FnPrototype, Generics, Type, TypeDef},
		FnScope,
	},
	constexpr::{ConstEval, ConstExpr},
	errors::{ComuneErrCode, ComuneError},
	lexer::{SrcSpan, Token},
	parser::ComuneResult,
};

pub fn resolve_interface_types(interface: &ModuleInterface) -> ComuneResult<()> {
	// Resolve types

	for child in interface.children.values() {
		if let ModuleItemInterface::TypeAlias(alias) = child {
			resolve_type(&mut *alias.write().unwrap(), interface, &vec![])?;
			check_dst_indirection(&alias.read().unwrap(), &BindingProps::default())?;
		}
	}

	for child in interface.children.values() {
		match child {
			ModuleItemInterface::Functions(fns) => {
				for func in fns.iter() {
					let FnPrototype {
						ret,
						params,
						generics,
						..
					} = &mut *func.write().unwrap();

					resolve_type(&mut ret.1, interface, generics)?;
					check_dst_indirection(&ret.1, &BindingProps::default())?;

					for (param, _, props) in &mut params.params {
						resolve_type(param, interface, generics)?;
						check_dst_indirection(param, props)?;
					}
				}
			}

			ModuleItemInterface::Type(t) => resolve_type_def(t.clone(), interface)?,

			ModuleItemInterface::TypeAlias(ty) => {
				resolve_type(&mut *ty.write().unwrap(), interface, &vec![])?
			}

			ModuleItemInterface::Alias(_) => {}

			ModuleItemInterface::Trait(tr) => {
				let TraitInterface { items, .. } = &mut *tr.write().unwrap();

				for fns in items.values_mut() {
					for func in fns {
						let FnPrototype {
							ret,
							params,
							generics,
							..
						} = &mut *func.write().unwrap();

						generics.push(("Self".into(), vec![], None));

						resolve_type(&mut ret.1, interface, generics)?;
						check_dst_indirection(&ret.1, &BindingProps::default())?;

						for param in &mut params.params {
							resolve_type(&mut param.0, interface, generics)?;
							check_dst_indirection(&param.0, &BindingProps::default())?;
						}
					}
				}
			}

			_ => todo!(),
		};
	}

	for (ty, im) in &interface.impl_solver.local_impls {
		// Create type parameter list with empty Self param
		let mut generics = im.read().unwrap().params.clone();
		generics.push(("Self".into(), vec![], None));

		// Resolve the implementing type
		resolve_type(&mut *ty.write().unwrap(), interface, &generics)?;

		// Then use it to fill in the Self param's type
		generics.last_mut().unwrap().2 = Some(ty.read().unwrap().clone());

		// Resolve item references in canonical root
		let resolved_trait = if let Some(ItemRef::Unresolved {
			name,
			scope,
			generic_args,
		}) = &im.read().unwrap().implements
		{
			let found = interface.with_item(&name, &scope, |item, name| match item {
				ModuleItemInterface::Trait(tr) => Some(Box::new(ItemRef::Resolved(TraitRef {
					def: Arc::downgrade(tr),
					name: name.clone(),
					args: generic_args.clone(),
				}))),

				_ => None,
			});

			if let Some(found) = found {
				found
			} else {
				return Err(ComuneError::new(
					ComuneErrCode::UnresolvedTrait(name.clone()),
					SrcSpan::new(),
				));
			}
		} else {
			None
		};

		let trait_qualif = (
			Some(Box::new(ty.read().unwrap().clone())),
			resolved_trait.clone(),
		);

		im.write().unwrap().canonical_root.qualifier = trait_qualif.clone();

		let mut trait_functions_found = HashSet::new();

		let im = im.read().unwrap();

		for (fn_name, fns) in &im.functions {
			for func in fns {
				// Add impl's generics to function prototype
				{
					let FnPrototype {
						generics: fn_generics,
						path,
						..
					} = &mut *func.write().unwrap();

					path.qualifier = trait_qualif.clone();

					for (i, param) in generics.iter().enumerate() {
						fn_generics.insert(i, param.clone());
					}
				}

				resolve_function_prototype(&mut *func.write().unwrap(), interface)?;

				let FnPrototype { ret, params, .. } = &*func.read().unwrap();

				if let Some(tr) = &resolved_trait {
					// Check if the function signature matches a declaration in the trait

					let ItemRef::Resolved(TraitRef { def, args, .. }) = &**tr else {
						panic!()
					};

					let mut args = args.clone();
					args.insert(0, ty.read().unwrap().clone());

					let def = def.upgrade().unwrap();
					let def = def.read().unwrap();

					let mut found_match = false;

					if let Some(funcs) = def.items.get(fn_name) {
						// Go through the overloads in the trait definition
						// and look for one that matches this impl function

						'overloads: for func in funcs {
							let func = func.read().unwrap();

							if func.params.params.len() != params.params.len() {
								continue 'overloads;
							}

							if func.params.variadic != params.variadic {
								continue 'overloads;
							}

							if ret.1 != func.ret.1.get_concrete_type(&args) {
								continue 'overloads;
							}

							for (i, (ty, _, props)) in func.params.params.iter().enumerate() {
								if params.params[i].2 != *props {
									continue 'overloads;
								}

								let concrete_self = params.params[i].0.get_concrete_type(&args);
								let concrete_other = ty.get_concrete_type(&args);

								if concrete_self != concrete_other {
									println!(
										"mismatch between {concrete_self} and {concrete_other}"
									);
									println!("type args: {:?}", args);

									continue 'overloads;
								}
							}

							// Checks out!
							found_match = true;
							trait_functions_found.insert(func.clone());
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
			}
		}

		if let Some(ItemRef::Resolved(tr)) = &resolved_trait.and_then(|t| Some(*t)) {
			// Now go through all the trait's functions and check for missing impls
			for (_, funcs) in &tr.def.upgrade().unwrap().read().unwrap().items {
				for func in funcs {
					if !trait_functions_found.contains(&*func.read().unwrap()) {
						return Err(ComuneError::new(
							ComuneErrCode::MissingTraitFuncImpl(func.read().unwrap().to_string()),
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

pub fn resolve_type(
	ty: &mut Type,
	namespace: &ModuleInterface,
	generics: &Generics,
) -> ComuneResult<()> {
	match ty {
		Type::Pointer { pointee, .. } => resolve_type(pointee, namespace, generics),

		Type::Array(pointee, _size) => resolve_type(pointee, namespace, generics),

		Type::Slice(slicee) => resolve_type(slicee, namespace, generics),

		Type::Unresolved {
			name: id,
			scope,
			type_args,
			span,
		} => {
			let result;
			let generic_pos = generics.iter().position(|(name, ..)| name == id.name());

			if let Some(generic_pos) = generic_pos {
				// Generic type parameter
				result = Some(Type::TypeParam(generic_pos));
			} else {
				result = namespace.resolve_type(id, scope);
			}

			for arg in type_args.iter_mut() {
				resolve_type(arg, namespace, generics)?;
			}

			if let Some(Type::TypeRef { def, mut args }) = result {
				args.append(type_args);
				*ty = Type::TypeRef { def, args };
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
	ty_lock: Arc<RwLock<TypeDef>>,
	interface: &ModuleInterface,
) -> ComuneResult<()> {
	let mut ty = ty_lock.write().unwrap();

	// Create type parameter list with empty Self param
	let mut generics = ty.params.clone();

	generics.push((
		"Self".into(),
		vec![],
		Some(Type::TypeRef {
			def: Arc::downgrade(&ty_lock),
			args: (0..ty.params.len()).map(|i| Type::TypeParam(i)).collect(),
		}),
	));

	for (_, types) in &mut ty.variants {
		for ty in types {
			resolve_type(ty, interface, &generics)?;
		}
	}

	for (_, ty, _) in &mut ty.members {
		resolve_type(ty, interface, &generics)?;
	}

	// This part is ugly as hell. sorry

	if let Some(drop) = &ty.drop {
		resolve_function_prototype(&mut *drop.write().unwrap(), interface)?;

		// Check whether the first parameter exists and is `mut& self`
		let drop = drop.read().unwrap();

		let Some((Type::TypeRef { def, .. }, _, props)) = drop.params.params.get(0) else {
			return Err(ComuneError::new(
				ComuneErrCode::DtorSelfParam(ty.name.clone()),
				SrcSpan::new(),
			))
		};

		if !Arc::ptr_eq(&ty_lock, &def.upgrade().unwrap()) || !props.is_mut || !props.is_ref {
			return Err(ComuneError::new(
				ComuneErrCode::DtorSelfParam(ty.name.clone()),
				SrcSpan::new(),
			));
		}
	}

	for init in &ty.init {
		resolve_function_prototype(&mut *init.write().unwrap(), interface)?;

		// Check whether the first parameter exists and is `new& self`
		let init = init.read().unwrap();

		let Some((Type::TypeRef { def, .. }, _, props)) = init.params.params.get(0) else {
			return Err(ComuneError::new(
				ComuneErrCode::CtorSelfParam(ty.name.clone()),
				SrcSpan::new(),
			))
		};

		if !Arc::ptr_eq(&ty_lock, &def.upgrade().unwrap()) || !props.is_new {
			return Err(ComuneError::new(
				ComuneErrCode::CtorSelfParam(ty.name.clone()),
				SrcSpan::new(),
			));
		}
	}

	if let Some(layout) = get_attribute(&ty.attributes, "layout") {
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
			ty.layout = match &**layout_name {
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
	func: &mut FnPrototype,
	interface: &ModuleInterface,
) -> ComuneResult<()> {
	let FnPrototype {
		ret,
		params,
		generics,
		..
	} = func;

	resolve_type(&mut ret.1, interface, generics)?;
	check_dst_indirection(&ret.1, &BindingProps::default())?;

	for (param, _, props) in &mut params.params {
		resolve_type(param, interface, generics)?;
		check_dst_indirection(param, props)?;
	}
	Ok(())
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
	pub fn validate<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> ComuneResult<()> {
		match self {
			Type::Array(_, n) => {
				let result = if let ConstExpr::Expr(e) = &*n.read().unwrap() {
					ConstExpr::Result(e.eval_const(scope)?)
				} else {
					panic!()
				};

				*n.write().unwrap() = result;
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
