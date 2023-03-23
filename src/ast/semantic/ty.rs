use std::sync::{Arc, RwLock};

use crate::{
	ast::{
		get_attribute,
		module::{ItemRef, ModuleInterface, ModuleItemInterface},
		traits::{TraitInterface, TraitRef},
		types::{self, AlgebraicDef, FnPrototype, GenericParamList, Type, TypeDef, TypeDefKind},
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
			let found = interface.with_item(&name, &scope, |item, name| match item {
				ModuleItemInterface::Trait(tr) => Some(Box::new(ItemRef::Resolved(TraitRef {
					def: Arc::downgrade(tr),
					name: name.clone(),
					args: type_args.clone(),
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

pub fn resolve_type(
	ty: &mut Type,
	namespace: &ModuleInterface,
	generics: &GenericParamList,
) -> ComuneResult<()> {
	match ty {
		Type::Pointer { pointee, .. } => resolve_type(pointee, namespace, generics),

		Type::Array(pointee, _size) => resolve_type(pointee, namespace, generics),

		Type::Unresolved {
			name: id,
			scope,
			type_args,
			span
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

pub fn check_cyclical_deps(
	ty: &Arc<RwLock<TypeDef>>,
	parent_types: &mut Vec<Arc<RwLock<TypeDef>>>,
) -> ComuneResult<()> {
	if let TypeDefKind::Algebraic(agg) = &ty.read().unwrap().def {
		for member in agg.members.iter() {
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
