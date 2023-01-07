// cIR monomorphization module

use std::collections::{HashMap, HashSet};

use crate::{
	ast::{get_attribute, namespace::Identifier, types::Basic},
	lexer::Token,
};

use super::{
	CIRFnMap, CIRFunction, CIRModule, CIRStmt, CIRType, CIRTypeDef, FuncID, Operand, RValue,
	TypeName,
};

// A set of requested Generic monomorphizations, with a Vec of type arguments
// TODO: Extend system to support constants as arguments
type MonoizationList = HashSet<(Identifier, Vec<CIRType>)>;

type TypeSubstitutions = Vec<CIRType>;

// Map from index + parameters to indices of existing instances
type TypeInstances = HashMap<TypeName, HashMap<TypeSubstitutions, TypeName>>;
type FuncInstances = HashMap<FuncID, HashMap<TypeSubstitutions, FuncID>>;

impl CIRModule {
	// monoize() consumes `self` and returns a CIRModule with all generics monomorphized, names mangled, etc.
	// This is necessary to prepare the module for LLVM codegen, but should be done after semantic analysis is complete.
	// The function takes `self` by value to convey that this is a destructive operation.
	pub fn monoize(mut self) -> Self {
		self.monoize_generics();
		self.mangle();
		self
	}

	fn monoize_generics(&mut self) {
		let mut ty_instances = HashMap::new();
		let mut fn_instances = HashMap::new();
		let mut functions_mono = HashMap::new();

		// While types can be modified in-place, function instantiations are monomorphized
		// by traversing the function list. And because Rust makes us write code that's
		// "correct" and "responsible" and "halfway decent", we have to clone the function
		// list here so we can mutate the clone. And yes, I *am* grumpy about it.
		let function_names: Vec<_> = self.functions.keys().cloned().collect();

		for name in function_names {
			// We can't monomorphize a generic function without its type parameters, only plain functions
			// Those plain functions call generic functions, which are then monoized from the call site
			if !self.functions[&name].type_params.is_empty() {
				continue;
			}

			let function_monoized = Self::monoize_function(
				&self.functions,
				&mut functions_mono,
				&self.functions[&name],
				&mut self.types,
				&vec![],
				&mut ty_instances,
				&mut fn_instances,
			);

			functions_mono.insert(name, function_monoized);
		}

		// Remove generic types
		for generic in ty_instances.keys() {
			self.types.remove(generic);
		}

		// Remove generic functions
		for generic in fn_instances.keys() {
			functions_mono.remove(generic);
		}

		self.functions = functions_mono;
	}

	fn monoize_function(
		functions_in: &CIRFnMap,
		functions_out: &mut CIRFnMap,
		func: &CIRFunction,
		types: &mut HashMap<TypeName, CIRTypeDef>,
		param_map: &TypeSubstitutions,
		type_instances: &mut TypeInstances,
		fn_instances: &mut FuncInstances,
	) -> CIRFunction {
		let mut func = func.clone();

		for (var, _) in &mut func.variables {
			Self::monoize_type(types, var, param_map, type_instances);
		}

		Self::monoize_type(types, &mut func.ret, param_map, type_instances);

		for block in &mut func.blocks {
			for stmt in block {
				if let CIRStmt::Assignment((_lval, _), _) = stmt {
					// TODO: Find RValues in LValue projection
				}

				match stmt {
					CIRStmt::Expression(expr, _)
					| CIRStmt::Assignment(_, (expr, _))
					| CIRStmt::Return(Some((expr, _))) => {
						Self::monoize_rvalue_types(types, expr, param_map, type_instances);

						Self::monoize_fn_calls(
							functions_in,
							functions_out,
							expr,
							types,
							param_map,
							type_instances,
							fn_instances,
						)
					}

					CIRStmt::Switch(expr, branches, _) => {
						Self::monoize_rvalue_types(types, expr, param_map, type_instances);

						for (ty, val, _) in branches {
							Self::monoize_operand(types, val, ty, param_map, type_instances)
						}
					}

					_ => {}
				}
			}
		}

		func
	}

	fn monoize_fn_calls(
		functions_in: &CIRFnMap,
		functions_out: &mut CIRFnMap,
		rval: &mut RValue,
		types: &mut HashMap<TypeName, CIRTypeDef>,
		param_map: &TypeSubstitutions,
		ty_instances: &mut TypeInstances,
		fn_instances: &mut FuncInstances,
	) {
		match rval {
			RValue::Atom(_, _, Operand::FnCall(name, _, type_args)) => {
				let mut param_map = param_map.clone();
				param_map.append(type_args);

				Self::monoize_call(
					functions_in,
					functions_out,
					name,
					types,
					&param_map,
					ty_instances,
					fn_instances,
				)
			}

			RValue::Cons(_, [(_, lhs), (_, rhs)], _) => {
				if let Operand::FnCall(name, _, type_args) = lhs {
					let mut param_map = param_map.clone();
					param_map.append(type_args);

					Self::monoize_call(
						functions_in,
						functions_out,
						name,
						types,
						&param_map,
						ty_instances,
						fn_instances,
					)
				}

				if let Operand::FnCall(name, _, type_args) = rhs {
					let mut param_map = param_map.clone();
					param_map.append(type_args);

					Self::monoize_call(
						functions_in,
						functions_out,
						name,
						types,
						&param_map,
						ty_instances,
						fn_instances,
					)
				}
			}

			RValue::Cast {
				val: Operand::FnCall(name, _, type_args),
				..
			} => {
				let mut param_map = param_map.clone();
				param_map.append(type_args);

				Self::monoize_call(
					functions_in,
					functions_out,
					name,
					types,
					&param_map,
					ty_instances,
					fn_instances,
				)
			}

			_ => {}
		}
	}

	fn monoize_call(
		functions_in: &CIRFnMap,
		functions_out: &mut CIRFnMap,
		func: &mut FuncID,
		types: &mut HashMap<TypeName, CIRTypeDef>,
		param_map: &TypeSubstitutions,
		ty_instances: &mut TypeInstances,
		fn_instances: &mut FuncInstances,
	) {
		if param_map.is_empty() {
			return;
		}

		if !fn_instances.contains_key(func) {
			fn_instances.insert(func.clone(), HashMap::new());
		}

		if fn_instances[func].contains_key(param_map) {
			*func = fn_instances[func][param_map].clone();
		} else {
			let monoized = Self::monoize_function(
				functions_in,
				functions_out,
				&functions_in[func],
				types,
				param_map,
				ty_instances,
				fn_instances,
			);

			let mut insert_id = func.clone();
			let mut name_suffix = "<".to_string();
			let mut param_iter = param_map.iter();

			name_suffix.push_str(&param_iter.next().unwrap().to_string());

			for param in param_iter {
				name_suffix.push_str(", ");
				name_suffix.push_str(&param.to_string());
			}

			name_suffix += ">";

			insert_id.name.path.push(name_suffix.into());

			fn_instances
				.get_mut(func)
				.unwrap()
				.insert(param_map.clone(), insert_id.clone());
			functions_out.insert(insert_id.clone(), monoized);

			*func = insert_id;
		}
	}

	fn monoize_rvalue_types(
		types: &mut HashMap<String, CIRTypeDef>,
		rval: &mut RValue,
		param_map: &TypeSubstitutions,
		type_instances: &mut TypeInstances,
	) {
		match rval {
			RValue::Atom(ty, _, val) => {
				if let Operand::FnCall(_, _, type_args) = val {
					let mut param_map = param_map.clone();
					param_map.append(&mut type_args.clone());

					Self::monoize_type(types, ty, &param_map, type_instances);
				} else {
					Self::monoize_type(types, ty, param_map, type_instances);
				}
			}

			RValue::Cons(ty, [(lty, lhs), (rty, rhs)], _) => {
				Self::monoize_operand(types, lhs, lty, param_map, type_instances);
				Self::monoize_operand(types, rhs, rty, param_map, type_instances);

				Self::monoize_type(types, ty, param_map, type_instances);
			}

			RValue::Cast { from, to, val } => {
				Self::monoize_operand(types, val, from, param_map, type_instances);
				Self::monoize_type(types, to, param_map, type_instances);
			}
		}
	}

	fn monoize_operand(
		types: &mut HashMap<String, CIRTypeDef>,
		val: &mut Operand,
		ty: &mut CIRType,
		param_map: &TypeSubstitutions,
		type_instances: &mut TypeInstances,
	) {
		if let Operand::FnCall(_, _, type_args) = val {
			let mut param_map = param_map.clone();
			param_map.append(&mut type_args.clone());

			Self::monoize_type(types, ty, &param_map, type_instances);
		} else {
			Self::monoize_type(types, ty, param_map, type_instances);
		}
	}

	fn monoize_type(
		types: &mut HashMap<String, CIRTypeDef>,
		ty: &mut CIRType,
		param_map: &TypeSubstitutions,
		instances: &mut TypeInstances,
	) {
		match ty {
			CIRType::Basic(_) => {}

			CIRType::Pointer(pointee) => Self::monoize_type(types, pointee, param_map, instances),
			CIRType::Array(arr_ty, _) => Self::monoize_type(types, arr_ty, param_map, instances),
			CIRType::Reference(refee) => Self::monoize_type(types, refee, param_map, instances),

			CIRType::TypeRef(idx, args) => {
				// If we're referring to a type with generics, check if the
				// instantation we want exists already. If not, create it.
				if !args.is_empty() {
					if !instances.contains_key(idx) {
						instances.insert(idx.clone(), HashMap::new());
					}

					if !instances[idx].contains_key(param_map) {
						*idx = Self::instantiate_type_def(types, idx.clone(), args, instances);
					}
				}
			}

			CIRType::TypeParam(idx) => {
				*ty = param_map[*idx].clone();
			}

			CIRType::Tuple(_, tuple_types) => {
				for ty in tuple_types {
					Self::monoize_type(types, ty, param_map, instances)
				}
			}
		}
	}

	// Takes a Generic CIRTypeDef with parameters and instantiates it.
	fn instantiate_type_def(
		types: &mut HashMap<String, CIRTypeDef>,
		name: TypeName,
		param_map: &TypeSubstitutions,
		instances: &mut TypeInstances,
	) -> TypeName {
		let mut instance = types[&name].clone();

		match &mut instance {
			CIRTypeDef::Algebraic {
				members,
				type_params,
				..
			} => {
				for member in members {
					Self::monoize_type(types, member, param_map, instances);
				}
				type_params.clear();
			}

			CIRTypeDef::Class {} => todo!(),
		}

		let mut iter = param_map.iter();
		let mut insert_idx = name + "<" + &iter.next().unwrap().to_string();

		for param in iter {
			insert_idx.push_str(&param.to_string())
		}

		insert_idx += ">";

		types.insert(insert_idx.clone(), instance);
		insert_idx
	}

	fn mangle(&mut self) {
		// Mangle functions

		for (id, func) in &mut self.functions {
			// Check if the function has a `no_mangle` or `export_as` attribute, or if it's `main`. If not, mangle the name
			if get_attribute(&func.attributes, "no_mangle").is_some()
				|| (&**id.name.name() == "main" && !id.name.is_qualified())
			{
				func.mangled_name = Some(id.name.name().to_string());
			} else if let Some(export_name) = get_attribute(&func.attributes, "export_as") {
				// Export with custom symbol name
				if let Some(first_arg) = export_name.args.get(0) {
					if let Some(Token::StringLiteral(name)) = first_arg.get(0) {
						func.mangled_name = Some(name.clone())
					} else {
						panic!() //TODO: Proper error handling
					}
				}
			} else {
				// Mangle name
				func.mangled_name = Some(mangle_name(&id.name, func));
			}
		}
	}
}

// Basic implementation of the Itanium C++ ABI, which is used by GCC and Clang.
// This is not complete or robust at all, but it should do for now.

fn mangle_name(name: &Identifier, func: &CIRFunction) -> String {
	let mut result = String::from("_Z");

	assert!(name.absolute);

	if !name.is_qualified() {
		result.push_str(&name.name().len().to_string());
		result.push_str(name.name());
	} else {
		result.push('N');
		for scope in &name.path {
			result.push_str(&scope.len().to_string());
			result.push_str(scope);
		}
		result.push('E');
	}

	if func.arg_count == 0 {
		result.push('v');
	} else {
		for i in 0..func.arg_count {
			result.push_str(&func.variables[i].0.mangle());
		}
	}

	result
}

impl CIRType {
	fn mangle(&self) -> String {
		match self {
			CIRType::Basic(b) => String::from(b.mangle()),
			CIRType::Pointer(p) => String::from("P") + &p.mangle(),
			CIRType::Reference(r) => String::from("R") + &r.mangle(),
			CIRType::TypeRef(_, _) => String::from("S_"),
			_ => todo!(),
		}
	}
}

// See https://itanium-cxx-abi.github.io/cxx-abi/abi.html#mangle.builtin-type
impl Basic {
	fn mangle(&self) -> &str {
		match self {
			Basic::Bool => "b",

			Basic::Integral { signed, size_bytes } => {
				if *signed {
					match size_bytes {
						8 => "x",
						4 => "i",
						2 => "s",
						1 => "c",
						_ => unimplemented!(),
					}
				} else {
					match size_bytes {
						8 => "y",
						4 => "j",
						2 => "t",
						1 => "h",
						_ => unimplemented!(),
					}
				}
			}

			Basic::PtrSizeInt { signed } => {
				if *signed {
					"x"
				} else {
					"y"
				}
			}

			Basic::Float { size_bytes } => match size_bytes {
				8 => "d",
				4 => "f",
				_ => unimplemented!(),
			},

			Basic::Char => "c",
			Basic::Void => "v",
			Basic::Str => "cj", // TODO: Figure this out
		}
	}
}
