// cIR monomorphization module

use std::{
	collections::{HashMap, HashSet},
	sync::{Arc, RwLock},
};

use crate::{
	ast::{
		get_attribute,
		module::Identifier,
		types::{AlgebraicDef, Basic, TypeDef, TypeDefKind},
	},
	lexer::Token,
};

use super::{CIRCallId, CIRFnMap, CIRFunction, CIRModule, CIRStmt, FuncID, RValue, Type, TypeName};

// A set of requested Generic monomorphizations, with a Vec of type arguments
// TODO: Extend system to support constants as arguments
type MonoizationList = HashSet<(Identifier, Vec<Type>)>;

type TypeSubstitutions = Vec<Type>;

// Map from index + parameters to indices of existing instances
type TypeInstances = HashMap<TypeName, HashMap<TypeSubstitutions, TypeName>>;
type FuncInstances = HashMap<FuncID, HashMap<TypeSubstitutions, FuncID>>;
type TypeMap = HashMap<TypeName, Arc<RwLock<TypeDef>>>;

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
		let function_protos: Vec<_> = self.functions.keys().cloned().collect();

		for proto in function_protos {
			// We can't monomorphize a generic function without its type parameters, only plain functions
			// Those plain functions call generic functions, which are then monoized from the call site
			if !self.functions[&proto].type_params.is_empty() {
				continue;
			}

			let function_monoized = Self::monoize_function(
				&self.functions,
				&mut functions_mono,
				&self.functions[&proto],
				&mut self.types,
				&vec![],
				&mut ty_instances,
				&mut fn_instances,
			);

			functions_mono.insert(proto, function_monoized);
		}
		
		let generic_ty_keys: Vec<_> = self.types
			.iter()
			.filter_map(|(k, v)| {
				let is_generic = match &v.read().unwrap().def {
					TypeDefKind::Algebraic(alg) => !alg.params.is_empty(),
					TypeDefKind::Class => todo!()
				};

				if is_generic {
					Some(k.clone())
				} else {
					None
				}
			})
			.collect();

		// Remove generic types
		for generic in generic_ty_keys {
			self.types.remove(&generic);
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
		types: &mut HashMap<TypeName, Arc<RwLock<TypeDef>>>,
		param_map: &TypeSubstitutions,
		ty_instances: &mut TypeInstances,
		fn_instances: &mut FuncInstances,
	) -> CIRFunction {
		let mut func = func.clone();

		for (var, ..) in &mut func.variables {
			Self::monoize_type(types, var, param_map, ty_instances);
		}

		Self::monoize_type(types, &mut func.ret, param_map, ty_instances);

		for block in &mut func.blocks {
			for stmt in block.items.iter_mut() {
				if let CIRStmt::Assignment((_lval, _), _) = stmt {
					// TODO: Find RValues in LValue projection
				}

				match stmt {
					CIRStmt::Expression(expr) | CIRStmt::Assignment(_, expr) => {
						Self::monoize_rvalue_types(types, expr, param_map, ty_instances);
					}

					CIRStmt::FnCall { type_args, .. } => {
						for arg in type_args.iter_mut() {
							Self::monoize_type(types, arg, param_map, ty_instances);
						}

						Self::monoize_call(
							functions_in,
							functions_out,
							stmt,
							types,
							ty_instances,
							fn_instances,
						);
					}

					_ => {}
				}
			}
		}

		func
	}

	fn monoize_call(
		functions_in: &CIRFnMap,
		functions_out: &mut CIRFnMap,
		func: &mut CIRStmt,
		types: &mut HashMap<TypeName, Arc<RwLock<TypeDef>>>,
		ty_instances: &mut TypeInstances,
		fn_instances: &mut FuncInstances,
	) {
		let CIRStmt::FnCall { 
			id, 
			type_args,
			..
		} = func else { panic!() };

		if type_args.is_empty() {
			return;
		}

		if let CIRCallId::Direct(id, _) = id {
			if !fn_instances.contains_key(id) {
				fn_instances.insert(id.clone(), HashMap::new());
			}

			if fn_instances[id].contains_key(type_args) {
				*id = fn_instances[id][type_args].clone();
			} else {
				let Some(fn_in) = functions_in.get(id) else {
					let mut fail_str = format!("failed to find CIRFnPrototype {id} in functions_in map! items:\n");

					for item in functions_in.keys() {
						fail_str.push_str(&format!("\t{item}\n"));
					}

					panic!("{fail_str}")
				};

				let monoized = Self::monoize_function(
					functions_in,
					functions_out,
					fn_in,
					types,
					type_args,
					ty_instances,
					fn_instances,
				);

				let mut insert_id = id.clone();

				for (i, type_arg) in type_args.iter().enumerate() {
					insert_id.type_params[i].2 = Some(type_arg.clone())
				}

				for (_, param) in &mut insert_id.params {
					Self::monoize_type(types, param, type_args, ty_instances);
				}

				Self::monoize_type(types, &mut insert_id.ret, type_args, ty_instances);

				if let (Some(qualifier), _) = &mut insert_id.name.qualifier {
					Self::monoize_type(types, qualifier, type_args, ty_instances);	
				}
				

				fn_instances
					.get_mut(id)
					.unwrap()
					.insert(type_args.clone(), insert_id.clone());

				functions_out.insert(insert_id.clone(), monoized);

				*id = insert_id;
			}

			type_args.clear();
		}
	}

	fn monoize_rvalue_types(
		types: &mut TypeMap,
		rval: &mut RValue,
		param_map: &TypeSubstitutions,
		type_instances: &mut TypeInstances,
	) {
		match rval {
			RValue::Atom(ty, ..) => {
				Self::monoize_type(types, ty, param_map, type_instances);
			}

			RValue::Cons(ty, [(lty, _), (rty, _)], ..) => {
				Self::monoize_type(types, lty, param_map, type_instances);
				Self::monoize_type(types, rty, param_map, type_instances);

				Self::monoize_type(types, ty, param_map, type_instances);
			}

			RValue::Cast { from, to, .. } => {
				Self::monoize_type(types, from, param_map, type_instances);
				Self::monoize_type(types, to, param_map, type_instances);
			}
		}
	}

	fn monoize_type(
		types: &mut TypeMap,
		ty: &mut Type,
		param_map: &TypeSubstitutions,
		instances: &mut TypeInstances,
	) {
		match ty {
			Type::Basic(_) => {}

			Type::Pointer { pointee, .. } => {
				Self::monoize_type(types, pointee, param_map, instances)
			}

			Type::Array(arr_ty, _) => Self::monoize_type(types, arr_ty, param_map, instances),

			Type::TypeRef { def, args } => {
				// If we're referring to a type with generics, check if the
				// instantation we want exists already. If not, create it.
				let def_up = def.upgrade().unwrap();
				let name = &def_up.read().unwrap().name;

				if !args.is_empty() {
					for arg in args.iter_mut() {
						Self::monoize_type(types, arg, param_map, instances);
					}

					let typename = name.to_string();

					if !instances.contains_key(&typename) {
						instances.insert(typename.clone(), HashMap::new());
					}

					let name = if instances[&typename].contains_key(param_map) {
						instances[&typename][param_map].clone()
					} else {
						Self::instantiate_type_def(types, typename.clone(), args, instances)
					};

					*def = Arc::downgrade(&types[&name]);
					args.clear();
				}
			}

			Type::TypeParam(idx) => {
				*ty = param_map[*idx].clone();
			}

			Type::Tuple(_, tuple_types) => {
				for ty in tuple_types {
					Self::monoize_type(types, ty, param_map, instances)
				}
			}

			Type::Function(ret, args) => {
				Self::monoize_type(types, ret, param_map, instances);

				for (_, arg) in args {
					Self::monoize_type(types, arg, param_map, instances)
				}
			}

			Type::Never => {}

			Type::Unresolved { .. } => panic!(),
		}
	}

	// Takes a Generic TypeDef with parameters and instantiates it.
	fn instantiate_type_def(
		types: &mut TypeMap,
		name: TypeName,
		param_map: &TypeSubstitutions,
		instances: &mut TypeInstances,
	) -> TypeName {
		let mut instance = types[&name].read().unwrap().clone();

		match &mut instance.def {
			TypeDefKind::Algebraic(AlgebraicDef {
				members, params, ..
			}) => {
				for (_, member, _) in members {
					Self::monoize_type(types, member, param_map, instances);
				}

				params.clear();
			}

			TypeDefKind::Class {} => todo!(),
		}

		let mut iter = param_map.iter();
		let mut insert_idx = name + "<" + &iter.next().unwrap().to_string();

		for param in iter {
			insert_idx.push_str(&param.to_string())
		}

		insert_idx += ">";
				
		if types.contains_key(&insert_idx) {
			return insert_idx;
		}

		*instance.name.path.last_mut().unwrap() = insert_idx.clone();
		types.insert(insert_idx.clone(), Arc::new(RwLock::new(instance)));

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

impl Type {
	fn mangle(&self) -> String {
		match self {
			Type::Basic(b) => String::from(b.mangle()),
			Type::Pointer { pointee, .. } => String::from("P") + &pointee.mangle(),
			Type::TypeRef { .. } => String::from("S_"),
			Type::Function(ret, args) => {
				let mut result = String::from("PF");

				result.push_str(&ret.mangle());

				for (_, arg) in args {
					result.push_str(&arg.mangle())
				}

				result
			}

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
