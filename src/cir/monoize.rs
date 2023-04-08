// cIR monomorphization module

use std::{
	collections::{HashMap, HashSet},
	sync::{Arc, RwLock, Weak},
	time::Duration,
};

use crate::{
	ast::{
		get_attribute,
		module::Identifier,
		types::{AlgebraicDef, Basic, TypeDef, TypeDefKind},
	},
	lexer::Token,
};

use super::{
	CIRCallId, CIRFnMap, CIRFunction, CIRModule, CIRStmt, CIRTyMap, FuncID, RValue, Type, TypeName,
};

// A set of requested Generic monomorphizations, with a Vec of type arguments
// TODO: Extend system to support constants as arguments
type MonoizationList = HashSet<(Identifier, Vec<Type>)>;

type TypeSubstitutions = Vec<Type>;

// Map from index + parameters to indices of existing instances
type TypeInstanceMap = HashMap<TypeName, HashMap<TypeSubstitutions, TypeName>>;
type FuncInstanceMap = HashMap<FuncID, HashMap<TypeSubstitutions, FuncID>>;
type TypeMap = HashMap<TypeName, Arc<RwLock<TypeDef>>>;

// The monomorphization server (MonomorphServer) stores the bodies of generic
// functions, so that they can be instantiated even after their modules of origin
// are done compiling.
pub struct MonomorphServer {
	fn_templates: RwLock<CIRFnMap>,
	fn_instances: RwLock<CIRFnMap>,
	ty_instances: RwLock<CIRTyMap>,
}

impl MonomorphServer {
	pub fn new() -> Self {
		MonomorphServer {
			fn_templates: RwLock::default(),
			fn_instances: RwLock::default(),
			ty_instances: RwLock::default(),
		}
	}

	// Consumes a CIRModule and returns its monomorphized form,
	// also registering its generic functions for potential
	// further instantiations by downstream modules
	pub fn monoize_module(&self, mut module: CIRModule) -> CIRModule {
		self.monoize_generics(&mut module);
		self.mangle(&mut module);
		module
	}

	fn monoize_generics(&self, module: &mut CIRModule) {
		let mut functions_mono = HashMap::new();

		// While types can be modified in-place, function instantiations are monomorphized
		// by traversing the function list. And because Rust makes us write code that's
		// "correct" and "responsible" and "halfway decent", we have to clone the function
		// list here so we can mutate the clone. And yes, I *am* grumpy about it.
		//
		// TODO: when `drain_filter` get stabilized, be sure to use it here
		let function_protos: Vec<_> = module.functions.keys().cloned().collect();

		let generics: Vec<_> = function_protos
			.iter()
			.filter(|k| !module.functions[k].type_params.is_empty())
			.collect();

		for proto in generics {
			let mut fn_repo = self.fn_templates.write().unwrap();
			let fn_template = module.functions.remove(proto).unwrap();

			if !fn_template.is_extern {
				fn_repo.insert(proto.clone(), fn_template);
			}
		}

		for proto in function_protos {
			if !module.functions.contains_key(&proto) {
				// Generic function, we don't need to monomorphize this on its own
				continue;
			}

			let function_monoized = self.monoize_function(
				&module.functions,
				&mut functions_mono,
				&module.functions[&proto],
				&mut module.types,
				&vec![],
			);

			functions_mono.insert(proto, function_monoized);
		}

		let generic_ty_keys: Vec<_> = module
			.types
			.iter()
			.filter_map(|(k, v)| {
				let is_generic = match &v.read().unwrap().def {
					TypeDefKind::Algebraic(alg) => !alg.params.is_empty(),
					TypeDefKind::Class => todo!(),
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
			module.types.remove(&generic);
		}

		module.functions = functions_mono;
	}

	fn monoize_function(
		&self,
		functions_in: &CIRFnMap,
		functions_out: &mut CIRFnMap,
		func: &CIRFunction,
		types: &mut HashMap<TypeName, Arc<RwLock<TypeDef>>>,
		param_map: &TypeSubstitutions,
	) -> CIRFunction {
		let mut func = func.clone();

		for (var, ..) in &mut func.variables {
			self.monoize_type(types, var, param_map);
		}

		self.monoize_type(types, &mut func.ret.1, param_map);

		for block in &mut func.blocks {
			for stmt in block.items.iter_mut() {
				if let CIRStmt::Assignment((_lval, _), _) = stmt {
					// TODO: Find RValues in LValue projection
				}

				match stmt {
					CIRStmt::Expression(expr) | CIRStmt::Assignment(_, expr) => {
						self.monoize_rvalue_types(types, expr, param_map);
					}

					CIRStmt::FnCall { type_args, .. } => {
						for arg in type_args.iter_mut() {
							self.monoize_type(types, arg, param_map);
						}

						self.monoize_call(functions_in, functions_out, stmt, types);
					}

					_ => {}
				}
			}
		}

		func
	}

	fn monoize_call(
		&self,
		functions_in: &CIRFnMap,
		functions_out: &mut CIRFnMap,
		func: &mut CIRStmt,
		types: &mut HashMap<TypeName, Arc<RwLock<TypeDef>>>,
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
			let mut insert_id = id.clone();

			for (i, type_arg) in type_args.iter().enumerate() {
				insert_id.type_params[i].2 = Some(type_arg.clone())
			}

			for (_, param) in &mut insert_id.params {
				self.monoize_type(types, param, type_args);
			}

			self.monoize_type(types, &mut insert_id.ret.1, type_args);

			if let (Some(qualifier), _) = &mut insert_id.name.qualifier {
				self.monoize_type(types, qualifier, type_args);
			}

			// If the function template isn't available yet, wait for it
			while !self.fn_templates.read().unwrap().contains_key(id) {
				std::thread::sleep(Duration::from_millis(1));
			}

			let fn_instances = self.fn_instances.read().unwrap();
			let fn_templates = self.fn_templates.read().unwrap();

			if !fn_instances.contains_key(&insert_id) {
				let Some(fn_in) = fn_templates.get(id) else {
					unreachable!()
				};

				drop(fn_instances);

				let monoized =
					self.monoize_function(functions_in, functions_out, fn_in, types, type_args);

				drop(fn_templates);

				let fn_instances = &mut *self.fn_instances.write().unwrap();

				fn_instances.insert(insert_id.clone(), monoized);
			}

			*id = insert_id;

			let extern_fn = self.fn_instances.read().unwrap()[id].clone();

			functions_out.insert(id.clone(), extern_fn);

			type_args.clear();
		}
	}

	fn monoize_rvalue_types(
		&self,
		types: &mut TypeMap,
		rval: &mut RValue,
		param_map: &TypeSubstitutions,
	) {
		match rval {
			RValue::Atom(ty, ..) => {
				self.monoize_type(types, ty, param_map);
			}

			RValue::Cons(ty, [(lty, _), (rty, _)], ..) => {
				self.monoize_type(types, lty, param_map);
				self.monoize_type(types, rty, param_map);

				self.monoize_type(types, ty, param_map);
			}

			RValue::Cast { from, to, .. } => {
				self.monoize_type(types, from, param_map);
				self.monoize_type(types, to, param_map);
			}
		}
	}

	fn monoize_type(&self, types: &mut TypeMap, ty: &mut Type, param_map: &TypeSubstitutions) {
		match ty {
			Type::Basic(_) => {}

			Type::Pointer { pointee, .. } => self.monoize_type(types, pointee, param_map),

			Type::Array(arr_ty, _) => self.monoize_type(types, arr_ty, param_map),

			Type::Slice(slicee) => self.monoize_type(types, slicee, param_map),

			Type::TypeRef { def, args } => {
				// If we're referring to a type with generics, check if the
				// instantation we want exists already. If not, create it.
				let def_up = def.upgrade().unwrap();
				let name = &def_up.read().unwrap().name;

				if !args.is_empty() {
					for arg in args.iter_mut() {
						self.monoize_type(types, arg, param_map);
					}

					let typename = name.to_string();
					
					*def = self.instantiate_type_def(types, def.upgrade().unwrap(), typename, args);
					args.clear();
				}
			}

			Type::TypeParam(idx) => {
				*ty = param_map[*idx].clone();
			}

			Type::Tuple(_, tuple_types) => {
				for ty in tuple_types {
					self.monoize_type(types, ty, param_map);
				}
			}

			Type::Function(ret, args) => {
				self.monoize_type(types, ret, param_map);

				for (_, arg) in args {
					self.monoize_type(types, arg, param_map);
				}
			}

			Type::Never => {}

			Type::Unresolved { .. } => panic!(),
		}
	}

	// Takes a Generic TypeDef with parameters and instantiates it.
	fn instantiate_type_def(
		&self,
		types: &mut TypeMap,
		def: Arc<RwLock<TypeDef>>,
		name: TypeName,
		param_map: &TypeSubstitutions,
	) -> Weak<RwLock<TypeDef>> {
		let mut instance = def.read().unwrap().clone();

		match &mut instance.def {
			TypeDefKind::Algebraic(AlgebraicDef {
				members, params, ..
			}) => {
				for (_, member, _) in members {
					self.monoize_type(types, member, param_map);
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

		// Check if the current module has this instance already
		
		if let Some(instance) = types.get(&insert_idx) {
			return Arc::downgrade(instance);
		}
		
		// Nope, check if the global instance map has it instead

		let global_types = self.ty_instances.read().unwrap();

		if let Some(instance) = global_types.get(&insert_idx) {
			types.insert(insert_idx, instance.clone());
			return Arc::downgrade(instance);
		}

		// Couldn't find this instance in the global map either, so store it

		*instance.name.path.last_mut().unwrap() = insert_idx.clone().into();

		drop(global_types);
		
		let global_types = &mut *self.ty_instances.write().unwrap();

		global_types.insert(insert_idx.clone(), Arc::new(RwLock::new(instance)));
		
		let instance = &global_types[&insert_idx];

		types.insert(insert_idx, instance.clone());

		Arc::downgrade(instance)
	}

	fn mangle(&self, module: &mut CIRModule) {
		// Mangle functions

		for (id, func) in &mut module.functions {
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
			let (ty, props, _) = &func.variables[i];

			if props.is_ref {
				result.push_str(&ty.ptr_type(props.is_mut).mangle())
			} else {
				result.push_str(&ty.mangle());
			}
		}
	}

	result
}

impl Type {
	fn mangle(&self) -> String {
		match self {
			Type::Basic(b) => String::from(b.mangle()),
			
			Type::Pointer { pointee, .. } => {
				if let Type::Slice(slicee) = &**pointee {
					String::from("P") + &slicee.mangle() + "y"
				} else {
					String::from("P") + &pointee.mangle()
				}
			}

			Type::TypeRef { .. } => String::from("S_"),
			
			Type::Function(ret, args) => {
				let mut result = String::from("PF");

				result.push_str(&ret.mangle());

				for (_, arg) in args {
					result.push_str(&arg.mangle())
				}

				result
			}

			Type::Slice(_) => panic!("encountered Type::Slice without indirection!"),

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

			Basic::Void => "v",
		}
	}
}
