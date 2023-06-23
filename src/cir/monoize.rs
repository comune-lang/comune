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
		types::{Basic, FloatSize, FnPrototype, IntSize, TypeDef},
	},
	lexer::Token,
};

use super::{
	builder::CIRModuleBuilder, CIRCallId, CIRFnMap, CIRFunction, CIRModule, CIRStmt, CIRTyMap,
	FuncID, RValue, Type, TypeName,
};

// A set of requested Generic monomorphizations, with a Vec of type arguments
// TODO: Extend system to support constants as arguments
type MonoizationList = HashSet<(Identifier, Vec<Type>)>;

type GenericArgs = Vec<Type>;

// Map from index + parameters to indices of existing instances
type TypeInstanceMap = HashMap<TypeName, HashMap<GenericArgs, TypeName>>;
type FuncInstanceMap = HashMap<FuncID, HashMap<GenericArgs, FuncID>>;
type TypeMap = HashMap<TypeName, Arc<RwLock<TypeDef>>>;

// The monomorphization server (MonomorphServer) stores the bodies of generic
// functions, so that they can be instantiated even after their modules of origin
// are done compiling.
pub struct MonomorphServer {
	fn_templates: RwLock<CIRFnMap>,
	fn_instances: RwLock<CIRFnMap>,
	ty_instances: RwLock<CIRTyMap>,
	fn_jobs: RwLock<HashSet<Arc<FnPrototype>>>,
}

impl MonomorphServer {
	pub fn new() -> Self {
		MonomorphServer {
			fn_templates: RwLock::default(),
			fn_instances: RwLock::default(),
			ty_instances: RwLock::default(),
			fn_jobs: RwLock::default(),
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
			.filter(|k| !module.functions[*k].generics.is_empty())
			.collect();

		for proto in generics {
			let fn_template = module.functions.remove(proto).unwrap();

			if !fn_template.is_extern {
				let mut fn_repo = self.fn_templates.write().unwrap();

				fn_repo.insert(proto.clone(), fn_template);
			}
		}

		for proto in function_protos {
			if !module.functions.contains_key(&proto) {
				// Generic function, we don't need to monomorphize this on its own
				continue;
			}

			let function_monoized = self.monoize_function(
				&module.functions[&proto],
				&mut module.types,
				&vec![],
				&module.functions,
				&mut functions_mono,
			);

			functions_mono.insert(proto, function_monoized);
		}

		let generic_ty_keys: Vec<_> = module
			.types
			.iter()
			.filter_map(|(k, v)| {
				let is_generic = !v.read().unwrap().params.is_empty();

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
		func: &CIRFunction,
		types: &mut HashMap<TypeName, Arc<RwLock<TypeDef>>>,
		param_map: &GenericArgs,
		fns_in: &CIRFnMap,
		fns_out: &mut CIRFnMap,
	) -> CIRFunction {
		let mut func = func.clone();

		for (i, gen_arg) in param_map.iter().enumerate() {
			func.generics[i].2 = Some(gen_arg.clone());
		}

		for (var, ..) in &mut func.variables {
			self.monoize_type(types, var, param_map, fns_in, fns_out);
		}

		self.monoize_type(types, &mut func.ret.1, param_map, fns_in, fns_out);

		for block in &mut func.blocks {
			for stmt in block.items.iter_mut() {
				if let CIRStmt::Assignment(_lval, _) = stmt {
					// TODO: Find RValues in LValue projection
				}

				match stmt {
					CIRStmt::Expression(expr) | CIRStmt::Assignment(_, expr) => {
						self.monoize_rvalue_types(types, expr, param_map, fns_in, fns_out);
					}

					CIRStmt::Invoke {
						id: CIRCallId::Direct(fn_id, _),
						generic_args,
						..
					}
					| CIRStmt::Call {
						id: CIRCallId::Direct(fn_id, _),
						generic_args,
						..
					} => {
						for arg in generic_args.iter_mut() {
							self.monoize_type(types, arg, param_map, fns_in, fns_out);
						}

						let mut id = fn_id.as_ref().clone();

						self.monoize_call(&mut id, generic_args, fns_in, fns_out, types);

						*fn_id = Arc::new(id);

						generic_args.clear();
					}

					_ => {}
				}
			}
		}

		func
	}

	fn monoize_call(
		&self,
		id: &mut FnPrototype,
		generic_args: &Vec<Type>,
		fns_in: &CIRFnMap,
		fns_out: &mut CIRFnMap,
		types: &mut HashMap<TypeName, Arc<RwLock<TypeDef>>>,
	) {
		if generic_args.is_empty() {
			return;
		}

		let mut insert_id = id.clone();

		for (i, type_arg) in generic_args.iter().enumerate() {
			insert_id.generics[i].2 = Some(type_arg.clone())
		}

		for (param, ..) in &mut insert_id.params.params {
			self.monoize_type(types, param, generic_args, fns_in, fns_out);
		}

		self.monoize_type(types, &mut insert_id.ret.1, generic_args, fns_in, fns_out);

		if let (Some(qualifier), _) = &mut insert_id.path.qualifier {
			self.monoize_type(types, qualifier, generic_args, fns_in, fns_out);
		}

		let insert_id = Arc::new(insert_id);

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

			let monoized = self.monoize_function(fn_in, types, generic_args, fns_in, fns_out);

			drop(fn_templates);

			let fn_instances = &mut *self.fn_instances.write().unwrap();

			fn_instances.insert(insert_id.clone(), monoized);
		}

		*id = insert_id.as_ref().clone();

		let extern_fn = self.fn_instances.read().unwrap()[id].clone();

		fns_out.insert(insert_id.clone(), extern_fn);
	}

	fn monoize_rvalue_types(
		&self,
		types: &mut TypeMap,
		rval: &mut RValue,
		param_map: &GenericArgs,
		fns_in: &CIRFnMap,
		fns_out: &mut CIRFnMap,
	) {
		match rval {
			RValue::Atom(ty, ..) => {
				self.monoize_type(types, ty, param_map, fns_in, fns_out);
			}

			RValue::Cons(ty, [(lty, _), (rty, _)], ..) => {
				self.monoize_type(types, lty, param_map, fns_in, fns_out);
				self.monoize_type(types, rty, param_map, fns_in, fns_out);

				self.monoize_type(types, ty, param_map, fns_in, fns_out);
			}

			RValue::Cast { from, to, .. } => {
				self.monoize_type(types, from, param_map, fns_in, fns_out);
				self.monoize_type(types, to, param_map, fns_in, fns_out);
			}
		}
	}

	fn monoize_type(
		&self,
		types: &mut TypeMap,
		ty: &mut Type,
		param_map: &GenericArgs,
		fns_in: &CIRFnMap,
		fns_out: &mut CIRFnMap,
	) {
		match ty {
			Type::Basic(_) => {}

			Type::Pointer { pointee, .. } => {
				self.monoize_type(types, pointee, param_map, fns_in, fns_out)
			}

			Type::Array(arr_ty, _) => self.monoize_type(types, arr_ty, param_map, fns_in, fns_out),

			Type::Slice(slicee) => self.monoize_type(types, slicee, param_map, fns_in, fns_out),

			Type::TypeRef { def, args } => {
				// If we're referring to a type with generics, check if the
				// instantation we want exists already. If not, create it.
				let def_up = def.upgrade().unwrap();
				let name = &def_up.read().unwrap().name;

				if !args.is_empty() {
					for arg in args.iter_mut() {
						self.monoize_type(types, arg, param_map, fns_in, fns_out);
					}

					let typename = name.to_string();

					*def = self.instantiate_type_def(
						types,
						def.upgrade().unwrap(),
						typename,
						args,
						fns_in,
						fns_out,
					);
					args.clear();
				}
			}

			Type::TypeParam(idx) => {
				*ty = param_map[*idx].clone();
			}

			Type::Tuple(_, tuple_types) => {
				for ty in tuple_types {
					self.monoize_type(types, ty, param_map, fns_in, fns_out);
				}
			}

			Type::Function(ret, args) => {
				self.monoize_type(types, ret, param_map, fns_in, fns_out);

				for (_, arg) in args {
					self.monoize_type(types, arg, param_map, fns_in, fns_out);
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
		generic_args: &GenericArgs,
		fns_in: &CIRFnMap,
		fns_out: &mut CIRFnMap,
	) -> Weak<RwLock<TypeDef>> {
		let mut instance = def.read().unwrap().clone();

		for (_, member, _) in &mut instance.members {
			self.monoize_type(types, member, generic_args, fns_in, fns_out);
		}

		instance.params.clear();

		let mut iter = generic_args.iter();
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

		*instance.name.path.last_mut().unwrap() = insert_idx.clone().into();

		if self.ty_instances.read().unwrap().contains_key(&insert_idx) {
			let instance_arc = self.ty_instances.read().unwrap()[&insert_idx].clone();

			types.insert(insert_idx.clone(), instance_arc.clone());

			Arc::downgrade(&instance_arc)
		} else {
			// Couldn't find this instance in the global map either, so register it
			let instance_arc = Arc::new(RwLock::new(instance));
			let mut instance_lock = instance_arc.write().unwrap();

			// Monoize dtor
			if let Some(drop_fn) = &instance_lock.drop {
				if let Some(drop_body) = fns_in.get(drop_fn) {
					self.register_fn_template(&drop_fn, drop_body);
				}

				let (drop_fn, drop_body) =
					self.register_fn_job(drop_fn.as_ref().clone(), &generic_args);

				fns_out.insert(drop_fn.clone(), drop_body);

				// this is really ugly. we have to go back and forth between
				// Arc<T> and Arc<RwLock<T>> a lot because of annoying reasons
				//
				// TODO: evaluate whether RwLock is still necessary here at all
				instance_lock.drop = Some(drop_fn);
			}

			self.ty_instances
				.write()
				.unwrap()
				.insert(insert_idx.clone(), instance_arc.clone());

			types.insert(insert_idx, instance_arc.clone());

			Arc::downgrade(&instance_arc)
		}
	}

	// Register a function template if it hasn't been registered already
	// which it.. technically never should? hm. i dunno let's just be safe
	fn register_fn_template(&self, func: &FnPrototype, body: &CIRFunction) {
		if self.fn_templates.read().unwrap().contains_key(func) {
			return;
		}

		self.fn_templates
			.write()
			.unwrap()
			.insert(Arc::new(func.clone()), body.clone());
	}

	// Request a function instance, returning an `extern` fn
	// and adding it to the MonomorphServer's job list
	fn register_fn_job(
		&self,
		mut func: FnPrototype,
		args: &GenericArgs,
	) -> (Arc<FnPrototype>, CIRFunction) {
		for (i, arg) in args.iter().enumerate() {
			func.generics[i].2 = Some(arg.clone())
		}

		let func = Arc::new(func);

		let extern_fn = CIRModuleBuilder::generate_prototype(&func);

		if self.fn_instances.read().unwrap().contains_key(&func)
			|| self.fn_jobs.read().unwrap().contains(&func)
		{
			// instance already exists, or job already registered?
			// then just return the extern fn
			(func, extern_fn)
		} else {
			self.fn_jobs.write().unwrap().insert(func.clone());
			(func, extern_fn)
		}
	}

	fn mangle(&self, module: &mut CIRModule) {
		// Mangle functions

		for (id, func) in &mut module.functions {
			// Check if the function has a `no_mangle` or `export_as` attribute, or if it's `main`. If not, mangle the name
			if get_attribute(&func.attributes, "no_mangle").is_some()
				|| (&**id.path.name() == "main" && !id.path.is_scoped())
			{
				func.mangled_name = Some(id.path.name().to_string());
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
				func.mangled_name = Some(mangle_name(&id.path, func));
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

		if let Some(ty_qualifier) = &name.qualifier.0 {
			let Type::TypeRef { def, .. } = &**ty_qualifier else {
				unimplemented!()
			};

			let def = def.upgrade().unwrap();
			let typename = &def.read().unwrap().name;

			for scope in &typename.path {
				result.push_str(&scope.len().to_string());
				result.push_str(scope);
			}
		}

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

	if !func.generics.is_empty() {
		result.push('I');

		for (.., ty) in &func.generics {
			let Some(ty) = ty else {
				panic!() // Can't have un-monomorphized generics at this point 
			};

			result.push_str(&ty.mangle());
		}

		result.push('E');
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

			Basic::Integral { signed, size } => {
				if *signed {
					match size {
						// FIXME: figure this out properly
						IntSize::IAddr => "x",

						IntSize::I64 => "x",
						IntSize::I32 => "i",
						IntSize::I16 => "s",
						IntSize::I8 => "c",
					}
				} else {
					match size {
						// FIXME: ditto
						IntSize::IAddr => "y",

						IntSize::I64 => "y",
						IntSize::I32 => "j",
						IntSize::I16 => "t",
						IntSize::I8 => "h",
					}
				}
			}

			Basic::Float { size } => match size {
				FloatSize::F64 => "d",
				FloatSize::F32 => "f",
			},

			Basic::Void => "v",
		}
	}
}
