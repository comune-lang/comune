// cIR monomorphization module

use std::{
	collections::{HashMap, HashSet},
	sync::{Arc, RwLock, Weak},
};

use crate::{
	ast::{
		get_attribute,
		module::Identifier,
		traits::ImplSolver,
		types::{
			Basic, FloatSize, FnPrototype, GenericArg, GenericArgs, GenericParam, IntSize, TypeDef,
		},
	},
	lexer::Token,
};

use super::{
	builder::CIRModuleBuilder, CIRCallId, CIRFnMap, CIRFunction, CIRModule, CIRStmt, CIRTyMap,
	RValue, Type,
};

// The monomorphization server (MonomorphServer) stores the bodies of generic
// functions, so that they can be instantiated even after their modules of origin
// are done compiling.
pub struct MonomorphServer {
	fn_templates: RwLock<CIRFnMap>,
	fn_instances: RwLock<CIRFnMap>,
	ty_instances: RwLock<CIRTyMap>,
	fn_jobs: RwLock<HashSet<(Arc<FnPrototype>, GenericArgs)>>,
}

pub struct ModuleAccess<'acc> {
	types: &'acc mut CIRTyMap,
	fns_in: &'acc CIRFnMap,
	fns_out: &'acc mut CIRFnMap,
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

	pub fn generate_fn_instances(&self) -> CIRModule {
		let mut module = CIRModule {
			types: HashMap::new(),
			globals: HashMap::new(),
			functions: HashMap::new(),
			impl_solver: ImplSolver::new(),
		};

		let mut fns_out = HashMap::new();

		loop {
			let mut access = ModuleAccess {
				types: &mut module.types,
				fns_in: &module.functions,
				fns_out: &mut fns_out,
			};

			let fn_jobs = self.fn_jobs.write().unwrap().clone();

			for (func, generic_args) in &fn_jobs {
				let template = &self.fn_templates.read().unwrap()[func];
				let func_monoized = self.monoize_function(template, generic_args, &mut access);
				let mut proto = func.as_ref().clone();

				self.monoize_prototype(&mut proto, generic_args, &mut access);

				access.fns_out.insert(Arc::new(proto), func_monoized);
			}

			module.functions.extend(fns_out.drain());

			self.fn_jobs
				.write()
				.unwrap()
				.retain(|job| !fn_jobs.contains(job));

			// if fn_jobs is empty, we're done monomorphizing
			if self.fn_jobs.read().unwrap().is_empty() {
				break;
			}
		}

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
				&vec![],
				&mut ModuleAccess {
					types: &mut module.types,
					fns_in: &module.functions,
					fns_out: &mut functions_mono,
				},
			);

			functions_mono.insert(proto, function_monoized);
		}

		// Remove all generic types from module
		module
			.types
			.retain(|_, ty| ty.read().unwrap().generics.params.is_empty());

		module.functions = functions_mono;
	}

	fn monoize_function(
		&self,
		func: &CIRFunction,
		param_map: &GenericArgs,
		access: &mut ModuleAccess,
	) -> CIRFunction {
		let mut func = func.clone();

		for (i, gen_arg) in param_map.iter().enumerate() {
			func.generics.params[i].1.fill_with(gen_arg);
		}

		for (var, ..) in &mut func.variables {
			self.monoize_type(var, param_map, access);
		}

		self.monoize_type(&mut func.ret.1, param_map, access);

		for block in &mut func.blocks {
			for stmt in block.items.iter_mut() {
				if let CIRStmt::Assignment(_lval, _) = stmt {
					// TODO: Find RValues in LValue projection
				}

				match stmt {
					CIRStmt::Expression(expr) | CIRStmt::Assignment(_, expr) => {
						self.monoize_rvalue_types(expr, param_map, access);
					}

					CIRStmt::Invoke {
						id: CIRCallId::Direct(func, _),
						generic_args,
						..
					}
					| CIRStmt::Call {
						id: CIRCallId::Direct(func, _),
						generic_args,
						..
					} => {
						for arg in generic_args.iter_mut() {
							self.monoiez_generic_arg(arg, param_map, access);
						}

						self.monoize_call(func, generic_args, access);

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
		id: &mut Arc<FnPrototype>,
		generic_args: &GenericArgs,
		access: &mut ModuleAccess,
	) {
		if generic_args.is_empty() {
			if !access.fns_in.contains_key(id) {
				let extern_fn = CIRModuleBuilder::generate_prototype(id);
				access.fns_out.insert(id.clone(), extern_fn);
			}

			return;
		}

		let (func, body) = self.register_fn_job(id, generic_args, access);

		*id = func.clone();

		if !access.fns_out.contains_key(&func) {
			access.fns_out.insert(func.clone(), body);
		}
	}

	fn monoize_rvalue_types(
		&self,
		rval: &mut RValue,
		param_map: &GenericArgs,
		access: &mut ModuleAccess,
	) {
		match rval {
			RValue::Atom(ty, ..) => {
				self.monoize_type(ty, param_map, access);
			}

			RValue::Cons(ty, [(lty, _), (rty, _)], ..) => {
				self.monoize_type(lty, param_map, access);
				self.monoize_type(rty, param_map, access);

				self.monoize_type(ty, param_map, access);
			}

			RValue::Cast { from, to, .. } => {
				self.monoize_type(from, param_map, access);
				self.monoize_type(to, param_map, access);
			}
		}
	}

	fn monoize_type(&self, ty: &mut Type, generic_args: &GenericArgs, access: &mut ModuleAccess) {
		match ty {
			Type::Basic(_) => {}

			Type::Pointer { pointee, .. } => self.monoize_type(pointee, generic_args, access),

			Type::Array(arr_ty, _) => self.monoize_type(arr_ty, generic_args, access),

			Type::Slice(slicee) => self.monoize_type(slicee, generic_args, access),

			Type::TypeRef { def, args } => {
				let def_up = def.upgrade().unwrap();

				if !args.is_empty() {
					// If we're referring to a type with generics, check if the
					// instantation we want exists already. If not, create it.

					for arg in args.iter_mut() {
						self.monoiez_generic_arg(arg, generic_args, access);
					}

					*def = self.instantiate_type_def(def_up.clone(), args, access);
					args.clear();
				} else {
					// Check if the type exists in the current module
					// (may not be true in the monomorphization module)
					let typename = def_up.read().unwrap().name.to_string();

					if !access.types.contains_key(&typename) {
						let def_lock = def_up.read().unwrap();

						// Register type and its xtors
						if let Some(drop) = &def_lock.drop {
							let extern_fn = CIRModuleBuilder::generate_prototype(drop);
							access.fns_out.insert(drop.clone(), extern_fn);
						}

						for init in &def_lock.init {
							let extern_fn = CIRModuleBuilder::generate_prototype(init);
							access.fns_out.insert(init.clone(), extern_fn);
						}

						drop(def_lock);

						access.types.insert(typename, def_up);
					}
				}
			}

			Type::TypeParam(idx) => {
				*ty = generic_args[*idx].get_type_arg().clone();
			}

			Type::Tuple(_, tuple_types) => {
				for ty in tuple_types {
					self.monoize_type(ty, generic_args, access);
				}
			}

			Type::Function(ret, args) => {
				self.monoize_type(ret, generic_args, access);

				for (_, arg) in args {
					self.monoize_type(arg, generic_args, access);
				}
			}

			Type::Never => {}

			Type::Unresolved { .. } => panic!(),
		}
	}

	fn monoiez_generic_arg(
		&self,
		arg: &mut GenericArg,
		generic_args: &GenericArgs,
		access: &mut ModuleAccess,
	) {
		match arg {
			GenericArg::Type(ty) => self.monoize_type(ty, generic_args, access),
		}
	}

	// Takes a Generic TypeDef with parameters and instantiates it.
	fn instantiate_type_def(
		&self,
		def: Arc<RwLock<TypeDef>>,
		generic_args: &GenericArgs,
		access: &mut ModuleAccess,
	) -> Weak<RwLock<TypeDef>> {
		let mut instance = def.read().unwrap().clone();

		for (_, member, _) in &mut instance.members {
			self.monoize_type(member, generic_args, access);
		}

		instance.generics.params.clear();

		let mut iter = generic_args.iter();
		let mut instance_name = instance.name.to_string() + "<" + &iter.next().unwrap().to_string();

		for param in iter {
			instance_name.push_str(&param.to_string())
		}

		instance_name += ">";

		// Check if the current module has this instance already

		if let Some(instance) = access.types.get(&instance_name) {
			return Arc::downgrade(instance);
		}

		// Nope, check if the global instance map has it instead

		*instance.name.path.last_mut().unwrap() = instance_name.clone().into();

		if self
			.ty_instances
			.read()
			.unwrap()
			.contains_key(&instance_name)
		{
			// This instantiation exists already, add it to the current module

			// We do this because otherwise we end up with "orphan" TypeDefs,
			// which aren't stored anywhere except the Weak<> Arcs in TypeRefs

			let instance_arc = self.ty_instances.read().unwrap()[&instance_name].clone();
			let instance_lock = instance_arc.read().unwrap();

			access
				.types
				.insert(instance_name.clone(), instance_arc.clone());

			// Register monoize job for dtor
			if let Some(drop) = &instance_lock.drop {
				if let Some(template) = access.fns_in.get(drop) {
					self.register_fn_template(drop, template);
				}

				let body = CIRModuleBuilder::generate_prototype(drop);

				access.fns_out.insert(drop.clone(), body);
			}

			// Ditto for any constructors
			for init in &instance_lock.init {
				if let Some(template) = access.fns_in.get(init) {
					self.register_fn_template(init, template);
				}

				let body = CIRModuleBuilder::generate_prototype(init);

				access.fns_out.insert(init.clone(), body);
			}

			Arc::downgrade(&instance_arc)
		} else {
			// Couldn't find this instance in the global map either, so register it
			let instance_arc = Arc::new(RwLock::new(instance));
			let mut instance_lock = instance_arc.write().unwrap();

			self.ty_instances
				.write()
				.unwrap()
				.insert(instance_name.clone(), instance_arc.clone());

			access.types.insert(instance_name, instance_arc.clone());

			// Register and monoize dtor
			if let Some(drop) = &mut instance_lock.drop {
				if let Some(template) = access.fns_in.get(drop) {
					self.register_fn_template(drop, template);
				}

				let (drop_fn, drop_body) = self.register_fn_job(drop, generic_args, access);

				access.fns_out.insert(drop_fn.clone(), drop_body);
			}

			// Register and monoize ctors
			for init in &mut instance_lock.init {
				if let Some(template) = access.fns_in.get(init) {
					self.register_fn_template(init, template);
				}

				let (init_fn, init_body) = self.register_fn_job(init, generic_args, access);

				access.fns_out.insert(init_fn.clone(), init_body);
			}

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

	fn monoize_prototype(
		&self,
		func: &mut FnPrototype,
		args: &GenericArgs,
		access: &mut ModuleAccess,
	) {
		func.generics.fill_with(args);

		for (param, ..) in &mut func.params.params {
			self.monoize_type(param, args, access);
		}

		self.monoize_type(&mut func.ret.1, args, access);

		if let (Some(qualifier), _) = &mut func.path.qualifier {
			self.monoize_type(qualifier, args, access);
		}
	}

	// Request a function instance, returning an `extern` fn
	// and adding it to the MonomorphServer's job list
	fn register_fn_job(
		&self,
		func: &mut Arc<FnPrototype>,
		args: &GenericArgs,
		access: &mut ModuleAccess,
	) -> (Arc<FnPrototype>, CIRFunction) {
		if args.is_empty() {
			panic!("can't register a monoize job for a non-generic function!");
		}

		let mut func_new = func.as_ref().clone();

		self.monoize_prototype(&mut func_new, args, access);

		let func_new = Arc::new(func_new);
		let extern_fn = CIRModuleBuilder::generate_prototype(&func_new);

		// very silly how much we have to clone here because &(T, U) != (&T, &U)
		if !self.fn_instances.read().unwrap().contains_key(&func_new)
			&& !self
				.fn_jobs
				.read()
				.unwrap()
				.contains(&(func.clone(), args.clone()))
		{
			self.fn_jobs
				.write()
				.unwrap()
				.insert((func.clone(), args.clone()));
		}

		*func = func_new.clone();
		(func_new, extern_fn)
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

		for (.., param) in &func.generics.params {
			let GenericParam::Type { arg: Some(ty), .. } = param else {
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
