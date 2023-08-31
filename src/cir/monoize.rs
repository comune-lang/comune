// cIR monomorphization module

use std::{
	collections::{HashMap, HashSet},
	sync::{Arc, RwLock, Weak},
};

use itertools::Itertools;

use crate::ast::{
	traits::ImplSolver,
	types::{
		FnPrototype, GenericArg, GenericArgs, TypeDef,
	},
};

use super::{
	builder::CIRModuleBuilder, CIRCallId, CIRFnMap, CIRFunction, CIRModule, CIRStmt, CIRTyMap,
	RValue, Type, LValue, PlaceElem, Operand,
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
		
		// Monomorphize non-generic types

		let types = module
			.types
			.values()
			.filter(|ty| ty.read().unwrap().generics.is_empty())
			.cloned()
			.collect_vec();

		for ty in types {
			let mut ty = ty.write().unwrap();
			
			self.monoize_typedef_body(
				&mut ty,
				&vec![],
				&mut ModuleAccess {
					types: &mut module.types,
					fns_in: &module.functions,
					fns_out: &mut functions_mono,
				}
			);
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
					CIRStmt::Assignment(lval, expr) => {
						self.monoize_lvalue(lval, param_map, access);
						self.monoize_rvalue_types(expr, param_map, access);
					}

					CIRStmt::Invoke {
						id: CIRCallId::Direct(func, _),
						generic_args,
						args,
						result,
						..
					}
					| CIRStmt::Call {
						id: CIRCallId::Direct(func, _),
						generic_args,
						args,
						result,
						..
					} => {
						if let Some(result) = result {
							self.monoize_lvalue(result, generic_args, access);
						}

						for arg in generic_args.iter_mut() {
							self.monoize_generic_arg(arg, param_map, access);
						}

						for (arg, ty, _) in args.iter_mut() {
							self.monoize_lvalue(arg, generic_args, access);
							self.monoize_type(ty, generic_args, access);
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
		generic_args: &GenericArgs,
		access: &mut ModuleAccess,
	) {
		match rval {
			RValue::Atom(ty, _, val, _) => {
				self.monoize_type(ty, generic_args, access);
				self.monoize_operand(val, generic_args, access);
			}

			RValue::Cons(ty, [(lty, lhs), (rty, rhs)], ..) => {
				self.monoize_type(lty, generic_args, access);
				self.monoize_type(rty, generic_args, access);
				self.monoize_operand(lhs, generic_args, access);
				self.monoize_operand(rhs, generic_args, access);

				self.monoize_type(ty, generic_args, access);
			}

			RValue::Cast { from, to, val, .. } => {
				self.monoize_type(from, generic_args, access);
				self.monoize_type(to, generic_args, access);
				self.monoize_operand(val, generic_args, access);
			}
		}
	}

	fn monoize_operand(&self, op: &mut Operand, generic_args: &GenericArgs, access: &mut ModuleAccess) {
		match op {
			Operand::LValueUse(lval, _) => self.monoize_lvalue(lval, generic_args, access),
			_ => {}
		}
	}

	fn monoize_lvalue(&self, lval: &mut LValue, generic_args: &GenericArgs, access: &mut ModuleAccess) {
		for proj in lval.projection.iter_mut() {
			match proj {
				PlaceElem::SumData(ty) => self.monoize_type(ty, generic_args, access),
				PlaceElem::Index { index_ty, .. } => self.monoize_type(index_ty, generic_args, access),
				_ => {}
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
						self.monoize_generic_arg(arg, generic_args, access);
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

			Type::Unresolved { .. } | Type::Infer(_) => panic!(),
		}
	}

	fn monoize_generic_arg(
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
		if generic_args.is_empty() {
			return Arc::downgrade(&def)
		}

		// Generate the monomorphized type name
		let mut ty_name = def.read().unwrap().name.clone();
		let mut iter = generic_args.iter();
		let mut instance_name = ty_name.path.last().unwrap().to_string();

		instance_name.push_str("<");
		instance_name.push_str(&iter.next().unwrap().to_string());

		for param in iter {
			instance_name.push_str(", ");
			instance_name.push_str(&param.to_string())
		}

		instance_name.push_str(">");

		*ty_name.path.last_mut().unwrap() = instance_name.as_str().into();

		let instance_name = ty_name.to_string();

		// Check if the current module has this instance already

		if let Some(instance) = access.types.get(&instance_name) {
			return Arc::downgrade(instance);
		}

		// Nope, check if the global instance map has it instead
		if self
			.ty_instances
			.read()
			.unwrap()
			.contains_key(&instance_name)
		{
			// This instantiation exists already, add it to the current module
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
			let instance_arc = Arc::new(RwLock::new(def.read().unwrap().clone()));
			let mut instance_lock = instance_arc.write().unwrap();

			instance_lock.name = ty_name.clone();

			self.ty_instances
				.write()
				.unwrap()
				.insert(instance_name.clone(), instance_arc.clone());

			access.types.insert(instance_name, instance_arc.clone());

			self.monoize_typedef_body(
				&mut instance_lock,
				generic_args,
				access
			);

			Arc::downgrade(&instance_arc)
		}
	}

	fn monoize_typedef_body(&self, ty: &mut TypeDef, generic_args: &GenericArgs, access: &mut ModuleAccess) {
		for (_, member, _) in &mut ty.members {
			self.monoize_type(member, generic_args, access);
		}

		for (_, variant) in &mut ty.variants {
			let variant_instance =
				self.instantiate_type_def(variant.clone(), generic_args, access);
			*variant = variant_instance.upgrade().unwrap();
		}

		if generic_args.is_empty() {
			return
		}

		ty.generics.params.clear();

		// Register and monoize dtor
		if let Some(drop) = &mut ty.drop {
			if let Some(template) = access.fns_in.get(drop) {
				self.register_fn_template(drop, template);
			}

			let (drop_fn, drop_body) = self.register_fn_job(drop, generic_args, access);

			access.fns_out.insert(drop_fn.clone(), drop_body);
		}

		// Register and monoize ctors
		for init in &mut ty.init {
			if let Some(template) = access.fns_in.get(init) {
				self.register_fn_template(init, template);
			}

			let (init_fn, init_body) = self.register_fn_job(init, generic_args, access);

			access.fns_out.insert(init_fn.clone(), init_body);
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
}