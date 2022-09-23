use std::{ffi::{OsString, OsStr}, sync::{Arc, Mutex}, collections::HashMap, cell::RefCell, path::{PathBuf, Path}, fs};

use colored::Colorize;
use inkwell::{context::Context, module::{Module}, passes::PassManager, targets::FileType};

use crate::{llvm::{self, LLVMBackend}, semantic::{namespace::{Identifier, Namespace, NamespaceItem, NamespaceASTElem}, self}, errors::{CMNError, CMNMessage}, lexer::Lexer, parser::Parser};


pub struct ManagerState {
	pub import_paths: Vec<OsString>,
	pub working_dir: OsString,
	pub max_threads: usize,
	pub verbose_output: bool,
	pub output_modules: Mutex<Vec<PathBuf>>,
	pub emit_llvm: bool,
}


pub struct ModuleState {
	parser: Parser,
}


// I'm a bit iffy on this. This is safe IF and ONLY IF all the `Rc`s and `RefCell`s are referenced INSIDE ModuleState.
// TODO: Verify that's the case.
unsafe impl Send for ModuleState {}


pub fn launch_module_compilation<'scope>(state: Arc<ManagerState>, input_module: Identifier, s: &rayon::Scope<'scope>) -> Result<Namespace, CMNError> {
	let src_path = get_module_source_path(&state, &input_module);
	let out_path = get_module_out_path(&state, &input_module, None);
	state.output_modules.lock().unwrap().push(out_path.clone());

	let mut mod_state = parse_api(&state, &src_path).unwrap();

	// Resolve module imports
	let module_names = mod_state.parser.current_namespace().borrow().referenced_modules.clone();
	let mut imports = HashMap::new();

	for name in module_names {
		let module_interface = launch_module_compilation(state.clone(), name.clone(), s);
		imports.insert(name, module_interface?);
	}
	
	mod_state.parser.current_namespace().borrow_mut().imported = imports;

	resolve_types(&state, &mut mod_state).unwrap();

	let interface = mod_state.parser.current_namespace().borrow().clone();

	s.spawn(move |_s| {
		let context = Context::create();
		let result = generate_code(&state, mod_state, &context).unwrap();
		let target_machine = llvm::get_target_machine();

		if state.emit_llvm {
			let mut llvm_out_path = out_path.clone();
			llvm_out_path.set_extension("ll");
			result.1.module.print_to_file(llvm_out_path).unwrap();
		}

		target_machine.write_to_file(&result.1.module, FileType::Object, &out_path).unwrap();
	});


	Ok(interface)
}


// TODO: Add proper module searching support, based on a list of module search dirs, as well as support for .cmn, .h, .hpp etc 
pub fn get_module_source_path(state: &Arc<ManagerState>, module: &Identifier) -> PathBuf {
	let mut result = get_src_folder(state);
	
	fs::create_dir_all(result.clone()).unwrap();
	
	result.push(&module.name);
	result.set_extension("cmn");
	result
}


pub fn get_module_out_path(state: &Arc<ManagerState>, module: &Identifier, dependency_name: Option<&OsStr>) -> PathBuf {
	let mut result = get_out_folder(state);
	
	if let Some(dep) = dependency_name {
		result.push("deps");
		result.push(dep);
	} else {
		result.push("modules");
	}

	fs::create_dir_all(result.clone()).unwrap();
	
	result.push(&module.name);
	result.set_extension("o");
	result
}


pub fn get_src_folder(state: &Arc<ManagerState>) -> PathBuf {
	let mut result = PathBuf::from(&state.working_dir);
	result.push("src");
	result
}


pub fn get_out_folder(state: &Arc<ManagerState>) -> PathBuf {
	let mut result = PathBuf::from(&state.working_dir);
	result.push("build");
	result
}


pub fn parse_api(state: &Arc<ManagerState>, path: &Path) -> Result<ModuleState, CMNError> {
	// Okay, here's how we're going about this
	// Step 1a. Check if NamespaceInfo cache exists (Add this once modular compiling works in general lol)
	// Step 1b. Parse namespace level
	// Step 2. Resolve module imports, wait till done (this uses rayon)
	// Step 3. Return module compilation state, to be passed to resolve_types

	// Parse namespace level
	let mut mod_state = ModuleState {
		parser: Parser::new(match Lexer::new(path) { // TODO: Take module name instead of filename 
			Ok(f) => f,
			Err(e) => { 
				println!("{} failed to open module '{}' ({})", "fatal:".red().bold(), path.file_name().unwrap().to_string_lossy(), e); 
				return Err(CMNError::ModuleNotFound(OsString::from(path.file_name().unwrap()))); 
			}
		}, state.verbose_output),
	};

	println!("{} {}", "compiling".bold().green(), mod_state.parser.lexer.borrow().file_name.to_string_lossy());

	if state.verbose_output {
		println!("\ncollecting symbols...");
	}

	// Declarative pass
	return match mod_state.parser.parse_module() {
		Ok(_) => { Ok(mod_state) },
		Err(e) => { 
			mod_state.parser.lexer.borrow().log_msg(CMNMessage::Error(e.clone())); 
			Err(e) 
		},
	};

}


pub fn resolve_types(state: &Arc<ManagerState>, mod_state: &mut ModuleState) -> Result<(), CMNError> {
	// At this point, all imports have been resolved, so validate namespace-level types
	semantic::resolve_namespace_types(mod_state.parser.current_namespace(), mod_state.parser.current_namespace()).unwrap();
	// Check for cyclical dependencies without indirection
	// TODO: Nice error reporting for this
	semantic::check_namespace_cyclical_deps(&mod_state.parser.current_namespace().borrow()).unwrap();
	// And then mangle names
	semantic::mangle_names(mod_state.parser.current_namespace()).unwrap();

	if state.verbose_output {
		println!("\ntype resolution output:\n\n{}", mod_state.parser.current_namespace().borrow());
	}

	Ok(())
}


pub fn generate_code<'ctx>(state: &Arc<ManagerState>, mut mod_state: ModuleState, context: &'ctx Context) -> Result<(ModuleState, LLVMBackend<'ctx>), CMNError> {
	// Generate AST
	let namespace = match mod_state.parser.generate_ast() {
		Ok(ctx) => { if state.verbose_output { println!("\nvalidating..."); } ctx },
		Err(e) => {
			mod_state.parser.lexer.borrow().log_msg(CMNMessage::Error(e.clone())); 
			return Err(e); 
		},
	};

	// Validate code
	match semantic::validate_namespace(namespace, namespace) {
		Ok(()) => {	if state.verbose_output { println!("generating code..."); } },
		Err(e) => { 
			mod_state.parser.lexer.borrow().log_msg_at(e.1.0, e.1.1, CMNMessage::Error(e.0.clone())); 
			return Err(e.0); 
		},
	}

	// Generate code
	let module = context.create_module("test");
	let builder = context.create_builder();

	let mut backend = LLVMBackend {
		context,
		module,
		builder,
		fpm: None,
		fn_value_opt: None,
		type_map: RefCell::new(HashMap::new()),
	};

	for (_, import) in &namespace.borrow().imported {
		register_namespace(&mut backend, import, None);
	}

	register_namespace(&mut backend, &namespace.borrow(), None);

	// Generate LLVM IR
	register_namespace(&mut backend, &namespace.borrow(), None);
	compile_namespace(&mut backend, &namespace.borrow(), None);

	backend.generate_libc_bindings();

	if let Err(e) = backend.module.verify() {
		println!("an internal compiler error occurred:\n{}", e.to_string());
		
		// Output bogus LLVM here, for debugging purposes
		backend.module.print_to_file("bogus.ll").unwrap();

		return Err(CMNError::LLVMError);
	};
	
	// Optimization passes
	let mpm = PassManager::<Module>::create(());
	mpm.add_instruction_combining_pass();
	mpm.add_reassociate_pass();
	mpm.add_gvn_pass();
	mpm.add_cfg_simplification_pass();
	mpm.add_basic_alias_analysis_pass();
	mpm.add_promote_memory_to_register_pass();
	mpm.add_instruction_combining_pass();
	mpm.add_reassociate_pass();

	mpm.run_on(&backend.module);

	Ok((mod_state, backend))
}



// This function attempts to load a cached NamespaceInfo from disk, or else attempts to find a module and
// initialize its compilation, blocking until the NamespaceInfo is ready
// The paths searched for the module are defined by `CompilerState::import_paths`,
// Returns CMNError::ModuleNotFound if the module could not be found
/*pub fn resolve_module_imports(state: Arc<ManagerState>, mod_state: &mut ModuleState, s: &rayon::Scope) -> Result<Namespace, CMNError> {
	let module_names = mod_state.parser.current_namespace().borrow().referenced_modules.clone();
	
	rayon::scope(move |t| {
		for module in module_names.clone().into_iter() {
			// Launch compilation of child module
			let state_clone = state.clone();

			let mut mod_state = parse_api(&state, &OsString::from(module)).unwrap();
			let imports = resolve_module_imports(state_clone.clone(), &mut mod_state, t).unwrap();

			s.spawn(move |s| {
				let context = Context::create();
				resolve_types(&state_clone, &mut mod_state, &context).unwrap();
				let result = generate_code(&state_clone, mod_state, &context).unwrap();
			});
		}
	});
	

	Err(CMNError::Other) // TODO: Create error for this
}*/



fn register_namespace(backend: &mut LLVMBackend, namespace: &Namespace, root: Option<&Namespace>) {
	if root.is_some() {
		assert!(namespace as *const _ != root.unwrap() as *const _);
	}

	for child in &namespace.children {
		if let NamespaceItem::Namespace(namespace) = &child.1.0 {
			register_namespace(backend, &namespace.borrow(), root);
		}
	}
	
	for child in &namespace.children {
		if let NamespaceItem::Function(sym_type, _) = &child.1.0 {
			backend.register_fn(child.1.2.as_ref().unwrap(), &sym_type.read().unwrap()).unwrap();
		}
	}
}


fn compile_namespace(backend: &mut LLVMBackend, namespace: &Namespace, root: Option<&Namespace>) {
	if root.is_some() {
		assert!(namespace as *const _ != root.unwrap() as *const _);
	}
	
	for child in &namespace.children {
		if let NamespaceItem::Namespace(namespace) = &child.1.0 {
			compile_namespace(backend, &namespace.borrow(), root);
		}
	}

	// Generate function bodies
	for child in &namespace.children {
		if let NamespaceItem::Function(sym_type, sym_elem) = &child.1.0 {
			backend.generate_fn(
				child.1.2.as_ref().unwrap(), 
				&sym_type.read().unwrap(), 
				if let NamespaceASTElem::Parsed(elem) = &*sym_elem.borrow() { Some(elem) } else { None }
			).unwrap();
		}
	}
}