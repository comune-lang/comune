use std::{ffi::{OsString, OsStr}, sync::{Arc, Mutex}, collections::HashMap, cell::RefCell, path::{PathBuf, Path}, fs};

use colored::Colorize;
use inkwell::{context::Context, targets::FileType};
use rayon::prelude::*;

use crate::{llvm::{self, LLVMBackend}, semantic::{namespace::{Identifier, Namespace, NamespaceItem, NamespaceASTElem}, self}, errors::{CMNError, CMNMessage}, lexer::Lexer, parser::{Parser, ASTResult}};


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


// This is only sound under the condition that Namespaces are ONLY modified by their owning Parsers. 
unsafe impl Send for Namespace {}

pub fn launch_module_compilation<'scope>(state: Arc<ManagerState>, input_module: Identifier, s: &rayon::Scope<'scope>) -> Result<Namespace, CMNError> {
	let src_path = get_module_source_path(&state, &input_module);
	let out_path = get_module_out_path(&state, &input_module, None);
	state.output_modules.lock().unwrap().push(out_path.clone());

	let mut mod_state = parse_interface(&state, &src_path).unwrap();

	// Resolve module imports
	let module_names = mod_state.parser.current_namespace().borrow().referenced_modules.clone();

	let imports = module_names.into_par_iter().map(|name| {
		let module_interface = launch_module_compilation(state.clone(), name.clone(), s);
		(name, module_interface.unwrap())
	}).collect();
	
	mod_state.parser.current_namespace().borrow_mut().imported = imports;

	resolve_types(&state, &mut mod_state).unwrap();

	let interface = mod_state.parser.current_namespace().borrow().clone();
	
	// The rest of the module's compilation happens in a worker thread
	
	s.spawn(move |_s| {
		let context = Context::create();

		let result = match generate_code(&state, &mut mod_state, &context) {
			Ok(res) => res,
			Err(_) => return, // TODO: Add some kind of global compilation result tracker
		};

		let target_machine = llvm::get_target_machine();

		if state.emit_llvm {
			let mut llvm_out_path = out_path.clone();
			llvm_out_path.set_extension("ll");
			result.module.print_to_file(llvm_out_path).unwrap();
		}

		target_machine.write_to_file(&result.module, FileType::Object, &out_path).unwrap();
		println!("{:>10} {}", "finished".bold().green(), out_path.file_name().unwrap().to_str().unwrap());
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


pub fn parse_interface(state: &Arc<ManagerState>, path: &Path) -> Result<ModuleState, CMNError> {

	// First phase of module compilation: create Lexer and Parser, and parse the module at the namespace level

	let mut mod_state = ModuleState {
		parser: Parser::new(match Lexer::new(path) { // TODO: Take module name instead of filename 
			Ok(f) => f,
			Err(e) => { 
				println!("{} failed to open module '{}' ({})", "fatal:".red().bold(), path.file_name().unwrap().to_string_lossy(), e); 
				return Err(CMNError::ModuleNotFound(OsString::from(path.file_name().unwrap()))); 
			}
		}, state.verbose_output),
	};

	println!("{:>10} {}", "compiling".bold().green(), mod_state.parser.lexer.borrow().file_name.to_string_lossy());

	if state.verbose_output {
		println!("\ncollecting symbols...");
	}

	// Parse namespace level

	return match mod_state.parser.parse_module() {
		Ok(_) => { Ok(mod_state) },
		Err(e) => { 
			mod_state.parser.lexer.borrow().log_msg(CMNMessage::Error(e.clone())); 
			Err(e) 
		},
	};

}


pub fn resolve_types(state: &Arc<ManagerState>, mod_state: &mut ModuleState) -> ASTResult<()> {
	// At this point, all imports have been resolved, so validate namespace-level types
	semantic::resolve_namespace_types(mod_state.parser.current_namespace(), mod_state.parser.current_namespace())?;

	// Check for cyclical dependencies without indirection
	// TODO: Nice error reporting for this
	semantic::check_namespace_cyclical_deps(&mod_state.parser.current_namespace().borrow())?;

	// Then register impls to their types
	semantic::register_impls(mod_state.parser.current_namespace(), mod_state.parser.current_namespace())?;

	// And then mangle names
	semantic::mangle_names(mod_state.parser.current_namespace())?;

	if state.verbose_output {
		println!("\ntype resolution output:\n\n{}", mod_state.parser.current_namespace().borrow());
	}

	Ok(())
}


pub fn generate_code<'ctx>(state: &Arc<ManagerState>, mod_state: &mut ModuleState, context: &'ctx Context) -> Result<LLVMBackend<'ctx>, CMNError> {
	
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
		loop_blocks: RefCell::new(vec![]),
	};

	for (_, import) in &namespace.borrow().imported {
		register_namespace(&mut backend, import, None);
	}
	
	// why is this here Twice
	//register_namespace(&mut backend, &namespace.borrow(), None);

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
	/*let mpm = PassManager::<Module>::create(());
	mpm.add_instruction_combining_pass();
	mpm.add_reassociate_pass();
	mpm.add_gvn_pass();
	mpm.add_cfg_simplification_pass();
	mpm.add_basic_alias_analysis_pass();
	mpm.add_promote_memory_to_register_pass();
	mpm.add_instruction_combining_pass();
	mpm.add_reassociate_pass();

	mpm.run_on(&backend.module);
	*/
	Ok(backend)
}


fn register_namespace(backend: &mut LLVMBackend, namespace: &Namespace, root: Option<&Namespace>) {
	if root.is_some() {
		assert!(namespace as *const _ != root.unwrap() as *const _);
	}

	// Register child namespaces
	for child in &namespace.children {
		match &child.1.0 {
			NamespaceItem::Namespace(namespace) => register_namespace(backend, &namespace.borrow(), root),

			NamespaceItem::Function(sym_type, _) => { backend.register_fn(child.1.2.as_ref().unwrap(), &sym_type.read().unwrap()).unwrap(); },
			
			_ => {},
		}
	}

	for im in &namespace.impls {
		for meth in im.1 {
			backend.register_fn(meth.3.as_ref().unwrap(), &meth.1.read().unwrap()).unwrap();
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

	for im in &namespace.impls {
		for method in im.1 {
			backend.generate_fn(
				method.3.as_ref().unwrap(), 
				&method.1.read().unwrap(), 
				if let NamespaceASTElem::Parsed(elem) = &*method.2.borrow() { Some(elem) } else { None }
			).unwrap();
		}
	}
}