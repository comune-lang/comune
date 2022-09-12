use std::{ffi::OsString, sync::Arc};

use colored::Colorize;
use inkwell::{context::Context, module::Module, passes::PassManager};

use crate::{parser::{errors::{CMNMessage, CMNError}, lexer::{Lexer, log_msg_at, log_msg, self}, Parser, semantic, namespace::{Namespace, NamespaceItem}, types::Type}, llvm::LLVMBackend};

pub struct ManagerState {
	import_paths: Vec<OsString>,
	working_dir: OsString,
	max_threads: usize,
	verbose_output: bool,
}

pub struct ModuleJobManager {
	state: Arc<ManagerState> // Read-only
}

pub struct ModuleCompileState {
	parser: Parser,
}


impl ModuleJobManager {
	pub fn new(working_dir: OsString, import_paths: Vec<OsString>, max_threads: usize, verbose_output: bool) -> Self {
		ModuleJobManager { 
			state: Arc::new(ManagerState {
				import_paths, 
				working_dir,
				max_threads,
				verbose_output,
			})
		}
	}
	
	pub fn parse_api(&self, module: OsString) -> Result<ModuleCompileState, CMNError> {
		// Okay, here's how we're going about this
		// Step 1a. Check if NamespaceInfo cache exists (Add this once modular compiling works in general lol)
		// Step 1b. Parse namespace level
		// Step 2. Resolve module imports, wait till done (this uses rayon)
		// Step 3. Return module compilation state, to be passed to resolve_types

		// Parse namespace level
		let mod_state = lexer::CURRENT_LEXER.with(|lexer| { 

			lexer.replace(match Lexer::new(module.clone()) { // TODO: Take module name instead of filename 
				Ok(f) => f,
				Err(e) => { println!("{} failed to open module '{}' ({})", "fatal:".red().bold(), module.to_string_lossy(), e); return Err(CMNError::ModuleNotFound(module)); }
			});


			let mut state = ModuleCompileState {
				parser: Parser::new(self.state.verbose_output)
			};

			println!("{} {}\n", "compiling".bold().green(), lexer.borrow().file_name.to_string_lossy());

			if self.state.verbose_output {
				println!("\ncollecting symbols...");
			}

			// Declarative pass
			return match state.parser.parse_module(false) {
				Ok(_) => { Ok(state) },
				Err(e) => { log_msg(CMNMessage::Error(e.clone())); Err(e) },
			};
		});

		mod_state
	}

	
	pub fn resolve_types(&self, mod_state: ModuleCompileState, context: &Context) -> Result<ModuleCompileState, CMNError> {
		// At this point, all imports have been resolved, so validate namespace-level types
		semantic::resolve_types(mod_state.parser.current_namespace(), mod_state.parser.current_namespace()).unwrap();
		
		if self.state.verbose_output {
			println!("\ntype resolution output:\n\n{}", mod_state.parser.current_namespace().borrow());
		}
	
		Ok(mod_state)
	}


	pub fn generate_code<'ctx>(&self, mut mod_state: ModuleCompileState, context: &'ctx Context) -> Result<LLVMBackend<'ctx>, CMNError> {
		


		// Generative pass
		// TODO: This completely re-tokenizes the module, which is useless
		// We oughta:
		// A) cache the tokenization in the first phase
		// B) store the relevant token sequences in the mod state to avoid redundant namespace parsing
		let namespace = match mod_state.parser.parse_module(true) {
			Ok(ctx) => { if self.state.verbose_output { println!("\nvalidating..."); } ctx },
			Err(e) => { log_msg(CMNMessage::Error(e.clone())); return Err(e); },
		};

		// Validate code
		match semantic::validate_namespace(namespace, namespace) {
			Ok(()) => {	if self.state.verbose_output { println!("generating code..."); } },
			Err(e) => { log_msg_at(e.1.0, e.1.1, CMNMessage::Error(e.0.clone())); return Err(e.0); },
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
		};


		// Generate LLVM IR

		// Register function prototypes
		self.register_namespace(&mut backend, &namespace.borrow(), None);
		self.compile_namespace(&mut backend, &namespace.borrow(), None);

		backend.generate_libc_bindings();


		if let Err(e) = backend.module.verify() {
			println!("an internal compiler error occurred:\n{}", e);
			
			// Output bogus LLVM here, for debugging purposes
			//if args.emit_llvm {
			//	backend.module.print_to_file(args.output_file.clone() + ".ll").unwrap();
			//}

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

		Ok(backend)
	}
	
	fn register_namespace(&self, backend: &mut LLVMBackend, namespace: &Namespace, root: Option<&Namespace>) {
		if root.is_some() {
			assert!(namespace as *const _ != root.unwrap() as *const _);
		}

		for child in &namespace.children {
			if let NamespaceItem::Namespace(namespace) = &child.1.0 {
				self.register_namespace(backend, &namespace.borrow(), root);
			}
		}
				

		for child in &namespace.children {
			if let NamespaceItem::Function(sym_type, _) = &child.1.0 {
				let name_mangled = namespace.get_mangled_name(&child.0);
				backend.register_fn(name_mangled, &sym_type.borrow()).unwrap();
			}
		}
	}


	fn compile_namespace(&self, backend: &mut LLVMBackend, namespace: &Namespace, root: Option<&Namespace>) {
		if root.is_some() {
			assert!(namespace as *const _ != root.unwrap() as *const _);
		}
		
		for child in &namespace.children {
			if let NamespaceItem::Namespace(namespace) = &child.1.0 {
				self.compile_namespace(backend, &namespace.borrow(), root);
			}
		}

		// Generate function bodies
		for child in &namespace.children {
			if let NamespaceItem::Function(sym_type, sym_elem) = &child.1.0 {
				backend.generate_fn(namespace.get_mangled_name(&child.0), &sym_type.borrow(), sym_elem).unwrap();
			}
		}
	}


	// This function attempts to load a cached NamespaceInfo from disk, or else attempts to find a module and
	// initialize its compilation, blocking until the NamespaceInfo is ready
	// The paths searched for the module are defined by `CompilerState::import_paths`,
	// Returns CMNError::ModuleNotFound if the module could not be found
	fn resolve_module_imports(&mut self, module_names: Vec<OsString>) -> Result<Vec<Namespace>, CMNMessage> {		
		rayon::scope(|s| {
			
		});

		Err(CMNMessage::Error(CMNError::ModuleNotFound(module_names.first().unwrap().clone())))
	}
}