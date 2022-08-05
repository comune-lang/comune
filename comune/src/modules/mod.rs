use std::{ffi::OsString, sync::Arc, cell::RefCell};

use colored::Colorize;
use inkwell::{context::Context, module::Module, passes::PassManager};

use crate::{parser::{errors::{CMNMessage, CMNError}, self, lexer::{Lexer, log_msg_at, log_msg}, Parser, semantic, namespace::Namespace}, backend::llvm::LLVMBackend};

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
	
	pub fn start_module_compilation(&self, module: OsString) -> Result<ModuleCompileState, CMNError> {
		// Okay, here's how we're going about this
		// Step 1a. Check if NamespaceInfo cache exists (Add this once modular compiling works in general lol)
		// Step 1b. Parse namespace level
		// Step 2. Resolve module imports, wait till done (this uses rayon)
		// Step 3. Return module compilation state, to be passed to continue_module_compilation

		// Parse namespace level
		let mod_state = parser::lexer::CURRENT_LEXER.with(|lexer| { 

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
				Err(e) => { Err(e) },
			};
		});

		mod_state
	}



	pub fn continue_module_compilation<'ctx>(&self, mut mod_state: ModuleCompileState, context: &'ctx Context) -> Result<LLVMBackend<'ctx>, CMNError> {
		
		// Generative pass
		// TODO: This completely re-tokenizes the module, which is useless
		// We oughta:
		// A) cache the tokenization in the first phase
		// B) store the relevant token sequences in the mod state to avoid redundant namespace parsing
		let namespace = match mod_state.parser.parse_module(true) {
			Ok(ctx) => { if self.state.verbose_output { println!("\nresolving types..."); } ctx },
			Err(e) => { log_msg(CMNMessage::Error(e.clone())); return Err(e); },
		};

		// Resolve types
		match semantic::parse_namespace(namespace) {
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
		self.register_namespace(&mut backend, &namespace.borrow());
		self.compile_namespace(&mut backend, &namespace.borrow());

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
	
	fn register_namespace(&self, backend: &mut LLVMBackend, namespace: &Namespace) {
		for child in namespace.parsed_children.iter() {
			self.register_namespace(backend, child.1);
		}

		for (sym_name, (sym_type, _, attributes)) in &namespace.symbols {
			let name_mangled = namespace.get_mangled_name(sym_name, attributes);
			println!("registering {}", name_mangled);
			backend.register_fn(name_mangled, sym_type).unwrap();
		}

		
	}

	fn compile_namespace(&self, backend: &mut LLVMBackend, namespace: &Namespace) {
		for child in namespace.parsed_children.iter() {
			self.compile_namespace(backend, child.1);
		}
		// Generate function bodies
		for (sym_name, (sym_type, sym_elem, attributes)) in &namespace.symbols {
			backend.generate_fn(namespace.get_mangled_name(sym_name, attributes), sym_type, sym_elem).unwrap();
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