use std::{ffi::OsString, sync::Arc};

use colored::Colorize;

use crate::parser::{NamespaceInfo, errors::{CMNMessage, CMNError}, self, lexer::{Lexer, log_msg_at, log_msg}, Parser, semantic};


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



	pub fn continue_module_compilation(&self, mut mod_state: ModuleCompileState) {
		
		// Generative pass
		// TODO: This completely re-tokenizes the module, which is useless
		// We oughta:
		// A) cache the tokenization in the first phase
		// B) store the relevant token sequences in the mod state to avoid redundant namespace parsing
		let namespace = match mod_state.parser.parse_module(true) {
			Ok(ctx) => { if self.state.verbose_output { println!("\nresolving types..."); } ctx },
			Err(e) => { log_msg(CMNMessage::Error(e)); return; },
		};

		// Resolve types
		match semantic::parse_namespace(namespace) {
			Ok(()) => {	if self.state.verbose_output { println!("generating code..."); } },
			Err(e) => { log_msg_at(e.1.0, e.1.1, CMNMessage::Error(e.0)); return; },
		}
	}

	// This function attempts to load a cached NamespaceInfo from disk, or else attempts to find a module and
	// initialize its compilation, blocking until the NamespaceInfo is ready
	// The paths searched for the module are defined by `CompilerState::import_paths`,
	// Returns CMNError::ModuleNotFound if the module could not be found
	fn resolve_module_imports(&mut self, module_names: Vec<OsString>) -> Result<Vec<NamespaceInfo>, CMNMessage> {		
		rayon::scope(|s| {
			
		});

		Err(CMNMessage::Error(CMNError::ModuleNotFound(module_names.first().unwrap().clone())))
	}
}