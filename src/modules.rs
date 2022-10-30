use std::{
	ffi::{OsStr, OsString},
	fs,
	path::{Path, PathBuf},
	sync::{Arc, Mutex, mpsc::Sender},
};

use colored::Colorize;
use inkwell::{context::Context, module::Module, passes::PassManager, targets::FileType};
use rayon::prelude::*;

use crate::{
	cir::{
		analyze::{cleanup, verify, CIRPassManager, borrowck},
		builder::CIRModuleBuilder,
	},
	errors::{CMNError, CMNErrorCode, CMNMessage, CMNErrorLog},
	lexer::Lexer,
	llvm::{self, LLVMBackend},
	parser::{ASTResult, Parser},
	semantic::{
		self,
		namespace::{Identifier, Namespace},
	},
};

pub struct ManagerState {
	pub library_dir: OsString,
	pub import_paths: Vec<OsString>,
	pub working_dir: OsString,
	pub max_threads: usize,
	pub verbose_output: bool,
	pub output_modules: Mutex<Vec<PathBuf>>,
	pub emit_llvm: bool,
	pub backtrace_on_error: bool,
}

pub struct ModuleState {
	pub parser: Parser,
}

// This is only sound under the condition that Namespaces are ONLY modified by their owning Parsers.
unsafe impl Send for Namespace {}

pub fn launch_module_compilation<'scope>(
	state: Arc<ManagerState>,
	input_module: Identifier,
	error_sender: Sender<CMNErrorLog>,
	s: &rayon::Scope<'scope>,
) -> Result<Namespace, CMNError> {
	let src_path = get_module_source_path(&state, &input_module);
	let out_path = get_module_out_path(&state, &input_module, None);
	state.output_modules.lock().unwrap().push(out_path.clone());

	let mut mod_state = parse_interface(&state, &src_path, error_sender.clone())?;

	// Resolve module imports
	let module_names = mod_state
		.parser
		.current_namespace()
		.borrow()
		.referenced_modules
		.clone();
	
	let sender_lock = Mutex::new(error_sender);

	let imports = module_names
		.into_par_iter()
		.map(|name| {
			let error_sender = sender_lock.lock().unwrap().clone();
			let module_interface = launch_module_compilation(state.clone(), name.clone(), error_sender, s);
			(name, module_interface.unwrap())
		})
		.collect();

	mod_state.parser.current_namespace().borrow_mut().imported = imports;

	resolve_types(&state, &mut mod_state).unwrap();

	let interface = mod_state.parser.current_namespace().borrow().clone();

	// The rest of the module's compilation happens in a worker thread

	s.spawn(move |_s| {
		let context = Context::create();

		let result = match generate_code(&state, &mut mod_state, &context, &input_module) {
			Ok(res) => res,
			Err(_) => return,
		};

		let target_machine = llvm::get_target_machine();

		if state.emit_llvm {
			let mut llvm_out_path = out_path.clone();
			llvm_out_path.set_extension("ll");
			result.module.print_to_file(llvm_out_path).unwrap();
		}

		target_machine
			.write_to_file(&result.module, FileType::Object, &out_path)
			.unwrap();

		println!(
			"{:>10} {}",
			"finished".bold().green(),
			out_path.file_name().unwrap().to_str().unwrap()
		);
	});

	Ok(interface)
}

// TODO: Add proper module searching support, based on a list of module search dirs, as well as support for .cmn, .h, .hpp etc
pub fn get_module_source_path(state: &Arc<ManagerState>, module: &Identifier) -> PathBuf {
	let mut result = get_src_folder(state);

	fs::create_dir_all(result.clone()).unwrap();

	result.push(&**module.name());
	result.set_extension("cmn");
	result
}

pub fn get_module_out_path(
	state: &Arc<ManagerState>,
	module: &Identifier,
	dependency_name: Option<&OsStr>,
) -> PathBuf {
	let mut result = get_out_folder(state);

	if let Some(dep) = dependency_name {
		result.push("deps");
		result.push(dep);
	} else {
		result.push("modules");
	}

	fs::create_dir_all(result.clone()).unwrap();

	result.push(&**module.name());
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

pub fn parse_interface(state: &Arc<ManagerState>, path: &Path, error_sender: Sender<CMNErrorLog>) -> Result<ModuleState, CMNError> {
	// First phase of module compilation: create Lexer and Parser, and parse the module at the namespace level

	let mut mod_state = ModuleState {
		parser: Parser::new(
			match Lexer::new(path, error_sender) {
				// TODO: Take module name instead of filename
				Ok(f) => f,
				Err(e) => {
					println!(
						"{} failed to open module '{}' ({})",
						"fatal:".red().bold(),
						path.file_name().unwrap().to_string_lossy(),
						e
					);
					return Err(CMNError::new(CMNErrorCode::ModuleNotFound(OsString::from(
						path.file_name().unwrap(),
					))));
				}
			},
			state.verbose_output,
		),
	};

	println!(
		"{:>10} {}",
		"compiling".bold().green(),
		mod_state.parser.lexer.borrow().file_name.to_string_lossy()
	);

	if state.verbose_output {
		println!("\ncollecting symbols...");
	}

	// Parse namespace level

	return match mod_state.parser.parse_module() {
		Ok(_) => Ok(mod_state),
		Err(e) => {
			mod_state
				.parser
				.lexer
				.borrow()
				.log_msg(CMNMessage::Error(e.clone()));
			Err(e)
		}
	};
}

pub fn resolve_types(state: &Arc<ManagerState>, mod_state: &mut ModuleState) -> ASTResult<()> {
	let root = mod_state.parser.current_namespace();

	// At this point, all imports have been resolved, so validate namespace-level types
	semantic::resolve_namespace_types(root, root)?;

	// Check for cyclical dependencies without indirection
	// TODO: Nice error reporting for this
	semantic::check_namespace_cyclical_deps(&root.borrow())?;

	// Then register impls to their types
	semantic::register_impls(root, root)?;

	if state.verbose_output {
		println!("\ntype resolution output:\n\n{}", root.borrow());
	}

	Ok(())
}

pub fn generate_code<'ctx>(
	state: &Arc<ManagerState>,
	mod_state: &mut ModuleState,
	context: &'ctx Context,
	input_module: &Identifier,
) -> Result<LLVMBackend<'ctx>, CMNError> {
	// Generate AST

	match mod_state.parser.generate_ast() {
		Ok(()) => {
			if state.verbose_output {
				println!("\nvalidating...");
			}
		}
		Err(e) => {
			mod_state
				.parser
				.lexer
				.borrow()
				.log_msg(CMNMessage::Error(e.clone()));
			return Err(e);
		}
	};

	// Validate code

	match semantic::validate_namespace(
		mod_state.parser.current_namespace(),
		mod_state.parser.current_namespace(),
	) {
		Ok(()) => {
			if state.verbose_output {
				println!("generating code...");
			}
		}
		Err(e) => {
			mod_state.parser.lexer.borrow().log_msg_at(
				e.1 .0,
				e.1 .1,
				CMNMessage::Error(e.0.clone()),
			);
			return Err(e.0);
		}
	}

	// Generate cIR

	let module_name = input_module.to_string();
	let mut cir_module = CIRModuleBuilder::from_ast(mod_state).module;

	// Analyze & optimize cIR
	let mut cir_man = CIRPassManager::new();
	cir_man.add_pass(verify::Verify);
	cir_man.add_mut_pass(cleanup::RemoveNoOps);
	cir_man.add_mut_pass(borrowck::BorrowCheck);
	cir_man.add_pass(verify::Verify);
	cir_man.run_on_module(&mut cir_module);

	// Write cIR to file
	fs::write(
		get_module_out_path(&state, input_module, None).with_extension("cir"),
		cir_module.to_string(),
	)
	.unwrap();

	// Generate LLVM IR
	let mut backend = LLVMBackend::new(context, &module_name);
	let module_mono = cir_module.monoize();

	backend.compile_module(&module_mono).unwrap();
	backend.generate_libc_bindings();

	if let Err(e) = backend.module.verify() {
		println!("an internal compiler error occurred:\n{}", e.to_string());

		// Output bogus LLVM here, for debugging purposes
		backend.module.print_to_file("bogus.ll").unwrap();

		return Err(CMNError::new(CMNErrorCode::LLVMError));
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
