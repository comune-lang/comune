use std::{
	collections::HashMap,
	ffi::OsString,
	fs,
	path::{Path, PathBuf},
	sync::{mpsc::Sender, Arc, Mutex, RwLock},
};

use colored::Colorize;
use inkwell::{context::Context, passes::PassManager, targets::FileType};

use crate::{
	ast::{
		self,
		module::{Identifier, ModuleImportKind, ModuleInterface, ModuleInterfaceOpaque},
	},
	cir::{
		analyze::{lifeline::VarInitCheck, verify, CIRPassManager, DataFlowPass, cleanup},
		builder::CIRModuleBuilder,
	},
	errors::{CMNMessageLog, ComuneErrCode, ComuneError, ComuneMessage},
	lexer::{self, Lexer, SrcSpan},
	llvm::{self, LLVMBackend},
	parser::{ComuneResult, Parser},
};

pub struct ManagerState {
	pub libcomune_dir: OsString,
	pub import_paths: Vec<OsString>,
	pub max_threads: usize,
	pub verbose_output: bool,
	pub output_modules: Mutex<Vec<PathBuf>>,
	pub output_dir: OsString,
	pub emit_types: Vec<EmitType>,
	pub backtrace_on_error: bool,
	pub module_states: RwLock<HashMap<PathBuf, ModuleState>>,
}

#[derive(Clone)]
pub enum ModuleState {
	Parsing,
	ParsingFailed,
	InterfaceUntyped(ModuleInterfaceOpaque),
	InterfaceComplete(Arc<ModuleInterface>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EmitType {
	DynamicLib,
	StaticLib,
	Binary,
	Object,
	ComuneIr,
	ComuneIrMono,
	LLVMIrRaw,
	LLVMIr,
}

impl EmitType {
	pub fn from_string(string: &str) -> Option<Self> {
		match string {
			"bin" => Some(EmitType::Binary),
			"dylib" => Some(EmitType::DynamicLib),
			"lib" => Some(EmitType::StaticLib),
			"obj" => Some(EmitType::Object),
			"cir" => Some(EmitType::ComuneIr),
			"cirmono" => Some(EmitType::ComuneIrMono),
			"llraw" => Some(EmitType::LLVMIrRaw),
			"ll" => Some(EmitType::LLVMIr),
			_ => None,
		}
	}
}

pub fn launch_module_compilation(
	state: Arc<ManagerState>,
	src_path: PathBuf,
	module_name: Identifier,
	error_sender: Sender<CMNMessageLog>,
	s: &rayon::Scope,
) -> Result<(), ComuneError> {
	if state.module_states.read().unwrap().contains_key(&src_path) {
		return Ok(());
	}

	let out_path = get_module_out_path(&state, &module_name);

	state.output_modules.lock().unwrap().push(out_path.clone());

	state
		.module_states
		.write()
		.unwrap()
		.insert(src_path.clone(), ModuleState::Parsing);

	let mut parser = match parse_interface(&state, &src_path, error_sender.clone()) {
		Ok(parser) => parser,

		Err(e) => {
			state
				.module_states
				.write()
				.unwrap()
				.insert(src_path, ModuleState::ParsingFailed);
			return Err(e);
		}
	};

	state.module_states.write().unwrap().insert(
		src_path.clone(),
		ModuleState::InterfaceUntyped(parser.interface.get_opaque()),
	);

	// Resolve module imports
	let mut module_names: Vec<_> = parser.interface.import_names.clone().into_iter().collect();
	let sender_lock = Mutex::new(error_sender.clone());

	let mut imports = HashMap::new();

	while let Some(name) = module_names.first().cloned() {
		let (import_name, fs_name) = match name {
			ModuleImportKind::Child(name) => {
				(name.clone(), Identifier::from_parent(&module_name, name))
			}
			ModuleImportKind::Language(name) => (name.clone(), Identifier::from_name(name, true)),
			ModuleImportKind::Extern(name) => (name.name().clone(), name),
		};

		let import_path = get_module_source_path(&state, src_path.clone(), &fs_name).unwrap();

		let error_sender = sender_lock.lock().unwrap().clone();

		// Query module interface, blocking this thread until it's ready
		loop {
			let import_state = state
				.module_states
				.read()
				.unwrap()
				.get(&import_path)
				.cloned();
			match import_state {
				None => launch_module_compilation(
					state.clone(),
					import_path.clone(),
					fs_name.clone(),
					error_sender.clone(),
					s,
				)?,

				// Sleep for some short duration, so we don't hog the CPU
				Some(ModuleState::Parsing) => {
					std::thread::sleep(std::time::Duration::from_millis(1))
				}

				Some(ModuleState::ParsingFailed) => {
					state
						.module_states
						.write()
						.unwrap()
						.insert(src_path.clone(), ModuleState::ParsingFailed);

					return Err(ComuneError::new(
						ComuneErrCode::DependencyError,
						SrcSpan::new(),
					));
				}

				Some(ModuleState::InterfaceUntyped(interface)) => {
					imports.insert(import_name, interface.clone());
					module_names.remove(0);
					break;
				}

				Some(ModuleState::InterfaceComplete(interface)) => {
					imports.insert(import_name, interface.get_opaque());
					module_names.remove(0);
					break;
				}
			}
		}
	}

	// Return early if any import failed
	parser.imports_opaque = imports;

	match resolve_types(&state, &mut parser) {
		Ok(_) => {}
		Err(e) => {
			parser
				.lexer
				.borrow()
				.log_msg_at(SrcSpan::new(), ComuneMessage::Error(e.clone()));

			state
				.module_states
				.write()
				.unwrap()
				.insert(src_path.clone(), ModuleState::ParsingFailed);

			return Err(e);
		}
	};

	// Update the module database with the fully-typed version of the interface

	state.module_states.write().unwrap().insert(
		src_path.clone(),
		ModuleState::InterfaceComplete(Arc::new(parser.interface.clone())),
	);

	// The rest of the module's compilation happens in a worker thread

	s.spawn(move |_s| {
		// Wait for all module interfaces to be finalized
		let module_names = parser.interface.import_names.clone();

		let mut imports_left = module_names
			.into_iter()
			.map(|name| match name {
				ModuleImportKind::Child(name) => Identifier::from_parent(&module_name, name),
				ModuleImportKind::Language(name) => Identifier::from_name(name, true),
				ModuleImportKind::Extern(name) => name,
			})
			.collect::<Vec<_>>();

		// Loop over remaining pending imports
		while let Some(import_name) = imports_left.first() {
			let import_path =
				get_module_source_path(&state, src_path.clone(), import_name).unwrap();

			// Get the current import's compilation state

			let import_state = state
				.module_states
				.read()
				.unwrap()
				.get(&import_path)
				.cloned()
				.unwrap();

			// If the imported module is ready, remove it from the list.
			// If not, push it to the end of the list so we get a chance
			// to check up on the other imports in the meantime

			match import_state {
				ModuleState::InterfaceComplete(complete) => {
					parser
						.interface
						.imported
						.insert(import_name.name().clone(), complete);
					imports_left.remove(0);
				}

				ModuleState::InterfaceUntyped(_) => {
					let first = imports_left.remove(0);
					imports_left.push(first);
					continue;
				}

				_ => panic!(),
			};
		}

		// Time to generate some code baby!!! god this module is messy lmao

		let context = Context::create();
		let src_name = src_path.file_name().unwrap().to_str().unwrap();

		// generate_code() is a bit of a misleading name; this function takes care of
		// everything from AST parsing, to type checking, to cIR generation and validation,
		// to LLVM codegen. should be broken up into discrete functions at some point honestly

		let result = match generate_code(&state, &mut parser, &context, &src_path, &module_name) {
			Ok(res) => res,
			Err(_) => {
				error_sender
					.send(CMNMessageLog::Raw(format!(
						"\n{:>10} compiling {}\n",
						"failed".bold().red(),
						src_name.bold()
					)))
					.unwrap();
				return;
			}
		};

		let target_machine = llvm::get_target_machine();

		if state.emit_types.contains(&EmitType::LLVMIr) {
			let mut llvm_out_path = out_path.clone();
			llvm_out_path.set_extension("ll");
			result.module.print_to_file(llvm_out_path).unwrap();
		}

		if state.emit_types.iter().any(|ty| {
			matches!(
				ty,
				EmitType::Binary | EmitType::StaticLib | EmitType::DynamicLib
			)
		}) {
			target_machine
				.write_to_file(&result.module, FileType::Object, &out_path)
				.unwrap();
		}
	});

	Ok(())
}

// TODO: Add proper module searching support, based on a list of module search dirs, as well as support for .co, .h, .hpp etc
pub fn get_module_source_path(
	state: &Arc<ManagerState>,
	mut current_path: PathBuf,
	module: &Identifier,
) -> Option<PathBuf> {
	// Resolve built-in library paths. This is currently hard-coded, but
	// there's probably a more elegant solution to be written down the line
	if module.absolute && matches!(module.path[0].to_string().as_str(), "core" | "std") {
		let mut current_path = PathBuf::from(state.libcomune_dir.clone());

		current_path.push(module.path[0].to_string());
		current_path.push("src");
		current_path.push("lib");
		current_path.set_extension("co");

		return Some(current_path);
	}

	current_path.set_extension("");

	for i in 0..module.path.len() - 1 {
		current_path.push(&*module.path[i]);
	}

	current_path.set_file_name(&**module.name());

	let extensions = ["co", "cpp", "c"];

	for extension in extensions {
		current_path.set_extension(extension);

		if current_path.exists() {
			return Some(current_path);
		}
	}

	for dir in &state.import_paths {
		let mut current_path = PathBuf::from(dir);
		current_path.push(&**module.name());

		for extension in extensions {
			current_path.set_extension(extension);
			if current_path.exists() {
				return Some(current_path);
			}
		}
	}

	None
}

pub fn get_module_out_path(state: &Arc<ManagerState>, module: &Identifier) -> PathBuf {
	let mut result = PathBuf::from(&state.output_dir);

	for scope in &module.path {
		result.push(&**scope);
	}

	fs::create_dir_all(result.parent().unwrap()).unwrap();
	result.set_extension("o");
	result
}

pub fn parse_interface(
	state: &Arc<ManagerState>,
	path: &Path,
	error_sender: Sender<CMNMessageLog>,
) -> Result<Parser, ComuneError> {
	// First phase of module compilation: create Lexer and Parser, and parse the module at the namespace level

	let mut mod_state = Parser::new(
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
				return Err(ComuneError::new(
					ComuneErrCode::ModuleNotFound(OsString::from(path.file_name().unwrap())),
					SrcSpan::new(),
				));
			}
		},
		state.verbose_output,
	);

	println!(
		"{:>10} {}",
		"compiling".bold().green(),
		mod_state.lexer.borrow().file_name.to_string_lossy()
	);

	if state.verbose_output {
		println!("\ncollecting symbols...");
	}

	// Parse namespace level

	return match mod_state.parse_interface() {
		Ok(_) => Ok(mod_state),
		Err(e) => {
			mod_state
				.lexer
				.borrow()
				.log_msg(ComuneMessage::Error(e.clone()));
			Err(e)
		}
	};
}

pub fn resolve_types(state: &Arc<ManagerState>, parser: &mut Parser) -> ComuneResult<()> {
	// At this point, all imports have been resolved, so validate namespace-level types
	ast::resolve_namespace_types(&mut parser.interface)?;

	// Check for cyclical dependencies without indirection
	// TODO: Nice error reporting for this
	ast::check_module_cyclical_deps(&mut parser.interface)?;

	if state.verbose_output {
		todo!()
		//println!("\ntype resolution output:\n\n{}", parser.interface);
	}

	Ok(())
}

pub fn generate_code<'ctx>(
	state: &Arc<ManagerState>,
	parser: &mut Parser,
	context: &'ctx Context,
	src_path: &Path,
	input_module: &Identifier,
) -> Result<LLVMBackend<'ctx>, ComuneError> {
	// Generate AST

	match parser.generate_ast() {
		Ok(()) => {
			if state.verbose_output {
				println!("\nvalidating...");
			}
		}
		Err(e) => {
			parser
				.lexer
				.borrow()
				.log_msg(ComuneMessage::Error(e.clone()));
			return Err(e);
		}
	};

	// Validate code

	match ast::validate_module_impl(&parser.interface, &mut parser.module_impl) {
		Ok(()) => {
			if state.verbose_output {
				println!("generating code...");
			}
		}
		Err(e) => {
			parser
				.lexer
				.borrow()
				.log_msg_at(e.span, ComuneMessage::Error(e.clone()));
			return Err(e);
		}
	}

	// Generate cIR

	let module_name = input_module.to_string();
	let mut cir_module = CIRModuleBuilder::from_ast(parser).module;

	// Note: we currently write the output of a lot of
	// intermediate stages to the build directory. This is
	// mostly for debugging purposes; when the compiler is
	// at a more mature stage, most of these writes could be
	// removed or turned into an opt-in CLI option.

	if state.emit_types.contains(&EmitType::ComuneIr) {
		// Write cIR to file
		fs::write(
			get_module_out_path(state, input_module).with_extension("cir"),
			cir_module.to_string(),
		)
		.unwrap();
	}

	// Analyze & optimize cIR
	let mut cir_man = CIRPassManager::new();

	cir_man.add_pass(verify::Verify);
	
	// broken, don't use rn
	//cir_man.add_mut_pass(cleanup::SimplifyCFG);
	
	cir_man.add_mut_pass(DataFlowPass::new(VarInitCheck {}));
	cir_man.add_pass(verify::Verify);

	let cir_errors = cir_man.run_on_module(&mut cir_module);

	if !cir_errors.is_empty() {
		let mut return_errors = vec![];

		for error in cir_errors {
			return_errors.push(error.clone());
			parser
				.lexer
				.borrow()
				.log_msg_at(error.span, ComuneMessage::Error(error));
		}

		return Err(ComuneError::new(
			ComuneErrCode::Pack(return_errors),
			SrcSpan::new(),
		));
	}

	let module_mono = cir_module.monoize();

	if state.emit_types.contains(&EmitType::ComuneIrMono) {
		// Write monomorphized cIR to file
		fs::write(
			get_module_out_path(state, input_module).with_extension("cir_mono"),
			module_mono.to_string(),
		)
		.unwrap();
	}

	// Generate LLVM IR
	let mut backend = LLVMBackend::new(
		context,
		&module_name,
		src_path.to_str().unwrap(), // TODO: Handle invalid UTF-8 paths
		false,
		true,
	);

	backend.compile_module(&module_mono).unwrap();
	backend.generate_libc_bindings();

	if let Err(e) = backend.module.verify() {
		println!(
			"{}\n{}\n",
			"an internal compiler error occurred:".red().bold(),
			lexer::get_escaped(e.to_str().unwrap())
		);

		// Output bogus LLVM here, for debugging purposes
		backend.module.print_to_file("bogus.ll").unwrap();

		println!(
			"{} ill-formed LLVM IR printed to {}",
			"note:".bold(),
			"bogus.ll".bold()
		);

		return Err(ComuneError::new(ComuneErrCode::LLVMError, SrcSpan::new()));
	};

	if state.emit_types.contains(&EmitType::LLVMIrRaw) {
		backend
			.module
			.print_to_file(
				get_module_out_path(state, input_module)
					.with_extension("llraw")
					.as_os_str(),
			)
			.unwrap();
	}

	// Optimization passes
	let mpm = PassManager::create(());

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
