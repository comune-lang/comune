use std::{
	collections::HashMap,
	ffi::OsString,
	fs,
	path::{Path, PathBuf},
	sync::{atomic::Ordering, mpsc::Sender, Arc, Mutex, RwLock},
};

use colored::Colorize;
use inkwell::{context::Context, passes::PassManager, targets::FileType};

use crate::{
	ast::{
		self,
		module::{Identifier, ModuleImport, ModuleImportKind, ModuleInterface, Name},
	},
	cir::{
		analyze::{lifeline::VarInitCheck, verify, CIRPassManager, DataFlowPass},
		builder::CIRModuleBuilder,
		monoize::MonomorphServer,
		CIRModule,
	},
	clang::compile_cpp_module,
	errors::{CMNMessageLog, ComuneErrCode, ComuneError, ComuneMessage, ERROR_COUNT},
	lexer::{self, Lexer, SrcSpan},
	llvm::{self, LLVMBackend},
	parser::{ComuneResult, Parser},
};

pub struct CompilerState {
	pub libcomune_dir: OsString,
	pub import_paths: Vec<OsString>,
	pub max_threads: usize,
	pub verbose_output: bool,
	pub output_modules: Mutex<Vec<PathBuf>>,
	pub output_dir: OsString,
	pub emit_types: Vec<EmitType>,
	pub backtrace_on_error: bool,
	pub module_states: RwLock<HashMap<PathBuf, ModuleState>>,
	pub monomorph_server: MonomorphServer,
}

#[derive(Clone)]
pub enum ModuleState {
	Parsing,
	ParsingFailed,
	InterfaceUntyped(Arc<ModuleInterface>),
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
	state: Arc<CompilerState>,
	src_path: PathBuf,
	module_name: Identifier,
	error_sender: Sender<CMNMessageLog>,
	s: &rayon::Scope,
) -> Result<(), ComuneError> {
	if state.module_states.read().unwrap().contains_key(&src_path) {
		return Ok(());
	}

	println!(
		"{:>10} {}",
		"compiling".bold().green(),
		src_path.file_name().unwrap().to_string_lossy()
	);

	let out_path = get_module_out_path(&state, &module_name);

	state.output_modules.lock().unwrap().push(out_path.clone());

	state
		.module_states
		.write()
		.unwrap()
		.insert(src_path.clone(), ModuleState::Parsing);

	let ext = src_path.extension().unwrap();

	if ext == "cpp" {
		compile_cpp_module(state, src_path, &module_name, error_sender, s)
	} else if ext == "co" {
		compile_comune_module(state, src_path, module_name, error_sender, s)
	} else {
		todo!()
	}
}

pub fn compile_comune_module(
	state: Arc<CompilerState>,
	src_path: PathBuf,
	module_name: Identifier,
	error_sender: Sender<CMNMessageLog>,
	s: &rayon::Scope,
) -> Result<(), ComuneError> {
	let mut parser = match parse_interface(&state, &src_path, error_sender.clone()) {
		Ok(parser) => parser,

		Err(e) => {
			ERROR_COUNT.fetch_add(1, Ordering::Relaxed);

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
		ModuleState::InterfaceUntyped(Arc::new(parser.interface.get_external_interface(false))),
	);

	// Resolve module imports
	let modules: Vec<_> = parser.interface.import_names.clone().into_iter().collect();

	parser.interface.imported = await_imports_ready(
		&state,
		&src_path,
		&module_name,
		modules,
		error_sender.clone(),
		s,
	)?;

	match ast::semantic::validate_interface(&state, &mut parser) {
		Ok(_) => {}
		Err(e) => {
			ERROR_COUNT.fetch_add(1, Ordering::Relaxed);

			parser
				.lexer
				.borrow()
				.log_msg(ComuneMessage::Error(e.clone()));

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
		ModuleState::InterfaceComplete(Arc::new(parser.interface.get_external_interface(true))),
	);

	// The rest of the module's compilation happens in a worker thread

	s.spawn(move |_s| {
		// Wait for all module interfaces to be finalized
		parser.interface.imported.clear();

		let module_names = parser.interface.import_names.clone();

		let mut imports_left = module_names
			.into_iter()
			.map(|m_kind| {
				let m_kind_clone = m_kind.clone();
				match m_kind {
					ModuleImportKind::Child(name) => {
						(m_kind_clone, Identifier::from_parent(&module_name, name))
					}
					ModuleImportKind::Language(name) => {
						(m_kind_clone, Identifier::from_name(name, true))
					}
					ModuleImportKind::Extern(name) => (m_kind_clone, name),
				}
			})
			.collect::<Vec<_>>();

		// Loop over remaining pending imports
		while let Some(import_name) = imports_left.first() {
			let import_path =
				get_module_source_path(&state, src_path.clone(), &import_name.1).unwrap();

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
					parser.interface.imported.insert(
						import_name.1.name().clone(),
						ModuleImport {
							interface: complete,
							import_kind: import_name.0.clone(),
							path: import_path,
						},
					);

					imports_left.remove(0);
				}

				ModuleState::InterfaceUntyped(_) => {
					let first = imports_left.remove(0);
					imports_left.push(first);
					continue;
				}

				// Upstream parsing failed somewhere, abort
				ModuleState::ParsingFailed => return,

				ModuleState::Parsing => {}
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
				ERROR_COUNT.fetch_add(1, Ordering::Relaxed);

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
		let out_path = get_module_out_path(&state, &module_name);

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
	state: &CompilerState,
	mut current_path: PathBuf,
	module: &Identifier,
) -> Option<PathBuf> {
	// Resolve built-in library paths. This is currently hard-coded, but
	// there's probably a more elegant solution to be written down the line
	if module.absolute && matches!(module.path[0].to_string().as_str(), "core" | "std") {
		current_path = PathBuf::from(state.libcomune_dir.clone());
	} else {
		current_path.pop();
	}

	current_path.set_extension("");

	for i in 0..module.path.len() {
		current_path.push(&*module.path[i]);
	}

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

pub fn get_module_out_path(state: &CompilerState, module: &Identifier) -> PathBuf {
	let mut result = PathBuf::from(&state.output_dir);

	for scope in &module.path {
		result.push(&**scope);
	}

	fs::create_dir_all(result.parent().unwrap()).unwrap();
	result.set_extension("o");
	result
}

pub fn parse_interface(
	state: &Arc<CompilerState>,
	path: &Path,
	error_sender: Sender<CMNMessageLog>,
) -> Result<Parser, ComuneError> {
	// First phase of module compilation: create Lexer and Parser, and parse the module at the namespace level

	let mut mod_state = Parser::new(match Lexer::new(path, error_sender) {
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
	});

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

pub fn await_imports_ready(
	state: &Arc<CompilerState>,
	src_path: &PathBuf,
	module_name: &Identifier,
	mut modules: Vec<ModuleImportKind>,
	error_sender: Sender<CMNMessageLog>,
	s: &rayon::Scope,
) -> ComuneResult<HashMap<Name, ModuleImport>> {
	let mut imports = HashMap::new();

	while let Some(name) = modules.first().cloned() {
		let (import_name, fs_name) = match name.clone() {
			ModuleImportKind::Child(name) => {
				(name.clone(), Identifier::from_parent(module_name, name))
			}
			ModuleImportKind::Language(name) => (name.clone(), Identifier::from_name(name, true)),
			ModuleImportKind::Extern(name) => (name.name().clone(), name),
		};

		let import_path = get_module_source_path(&state, src_path.clone(), &fs_name).unwrap();

		let error_sender = error_sender.clone();

		// Query module interface, blocking this thread until it's ready
		loop {
			let import_state = state
				.module_states
				.read()
				.unwrap()
				.get(&import_path)
				.cloned();

			match import_state {
				None => match launch_module_compilation(
					state.clone(),
					import_path.clone(),
					fs_name.clone(),
					error_sender.clone(),
					s,
				) {
					Ok(()) => {}
					Err(e) => {
						state
							.module_states
							.write()
							.unwrap()
							.insert(src_path.clone(), ModuleState::ParsingFailed);

						let import_name = import_path.file_name().unwrap().to_str().unwrap();

						error_sender
							.send(CMNMessageLog::Raw(format!(
								"\n{:>10} compiling {}\n",
								"failed".bold().red(),
								import_name.bold()
							)))
							.unwrap();

						return Err(e);
					}
				},

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

				// If this is a child module, await the fully complete interface.
				// If not, the untyped interface is fine
				Some(ModuleState::InterfaceUntyped(interface)) => {
					if matches!(name, ModuleImportKind::Child(_)) {
						std::thread::sleep(std::time::Duration::from_millis(1))
					} else {
						imports.insert(
							import_name,
							ModuleImport {
								interface: interface.clone(),
								import_kind: name,
								path: import_path,
							},
						);

						modules.remove(0);
						break;
					}
				}

				Some(ModuleState::InterfaceComplete(interface)) => {
					imports.insert(
						import_name,
						ModuleImport {
							interface: interface.clone(),
							import_kind: name,
							path: import_path,
						},
					);

					modules.remove(0);
					break;
				}
			}
		}
	}

	Ok(imports)
}

pub fn generate_code<'ctx>(
	state: &Arc<CompilerState>,
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

	match ast::semantic::validate_module_impl(&parser.interface, &mut parser.module_impl) {
		Ok(()) => {
			if state.verbose_output {
				println!("generating code...");
			}
		}
		Err(e) => {
			parser
				.lexer
				.borrow()
				.log_msg(ComuneMessage::Error(e.clone()));
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
			parser.lexer.borrow().log_msg(ComuneMessage::Error(error));
		}

		return Err(ComuneError::new(
			ComuneErrCode::Pack(return_errors),
			SrcSpan::new(),
		));
	}

	let module_mono = state.monomorph_server.monoize_module(cir_module);

	if state.emit_types.contains(&EmitType::ComuneIrMono) {
		// Write monomorphized cIR to file
		fs::write(
			get_module_out_path(state, input_module).with_extension("cir_mono"),
			module_mono.to_string(),
		)
		.unwrap();
	}

	generate_llvm_ir(
		state,
		module_name,
		module_mono,
		src_path,
		&get_module_out_path(state, input_module),
		context,
	)
}

pub fn generate_llvm_ir<'ctx>(
	state: &CompilerState,
	module_name: String,
	module_mono: CIRModule,
	src_path: &Path,
	out_path: &Path,
	context: &'ctx Context,
) -> ComuneResult<LLVMBackend<'ctx>> {
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
			.print_to_file(out_path.with_extension("llraw").as_os_str())
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
