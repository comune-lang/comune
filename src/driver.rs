use std::{
	collections::{HashMap, HashSet},
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
		semantic::validate_module_impl,
	},
	cir::{
		analyze::{
			lifeline::{DefInitFlow, ElaborateDrops, VarInitCheck},
			verify, CIRPassManager, DataFlowPass,
		},
		builder::CIRModuleBuilder,
		monoize::MonomorphServer,
		CIRModule,
	},
	clang::compile_cpp_module,
	errors::{CMNMessageLog, ComuneErrCode, ComuneError, ComuneMessage, ERROR_COUNT},
	lexer::{self, Lexer, SrcSpan},
	llvm::LLVMBackend,
	parser::{ComuneResult, Parser},
};

pub const COMUNE_TOOLCHAIN_KEY: &str = "COMUNE_TOOLCHAIN";

pub struct CompilerState {
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum EmitType {
	DynamicLib,
	StaticLib,
	Binary,
	Object,
	ComuneIr,
	ComuneIrMono,
	LLVMIrRaw,
	LLVMIr,
	None,
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
			"none" => Some(EmitType::None),
			_ => None,
		}
	}
}

impl CompilerState {
	pub fn requires_obj_output(&self) -> bool {
		self.emit_types.iter().any(|emit| {
			matches!(
				emit,
				EmitType::Binary | EmitType::DynamicLib | EmitType::StaticLib | EmitType::Object
			)
		})
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
	let mut parser =
		match parse_interface(&state, &src_path, module_name.clone(), error_sender.clone()) {
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

		let out_path = get_module_out_path(&state, &module_name);

		if state.emit_types.contains(&EmitType::LLVMIr) {
			let mut llvm_out_path = out_path.clone();
			llvm_out_path.set_extension("ll");
			result.module.print_to_file(llvm_out_path).unwrap();
		}

		if state.requires_obj_output() {
			result
				.target_machine
				.write_to_file(&result.module, FileType::Object, &out_path)
				.unwrap();
		}
	});

	Ok(())
}

pub fn parse_interface(
	_state: &Arc<CompilerState>,
	path: &Path,
	module_name: Identifier,
	error_sender: Sender<CMNMessageLog>,
) -> Result<Parser, ComuneError> {
	// First phase of module compilation: create Lexer and Parser, and parse the module at the namespace level
	let lexer = match Lexer::new(path, error_sender) {
		Ok(f) => f,
		Err(e) => {
			eprintln!(
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
	};

	let mut parser = Parser::new(lexer, module_name);

	// TODO: HEY ASH TOMORROW MORNING MAKE IT SO CORE DOESN'T IMPORT STD
	// TODO: FUCK YOU I'M TIRED AND I HAVE TOO MUCH TO DO. IT WORKS FOR NOW
	parser.interface.import_names = HashSet::from([
		ModuleImportKind::Language("core".into()),
		ModuleImportKind::Language("std".into()),
	]);

	// Parse namespace level

	return match parser.parse_interface() {
		Ok(_) => Ok(parser),
		Err(e) => {
			parser
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

		let import_path = get_module_source_path(&state, src_path.clone(), &fs_name)
			.expect(&format!("could not find module source path: {fs_name}!"));

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
	if let Err(e) = parser.generate_ast() {
		parser
			.lexer
			.borrow()
			.log_msg(ComuneMessage::Error(e.clone()));

		return Err(e);
	}

	// Validate code
	if let Err(e) = validate_module_impl(&parser.interface, &mut parser.module_impl) {
		parser
			.lexer
			.borrow()
			.log_msg(ComuneMessage::Error(e.clone()));

		return Err(e);
	}

	// Generate cIR
	let module_name = input_module.to_string();
	let mut cir_module = CIRModuleBuilder::from_ast(parser).module;

	if state.emit_types.contains(&EmitType::ComuneIr) {
		// Write cIR to file
		fs::write(
			get_module_out_path(state, input_module).with_extension("cir"),
			cir_module.to_string(),
		)
		.unwrap();
	}

	let mut cir_man = CIRPassManager::new();

	// NOTE: VarInitCheck happens BEFORE ElaborateDrops, because
	// ElaborateDrops strips any DropShims from the IR and replaces them
	// with the appropriate destructor code (if any).
	cir_man.add_mut_pass(DataFlowPass::new(DefInitFlow, VarInitCheck));
	cir_man.add_pass(verify::Verify);

	let cir_errors = cir_man.run_on_module(&mut cir_module);

	// Handle any errors
	if !cir_errors.is_empty() {
		for error in &cir_errors {
			parser
				.lexer
				.borrow()
				.log_msg(ComuneMessage::Error(error.clone()));
		}

		return Err(ComuneError::new(
			ComuneErrCode::Pack(cir_errors),
			SrcSpan::new(),
		));
	}

	// Monomorphize the module
	let mut module_mono = state.monomorph_server.monoize_module(cir_module);

	// Perform post-monomorphization passes, including drop elaboration
	let mut cir_man = CIRPassManager::new();

	cir_man.add_mut_pass(DataFlowPass::new(DefInitFlow, ElaborateDrops));
	cir_man.add_pass(verify::Verify);

	let cir_errors = cir_man.run_on_module(&mut module_mono);

	// Write finalized cIR to file
	if state.emit_types.contains(&EmitType::ComuneIrMono) {
		fs::write(
			get_module_out_path(state, input_module).with_extension("cir_mono"),
			module_mono.to_string(),
		)
		.unwrap();
	}

	// And handle any errors again
	if !cir_errors.is_empty() {
		for error in &cir_errors {
			parser
				.lexer
				.borrow()
				.log_msg(ComuneMessage::Error(error.clone()));
		}

		return Err(ComuneError::new(
			ComuneErrCode::Pack(cir_errors),
			SrcSpan::new(),
		));
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

pub fn generate_monomorph_module(
	state: Arc<CompilerState>,
	error_sender: &Sender<CMNMessageLog>,
) -> ComuneResult<()> {
	let mut out_path = PathBuf::from(&state.output_dir);
	out_path.push("monomorph-module");

	// Monomorphize all the requested function instances into a dedicated module
	//
	// This is pretty low-hanging fruit for optimization,
	// considering it's entirely single-threaded right now
	let mut module = state.monomorph_server.generate_fn_instances();

	if state.emit_types.contains(&EmitType::ComuneIr) {
		// Write cIR to file
		fs::write(out_path.with_extension("cir"), module.to_string()).unwrap();
	}

	let mut cir_man = CIRPassManager::new();

	cir_man.add_mut_pass(DataFlowPass::new(DefInitFlow, VarInitCheck));
	cir_man.add_mut_pass(DataFlowPass::new(DefInitFlow, ElaborateDrops));

	let errors = cir_man.run_on_module(&mut module);

	if !errors.is_empty() {
		for error in &errors {
			error_sender
				.send(CMNMessageLog::Plain {
					msg: ComuneMessage::Error(error.clone()),
					filename: "monomorph-module".to_string(),
				})
				.unwrap();
		}

		return Err(ComuneError::new(
			ComuneErrCode::Pack(errors),
			SrcSpan::new(),
		));
	}

	if state.emit_types.contains(&EmitType::ComuneIrMono) {
		// Write optimized cIR to file
		fs::write(out_path.with_extension("cir_mono"), module.to_string()).unwrap();
	}

	let context = Context::create();

	let result = generate_llvm_ir(
		&state,
		"monomorph-module".into(),
		module,
		&PathBuf::from("monomorph-module"),
		&out_path,
		&context,
	)?;

	if state.emit_types.contains(&EmitType::LLVMIr) {
		let mut llvm_out_path = out_path.clone();
		llvm_out_path.set_extension("ll");
		result.module.print_to_file(llvm_out_path).unwrap();
	}

	if state.requires_obj_output() {
		result
			.target_machine
			.write_to_file(&result.module, FileType::Object, &out_path)
			.unwrap();
	}

	state.output_modules.lock().unwrap().push(out_path);

	Ok(())
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
		eprintln!(
			"{}\n{}\n",
			"an internal compiler error occurred:".red().bold(),
			lexer::get_escaped(e.to_str().unwrap())
		);

		let boguspath = out_path.with_extension("llbogus");

		// Output bogus LLVM here, for debugging purposes
		backend.module.print_to_file(boguspath.as_os_str()).unwrap();

		eprintln!(
			"{} ill-formed LLVM IR printed to {}",
			"note:".bold(),
			boguspath.to_string_lossy().bold()
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

pub fn get_module_source_path(
	state: &CompilerState,
	mut current_path: PathBuf,
	module: &Identifier,
) -> Option<PathBuf> {
	// Resolve built-in library paths. This is currently hard-coded, but
	// there's probably a more elegant solution to be written down the line
	if module.absolute && matches!(module.path[0].to_string().as_str(), "core" | "std") {
		current_path = PathBuf::from(std::env::var(COMUNE_TOOLCHAIN_KEY).unwrap());
		current_path.push("libcomune")
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
	let mut filename = String::new();
	let mut iter = module.path.iter();

	filename.push_str(iter.next().unwrap());

	for scope in iter {
		filename.push('-');
		filename.push_str(scope);
	}

	result.push(filename);

	fs::create_dir_all(result.parent().unwrap()).unwrap();
	result.set_extension("o");
	result
}
