use std::{
	ffi::OsString,
	fs,
	path::{Path, PathBuf},
	sync::{mpsc::Sender, Arc, Mutex},
};

use colored::Colorize;
use inkwell::{context::Context, module::Module, passes::PassManager, targets::FileType};
use rayon::prelude::*;

use crate::{
	ast::{
		self,
		namespace::{Identifier, Namespace},
	},
	cir::{
		analyze::{verify, CIRPassManager, lifeline::{self, VarInitCheck, LivenessState}, DataFlowPass},
		builder::CIRModuleBuilder, CIRStmt, RValue, Operand,
	},
	errors::{CMNError, CMNErrorCode, CMNMessage, CMNMessageLog},
	lexer::{self, Lexer},
	llvm::{self, LLVMBackend},
	parser::{ParseResult, Parser},
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
}

pub struct ModuleState {
	pub parser: Parser,
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
) -> Result<Namespace, CMNError> {
	let out_path = get_module_out_path(&state, &module_name);
	state.output_modules.lock().unwrap().push(out_path.clone());

	let mut mod_state = parse_interface(&state, &src_path, error_sender.clone())?;

	// Resolve module imports
	let module_names = mod_state.parser.namespace.referenced_modules.clone();

	let sender_lock = Mutex::new(error_sender.clone());

	let imports = module_names
		.into_par_iter()
		.map(|name| {
			let import_path = get_module_source_path(&state, src_path.clone(), &name).unwrap();

			let error_sender = sender_lock.lock().unwrap().clone();
			let module_interface = launch_module_compilation(
				state.clone(),
				import_path,
				name.clone(),
				error_sender,
				s,
			);
			(name, module_interface.unwrap())
		})
		.collect();

	mod_state.parser.namespace.imported = imports;

	match resolve_types(&state, &mut mod_state) {
		Ok(_) => {}
		Err(e) => {
			mod_state
				.parser
				.lexer
				.borrow()
				.log_msg_at(0, 0, CMNMessage::Error(e.clone()));
			return Err(e);
		}
	};

	let interface = mod_state.parser.namespace.get_interface();

	// The rest of the module's compilation happens in a worker thread

	s.spawn(move |_s| {
		let context = Context::create();
		let src_name = src_path.file_name().unwrap().to_str().unwrap();

		let result = match generate_code(&state, &mut mod_state, &context, &src_path, &module_name)
		{
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

	Ok(interface)
}

// TODO: Add proper module searching support, based on a list of module search dirs, as well as support for .co, .h, .hpp etc
pub fn get_module_source_path(
	state: &Arc<ManagerState>,
	mut current_path: PathBuf,
	module: &Identifier,
) -> Option<PathBuf> {
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
) -> Result<ModuleState, CMNError> {
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

pub fn resolve_types(state: &Arc<ManagerState>, mod_state: &mut ModuleState) -> ParseResult<()> {
	let root = &mut mod_state.parser.namespace;

	// At this point, all imports have been resolved, so validate namespace-level types
	ast::resolve_namespace_types(root)?;

	// Check for cyclical dependencies without indirection
	// TODO: Nice error reporting for this
	ast::check_namespace_cyclical_deps(root)?;

	if state.verbose_output {
		println!("\ntype resolution output:\n\n{}", root);
	}

	Ok(())
}

pub fn generate_code<'ctx>(
	state: &Arc<ManagerState>,
	mod_state: &mut ModuleState,
	context: &'ctx Context,
	src_path: &Path,
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

	match ast::validate_namespace(&mut mod_state.parser.namespace) {
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
	
	cir_man.add_pass(DataFlowPass::new(VarInitCheck {}, |result, func| {
		let mut errors = vec![];
		
		for (i, block) in func.blocks.iter().enumerate() {
			for (j, stmt) in block.items.iter().enumerate() {
				match stmt {
					CIRStmt::Assignment(_, (RValue::Atom(_, _, Operand::LValue(lval)), _)) | 
					CIRStmt::Switch(Operand::LValue(lval), ..) | 
					CIRStmt::Return(Some((Operand::LValue(lval), _)))=> {
						let state = result.get_state_before(i, j);
						
						match state.get_liveness(lval) {
							LivenessState::Live => { }

							_ => {
								errors.push((
									CMNError::new(CMNErrorCode::InvalidUse {
										variable: Identifier::from_name(
											func.variables[lval.local]
												.2
												.as_ref()
												.unwrap_or(&format!("(temp variable _{})", lval.local).into())
												.clone(),
											false,
										),
										state: state.get_liveness(lval),
									}), 
									(0, 0)
								))
							}
						}
					}

					_ => {}
				}
			}
		}
		
		errors
	}));

	cir_man.add_pass(verify::Verify);

	let cir_errors = cir_man.run_on_module(&mut cir_module);

	if !cir_errors.is_empty() {
		let mut return_errors = vec![];

		for error in cir_errors {
			return_errors.push(error.0.clone());
			mod_state.parser.lexer.borrow().log_msg_at(
				error.1 .0,
				error.1 .1,
				CMNMessage::Error(error.0),
			);

			//println!("{cir_module}\n");
		}

		return Err(CMNError::new(CMNErrorCode::Pack(return_errors)));
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

		return Err(CMNError::new(CMNErrorCode::LLVMError));
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
