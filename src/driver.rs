use std::{
	io::Write,
	collections::{HashMap, HashSet},
	ffi::OsString,
	fs,
	marker::PhantomData,
	path::{Path, PathBuf},
	sync::{atomic::{Ordering, AtomicU32}, Arc, Mutex, RwLock}, io,
};

use colored::Colorize;
use itertools::Itertools;

use crate::{
	ast::{
		self,
		module::{Identifier, ModuleImport, ModuleImportKind, ModuleInterface, Name},
		semantic::validate_module_impl, traits::LangTraitDatabase,
	},
	backend::Backend,
	cir::{
		analyze::{
			lifeline::{DefInitFlow, ElaborateDrops, VarInitCheck},
			verify, CIRPassManager, DataFlowPass,
		},
		builder::CIRModuleBuilder,
		monoize::MonomorphServer,
		CIRModule,
	},
	errors::{ComuneErrCode, ComuneError, ComuneMessage, log_msg},
	lexer::{Lexer, SrcSpan},
	parser::{ComuneResult, Parser},
};

pub const COMUNE_TOOLCHAIN_KEY: &str = "COMUNE_TOOLCHAIN";

pub struct DummyScope<'ctx>(PhantomData<&'ctx u32>);

#[cfg(feature = "concurrent")]
pub type RayonScope<'ctx> = rayon::Scope<'ctx>;
#[cfg(not(feature = "concurrent"))]
pub type RayonScope<'ctx> = DummyScope<'ctx>;

pub struct Compiler<'ctx, T: Backend + ?Sized> {
	pub import_paths: &'ctx [OsString],
	pub output_dir: OsString,
	pub output_file: OsString,
	pub verbose_output: bool,
	pub output_modules: Mutex<Vec<PathBuf>>,
	pub module_states: RwLock<HashMap<PathBuf, ModuleState<'ctx>>>,
	pub opt_level: u32,
	pub debug_info: bool,
	pub no_std: bool,

	pub emit_types: Vec<&'ctx str>,
	pub dep_emit_types: Vec<&'ctx str>,
	pub link_types: Vec<&'ctx str>,

	pub lang_traits: LangTraitDatabase,
	pub error_count: AtomicU32,
	
	monomorph_server: MonomorphServer,
	
	// the compiler doesn't actually *own* any instances of Backend,
	// so we use PhantomData<fn() -> T> to signal that T doesn't
	// have to be Send or Sync
	backend: PhantomData<fn() -> T>,
}

pub struct CompileState<'ctx> {
	parser: Parser<'ctx>,
}

#[derive(Clone)]
pub enum JobSpawner<'ctx, T> {
	Concurrent(T),
	Synchronous(Arc<RwLock<Vec<CompileState<'ctx>>>>)
}

#[derive(Clone)]
pub enum ModuleState<'ctx> {
	Parsing,
	ParsingFailed,
	InterfaceUntyped(Arc<ModuleInterface<'ctx>>),
	InterfaceComplete(Arc<ModuleInterface<'ctx>>),
}

const BUILTIN_EMIT_TYPES: [&str; 3] = ["cir", "cirmono", "none"];

impl<'ctx, T: Backend> Compiler<'ctx, T> {
	pub fn new(
		import_paths: &'ctx [OsString],
		verbose_output: bool,
		output_dir: OsString,
		output_file: OsString,
		emit_types: &'ctx [&'ctx str],
		opt_level: u32,
		debug_info: bool,
		no_std: bool,
	) -> Self {
		let mut emits = vec![];
		let mut links = vec![];
		let mut dep_emits = vec![];

		for ty in emit_types {
			if BUILTIN_EMIT_TYPES.contains(&ty) {
				emits.push(*ty);
			} else if T::SUPPORTED_EMIT_TYPES.contains(&ty) {
				emits.push(*ty);
			} else if T::SUPPORTED_LINK_TYPES.contains(&ty) {
				links.push(*ty);
			} else {
				panic!("invalid argument to --emit: {ty}");
			}
		}

		for ty in &links {
			dep_emits.extend(T::get_required_emit_types(&ty));
		}

		if emits.is_empty() && dep_emits.is_empty() {
			links.extend(T::DEFAULT_LINK_TYPES);

			for ty in &links {
				dep_emits.extend(T::get_required_emit_types(&ty));
			}	
		}

		Self {
			import_paths,
			verbose_output,
			output_dir,
			output_file,
			emit_types: emits,
			dep_emit_types: dep_emits,
			link_types: links,
			opt_level,
			debug_info,
			no_std,
			module_states: RwLock::default(),
			output_modules: Mutex::default(),
			monomorph_server: MonomorphServer::new(),
			error_count: AtomicU32::new(0),
			lang_traits: RwLock::new(HashMap::default()),
			backend: PhantomData,
		}
	}

	pub fn launch_module_compilation(
		&'ctx self,
		src_path: PathBuf,
		module_name: Identifier,
		s: JobSpawner<'ctx, &RayonScope<'ctx>>,
	) -> Result<Vec<Parser>, ComuneError> {
		if self.module_states.read().unwrap().contains_key(&src_path) {
			return Ok(vec![]);
		}

		println!(
			"{:>10} {}",
			"compiling".bold().green(),
			src_path.file_name().unwrap().to_string_lossy()
		);

		self.module_states
			.write()
			.unwrap()
			.insert(src_path.clone(), ModuleState::Parsing);

		let ext = src_path.extension().unwrap();

		if ext == "cpp" {
			self.compile_cpp_module(src_path, &module_name, s)?;
			
			Ok(vec![])
		} else if ext == "co" {
			let mut parsers = vec![];

			self.generate_untyped_interface(
				src_path, 
				module_name.clone(), 
				&mut parsers
			)?;

			Ok(parsers)
		} else {
			unimplemented!()
		}
	}

	pub fn generate_untyped_interface(
		&'ctx self,
		src_path: PathBuf,
		module_name: Identifier,
		jobs_out: &mut Vec<Parser<'ctx>>,
	) -> Result<Arc<ModuleInterface>, ComuneError> {
		let mut parser =
			match self.parse_interface(src_path.clone(), module_name) {
				Ok(parser) => parser,

				Err(e) => {
					self.error_count.fetch_add(1, Ordering::Relaxed);

					self.module_states
						.write()
						.unwrap()
						.insert(src_path.clone(), ModuleState::ParsingFailed);

					return Err(e);
				}
			};
		
		for import in &parser.interface.import_names {
			if let ModuleImportKind::Child(child) = import {
				let import_id = import.get_import_identifier(&parser.interface.name);
				
				let Some(import_path) = self
					.get_module_source_path(src_path.clone(), &import_id)
				else {
					return Err(ComuneError::new(ComuneErrCode::ModuleNotFound(import_id), SrcSpan::new()));
				};

				let child_interface = self.generate_untyped_interface(
					import_path.clone(),
					import_id,
					jobs_out
				)?;
				
				parser.interface.imported.insert(
					child.clone(), 
					ModuleImport { 
						interface: child_interface, 
						import_kind: import.clone(), 
						path: import_path
					}
				);
			}
		}
	
		let interface = Arc::new(parser.interface.get_external_interface(false));

		self.module_states.write().unwrap().insert(
			src_path.clone(),
			ModuleState::InterfaceUntyped(interface.clone()),
		);

		jobs_out.push(parser);

		Ok(interface)
	}

	pub fn generate_typed_interface(
		&'ctx self,
		mut parser: Parser<'ctx>,
		s: JobSpawner<'ctx, &RayonScope<'ctx>>,
	) -> Result<(), ComuneError> {
		// Resolve module imports
		let modules = parser
			.interface
			.import_names
			.clone()
			.into_iter()
			.collect_vec();

		self.await_imports_ready(
			&parser.path, 
			&parser.interface.name, 
			modules, 
			&mut parser.interface.imported,
			s.clone()
		)?;

		match ast::semantic::validate_interface(&mut parser) {
			Ok(_) => {}
			Err(e) => {
				self.error_count.fetch_add(1, Ordering::Relaxed);

				parser
					.lexer
					.borrow()
					.log_msg(ComuneMessage::Error(e.clone()));

				self.module_states
					.write()
					.unwrap()
					.insert(parser.path.clone(), ModuleState::ParsingFailed);

				return Err(e);
			}
		};

		// Update the module database with the fully-typed version of the interface

		self.module_states.write().unwrap().insert(
			parser.path.clone(),
			ModuleState::InterfaceComplete(Arc::new(parser.interface.get_external_interface(true))),
		);

		// The rest of the module's compilation happens later,
		// either in a worker thread, or when the single-threaded
		// spawner is done with the rest of the interfaces
		self.spawn(s, CompileState { parser });
		Ok(())
	}

	pub fn finish_module_job(&self, module_state: CompileState<'ctx>) {
		let CompileState { mut parser } = module_state;

		// Wait for all module interfaces to be finalized
		let module_names = parser.interface.import_names.clone();

		let mut imports_left = module_names
			.into_iter()
			.map(|m_kind| {
				(m_kind.clone(), m_kind.get_import_identifier(&parser.interface.name))
			})
			.collect_vec();

		// Loop over remaining pending imports
		while let Some(import_name) = imports_left.first() {
			let import_path = self
				.get_module_source_path(parser.path.clone(), &import_name.1)
				.unwrap();

			// Get the current import's compilation state

			let import_state = self
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

		let src_name = parser.path.file_name().unwrap().to_str().unwrap().to_string();

		// generate_cir() is a bit of a misleading name; this function takes care of
		// everything from AST parsing, to type checking, to cIR generation and validation.
		// should be broken up into discrete functions at some point honestly

		let parser_name = parser.interface.name.to_string();
		let parser_path = parser.path.to_string_lossy().to_string();
		let module_mono = match self.generate_cir(&mut parser) {
			Ok(res) => res,
			Err(_) => {
				self.error_count.fetch_add(1, Ordering::Relaxed);

				let mut io = io::stderr().lock();

				write!(
					io,
					"\n{:>10} compiling {}\n",
					"failed".bold().red(),
					src_name.bold()
				).unwrap();
	
				return;
			}
		};

		// Time to generate some code baby!!! god this module is messy lmao

		let backend = T::create_instance(self);
		let result = match backend.generate_code(
			&module_mono,
			self,
			&parser_name,
			&parser_path,
		) {
			Ok(res) => res,
			Err(_) => {
				self.error_count.fetch_add(1, Ordering::Relaxed);

				let mut io = io::stderr().lock();

				write!(
					io,
					"\n{:>10} compiling {}\n",
					"failed".bold().red(),
					src_name.bold()
				).unwrap();
	
				return;
			}
		};

		let out_path = self.get_module_out_path(&parser.interface.name);

		self.output_modules.lock().unwrap().push(out_path.clone());
		
		let custom_emits: Vec<_> = 
			self
				.emit_types
				.iter()
				.filter(|emit| !BUILTIN_EMIT_TYPES.contains(emit))
				.chain(self.dep_emit_types.iter())
				.unique()
				.copied()
				.collect();

		backend.emit(self, &result, &custom_emits, &out_path);
	}

	pub fn spawn(&'ctx self, s: JobSpawner<'ctx, &RayonScope<'ctx>>, state: CompileState<'ctx>) {
		match s {
			#[cfg(feature = "concurrent")]
			JobSpawner::Concurrent(s) => {
				s.spawn(|_| self.finish_module_job(state));
			}

			#[cfg(not(feature = "concurrent"))]
			JobSpawner::Concurrent(_) => {
				panic!("feature `concurrent` is not enabled!");
			}

			JobSpawner::Synchronous(s) => {
				s.write().unwrap().push(state);
			}
		}
	}

	pub fn parse_interface(
		&self,
		path: PathBuf,
		module_name: Identifier,
	) -> Result<Parser, ComuneError> {
		// First phase of module compilation: create Lexer and Parser, and parse the module at the namespace level
		let lexer = match Lexer::new(path.clone()) {
			Ok(f) => f,
			Err(e) => {
				eprintln!(
					"{} failed to parse module '{}' ({})",
					"fatal:".red().bold(),
					path.file_name().unwrap().to_string_lossy(),
					e
				);
				return Err(ComuneError::new(
					ComuneErrCode::ModuleNotFound(module_name),
					SrcSpan::new(),
				));
			}
		};

		let mut parser = Parser::new(lexer, module_name, path, &self.lang_traits);

		if self.no_std {
			parser.interface.import_names = HashSet::from([
				ModuleImportKind::Language("core".into()),
			]);
		} else {
			parser.interface.import_names = HashSet::from([
				ModuleImportKind::Language("core".into()),
				ModuleImportKind::Language("std".into()),
			]);
		}

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
		&'ctx self,
		src_path: &PathBuf,
		module_name: &Identifier,
		mut imports_in: Vec<ModuleImportKind>,
		imports_out: &mut HashMap<Name, ModuleImport<'ctx>>,
		s: JobSpawner<'ctx, &RayonScope<'ctx>>,
	) -> ComuneResult<()> {

		while let Some(kind) = imports_in.first().cloned() {
			let import_id = kind.get_import_identifier(module_name);
			let import_name = import_id.name();
			
			let Some(import_path) = self
				.get_module_source_path(src_path.clone(), &import_id)
			else {
				return Err(ComuneError::new(ComuneErrCode::ModuleNotFound(import_id.clone()), SrcSpan::new()))
			};

			// Query module interface, blocking until it's ready
			loop {
				let import_state = self
					.module_states
					.read()
					.unwrap()
					.get(&import_path)
					.cloned();

				match import_state {

					None => match self.launch_module_compilation(
						import_path.clone(),
						import_id.clone(),
						s.clone(),
					) {
						Ok(parsers) => {
							for parser in parsers {
								let Some(ModuleState::InterfaceUntyped(interface)) = 
									self
										.module_states
										.read()
										.unwrap()
										.get(&import_path)
										.cloned() 
								else {
									panic!()
								};

								imports_out.insert(
									import_name.clone(), 
									ModuleImport {
										interface: interface.clone(),
										import_kind: kind.clone(),
										path: import_path.clone(),
									}
								);

								self.generate_typed_interface(
									parser, 
									s.clone()
								)?;
							}
						}

						Err(e) => {
							self.module_states
								.write()
								.unwrap()
								.insert(src_path.clone(), ModuleState::ParsingFailed);

							let import_name = import_path.file_name().unwrap().to_str().unwrap();

							let mut io = io::stderr().lock();

							write!(
								io,
								"\n{:>10} compiling {}\n",
								"failed".bold().red(),
								import_name.bold()
							).unwrap();

							return Err(e);
						}
					},

					// Sleep for some short duration, so we don't hog the CPU
					Some(ModuleState::Parsing) => {
						std::thread::sleep(std::time::Duration::from_millis(1))
					}

					Some(ModuleState::ParsingFailed) => {
						self.module_states
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
						imports_out.insert(
							import_name.clone(),
							ModuleImport {
								interface: interface.clone(),
								import_kind: kind.clone(),
								path: import_path.clone(),
							},
						);

						if !matches!(kind, ModuleImportKind::Child(_)) {
							imports_in.remove(0);
							break;
						} else {
							std::thread::sleep(std::time::Duration::from_millis(1))
						}
					}

					Some(ModuleState::InterfaceComplete(interface)) => {
						imports_out.insert(
							import_name.clone(),
							ModuleImport {
								interface: interface.clone(),
								import_kind: kind,
								path: import_path,
							},
						);

						imports_in.remove(0);
						break;
					}
				}
			}
		}

		Ok(())
	}

	pub fn generate_cir<'cir>(&self, parser: &'cir mut Parser<'ctx>) -> Result<CIRModule<'cir>, ComuneError> {
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
		let mut cir_module = CIRModuleBuilder::from_ast(parser).module;

		if self.emit_types.contains(&"cir") {
			// Write cIR to file
			fs::write(
				self.get_module_out_path(&parser.interface.name).with_extension("cir"),
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
		let mut module_mono = self.monomorph_server.monoize_module(cir_module);

		// Perform post-monomorphization passes, including drop elaboration
		let mut cir_man = CIRPassManager::new();

		cir_man.add_mut_pass(DataFlowPass::new(DefInitFlow, ElaborateDrops));
		cir_man.add_pass(verify::Verify);

		let cir_errors = cir_man.run_on_module(&mut module_mono);

		// Write finalized cIR to file
		if self.emit_types.contains(&"cirmono") {
			fs::write(
				self.get_module_out_path(&parser.interface.name)
					.with_extension("cir_mono"),
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

		Ok(module_mono)
	}

	pub fn generate_monomorph_module(&self) -> ComuneResult<()> {
		let mut out_path = PathBuf::from(&self.output_dir);
		out_path.push("monomorph-module");

		// Monomorphize all the requested function instances into a dedicated module
		//
		// This is pretty low-hanging fruit for optimization,
		// considering it's entirely single-threaded right now
		let mut module = self.monomorph_server.generate_fn_instances(&self.lang_traits);

		if self.emit_types.contains(&"cir") {
			// Write cIR to file
			fs::write(out_path.with_extension("cir"), module.to_string()).unwrap();
		}

		let mut cir_man = CIRPassManager::new();

		cir_man.add_mut_pass(DataFlowPass::new(DefInitFlow, VarInitCheck));
		cir_man.add_mut_pass(DataFlowPass::new(DefInitFlow, ElaborateDrops));

		let errors = cir_man.run_on_module(&mut module);

		if !errors.is_empty() {
			for error in &errors {
				log_msg(ComuneMessage::Error(error.clone()), None);
			}

			return Err(ComuneError::new(
				ComuneErrCode::Pack(errors),
				SrcSpan::new(),
			));
		}

		if self.emit_types.contains(&"cirmono") {
			// Write optimized cIR to file
			fs::write(out_path.with_extension("cir_mono"), module.to_string()).unwrap();
		}

		let backend = T::create_instance(self);

		let result = match backend.generate_code(&module, self, "monomorph-module", "monomorph-module") {
			Ok(res) => res,
			Err(_) => {
				for error in &errors {
					log_msg(ComuneMessage::Error(error.clone()), None);
				}

				return Err(ComuneError::new(
					ComuneErrCode::Pack(errors),
					SrcSpan::new(),
				));
			}
		};

		let custom_emits: Vec<_> = 
			self
				.emit_types
				.iter()
				.filter(|emit| !BUILTIN_EMIT_TYPES.contains(emit))
				.chain(self.dep_emit_types.iter())
				.unique()
				.copied()
				.collect();

		backend.emit(self, &result, &custom_emits, &out_path);

		self.output_modules.lock().unwrap().push(out_path);

		Ok(())
	}

	pub fn link(&self) -> ComuneResult<()> {
		for ty in &self.link_types {
			T::link(self, ty)?;
		}

		Ok(())
	}

	pub(crate) fn get_module_source_path(
		&self,
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
			current_path.push(module.path[i].as_str());
		}

		let extensions = ["co", "cpp", "c"];

		for extension in extensions {
			current_path.set_extension(extension);

			if current_path.exists() {
				return Some(current_path);
			}
		}

		for dir in self.import_paths {
			let mut current_path = PathBuf::from(dir);
			current_path.push(module.name().as_str());

			for extension in extensions {
				current_path.set_extension(extension);
				if current_path.exists() {
					return Some(current_path);
				}
			}
		}

		None
	}

	pub fn get_module_out_path(&self, module: &Identifier) -> PathBuf {
		let mut result = PathBuf::from(&self.output_dir);
		let mut filename = String::new();
		let mut iter = module.path.iter();

		filename.push_str(iter.next().unwrap().as_str());

		for scope in iter {
			filename.push('-');
			filename.push_str(scope.as_str());
		}

		result.push(filename);

		fs::create_dir_all(result.parent().unwrap()).unwrap();
		result.set_extension("o");
		result
	}

	pub fn requires_linking(&self) -> bool {
		!self.link_types.is_empty()
	}
}

pub fn get_file_suffix(path: &Path) -> Option<Name> {
	let mut name = path.file_name()?.to_string_lossy().to_string();
	name.truncate(name.rfind('.').unwrap_or(name.len()));

	Some(name.into())
}
