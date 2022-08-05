mod parser;
mod llvm;
mod modules;

use std::{path::Path, io::{self, Write}, ffi::OsString};
use clap::Parser;
use colored::Colorize;
use inkwell::{context::Context, targets::{Target, InitializationConfig, TargetTriple, FileType}};
use std::process::Command;


#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct ComuneCLI {
	// Verbose flag
	#[clap(short='v', long="verbose", default_value_t=false, value_parser)]
	verbose: bool,

	#[clap(value_parser, default_value="")]
	input_file: OsString,

	#[clap(short='o', long="output", default_value="a.out", value_parser)]
	output_file: OsString,

	#[clap(long="emit-llvm", default_value_t=false, value_parser)]
	emit_llvm: bool,

	#[clap(short='j', long="jobs", default_value_t=1, value_parser)]
	num_jobs: usize,
}



fn main() {
	let args = ComuneCLI::parse();

	if args.input_file.is_empty() {
		println!("{} {}", "fatal:".red().bold(), "no input module");
		return;
	}

	rayon::ThreadPoolBuilder::new()
		.num_threads(args.num_jobs)
		.build_global()
		.unwrap();


	Target::initialize_x86(&InitializationConfig::default());
	let target = Target::from_name("x86-64").unwrap();

	let target_machine = target.create_target_machine(
		&TargetTriple::create("x86_64-pc-linux-gnu"), 
		"x86-64", 
		"+avx2", 
		inkwell::OptimizationLevel::Aggressive, 
		inkwell::targets::RelocMode::Default, 
		inkwell::targets::CodeModel::Default
	).unwrap();

	let manager = modules::ModuleJobManager::new("test/".into(), vec![], args.num_jobs, args.verbose);

	let state = manager.start_module_compilation(args.input_file).unwrap(); // TODO: Handle error
	let context = Context::create();
	let result = manager.continue_module_compilation(state, &context).unwrap();
	
	result.module.print_to_file("ir.ll").unwrap();
	target_machine.write_to_file(&result.module, FileType::Object, &Path::new("out.o")).unwrap();

	
	// Extremely basic, needs parallelization and linking modules together
	/*for file in args.input_files.iter() {
	
		parser::lexer::CURRENT_LEXER.with(|lexer| { 

			lexer.replace(match Lexer::new(file) {
				Ok(f) => f,
				Err(e) => { println!("{} failed to open input file '{}' ({})", "fatal:".red().bold(), file, e); return; }
			});
		
			let mut parser = parser::Parser::new(&lexer, args.verbose);

			println!("{} {}\n", "compiling".bold().green(), lexer.borrow().file_name.to_string_lossy());

			if args.verbose {
				println!("\ncollecting symbols...");
			}

			// Declarative pass
			match parser.parse_module(false) {
				Ok(_) => { if args.verbose { println!("\nbuilding AST..."); } },
				Err(e) => { lexer.borrow().log_msg(CMNMessage::Error(e)); return; },
			};

			// Generative pass
			let namespace = match parser.parse_module(true) {
				Ok(ctx) => { if args.verbose { println!("\nresolving types..."); } ctx },
				Err(e) => { lexer.borrow().log_msg(CMNMessage::Error(e)); return; },
			};

			// Resolve types
			match semantic::parse_namespace(namespace) {
				Ok(()) => {	if args.verbose { println!("generating code..."); } },
				Err(e) => { lexer.borrow().log_msg_at(e.1.0, e.1.1, CMNMessage::Error(e.0)); return; },
			}


			// LLVM Backend
			
			// Set up target machine
			Target::initialize_x86(&InitializationConfig::default());
			let target = Target::from_name("x86-64").unwrap();

			let target_machine = target.create_target_machine(
				&TargetTriple::create("x86_64-pc-linux-gnu"), 
				"x86-64", 
				"+avx2", 
				inkwell::OptimizationLevel::Aggressive, 
				inkwell::targets::RelocMode::Default, 
				inkwell::targets::CodeModel::Default
			).unwrap();

			// Create LLVM generator
			let context = Context::create();
			let module = context.create_module("test");
			let builder = context.create_builder();


			let mut backend = LLVMBackend {
				context: &context,
				module,
				builder,
				fpm: None,
				fn_value_opt: None,
			};


			// Generate LLVM IR

			// Register function prototypes
			for (sym_name, (sym_type, _)) in &namespace.borrow().symbols {
				backend.register_fn(sym_name.clone(), sym_type).unwrap();
			}

			// Generate function bodies
			for (sym_name, (sym_type, sym_elem)) in &namespace.borrow().symbols {
				backend.generate_fn(sym_name.clone(), sym_type, sym_elem).unwrap();
			}

			backend.generate_libc_bindings();


			if let Err(e) = backend.module.verify() {
				println!("an internal compiler error occurred:\n{}", e);
				
				// Output bogus LLVM here, for debugging purposes
				if args.emit_llvm {
					backend.module.print_to_file(args.output_file.clone() + ".ll").unwrap();
				}

				return;
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

			//mpm.run_on(&backend.module);


			if args.emit_llvm {
				backend.module.print_to_file(args.output_file.clone() + ".ll").unwrap();
			}


			// TODO: Link modules together into single executable
			target_machine.write_to_file(&backend.module, FileType::Object, &Path::new("out.o")).unwrap();
		});
	}*/

	// Link into executable
	// We use gcc here because fuck dude i don't know how to use ld manually
	let output = Command::new("gcc")
				.arg("-o".to_string() + &args.output_file.to_string_lossy())
				.arg("-nodefaultlibs")
				.arg("-lc")
				.arg("-fno-rtti")
				.arg("-fno-exceptions")
				.arg("out.o")
				.output()
				.expect("fatal: failed to link executable");
	
	io::stdout().write(&output.stdout).unwrap();
	io::stderr().write(&output.stderr).unwrap();
}
