mod parser;
mod llvm;
mod modules;

use std::{path::Path, io::{self, Write}, ffi::OsString};
use clap::Parser;
use colored::Colorize;
use inkwell::{context::Context, targets::{Target, InitializationConfig, TargetTriple, FileType}};
use parser::types;
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



fn main() -> color_eyre::eyre::Result<()> {
    color_eyre::install()?;

	let args = ComuneCLI::parse();

	if args.input_file.is_empty() {
		println!("{} {}", "fatal:".red().bold(), "no input module");
		return Ok(());
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


	types::PTR_SIZE_BYTES.set(target_machine.get_target_data().get_pointer_byte_size(None)).unwrap();


	let manager = modules::ModuleJobManager::new("test/".into(), vec![], args.num_jobs, args.verbose);

	let mut state = match manager.parse_api(args.input_file) {
		Ok(r) => r,
		Err(_) => return Ok(()),
	};

	let context = Context::create();

	state = match manager.resolve_types(state, &context) {
		Ok(r) => r,
		Err(_) => return Ok(()),
	};


	let result = match manager.generate_code(state, &context) {
		Ok(r) => r,
		Err(_) => return Ok(()),
	};
	
	result.module.print_to_file("ir.ll").unwrap();
	target_machine.write_to_file(&result.module, FileType::Object, &Path::new("out.o")).unwrap();

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
	
	Ok(())
}
