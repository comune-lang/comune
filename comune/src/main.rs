mod parser;
mod llvm;
mod modules;

use std::{io::{self, Write}, ffi::OsString, sync::{Arc, Mutex}};
use clap::Parser;
use colored::Colorize;
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


	let target_machine = llvm::get_target_machine();


	types::PTR_SIZE_BYTES.set(target_machine.get_target_data().get_pointer_byte_size(None)).unwrap();

	let manager_state = Arc::new(modules::ManagerState { 
		working_dir: "test/".into(), 
		import_paths: vec![], 
		max_threads: args.num_jobs, 
		verbose_output: args.verbose,
		output_modules: Mutex::new(vec![]),
	});

	rayon::scope(|s| {
		modules::launch_module_compilation(manager_state.clone(), args.input_file, s).unwrap();
	});
	
	// Link into executable
	// We use gcc here because fuck dude i don't know how to use ld manually
	let mut output = Command::new("gcc");
	
	for module in &*manager_state.output_modules.lock().unwrap() {
		output.arg("-o".to_string() + &module.to_string_lossy());
	}

	let output_result = output
				.arg("-nodefaultlibs")
				.arg("-lc")
				.arg("-fno-rtti")
				.arg("-fno-exceptions")
				.arg("out.o")
				.output()
				.expect("fatal: failed to link executable");
	
	io::stdout().write(&output_result.stdout).unwrap();
	io::stderr().write(&output_result.stderr).unwrap();
	
	Ok(())
}
