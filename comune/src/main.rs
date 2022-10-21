mod cir;
mod constexpr;
mod errors;
mod lexer;
mod llvm;
mod modules;
mod parser;
mod semantic;

use clap::Parser;
use colored::Colorize;
use semantic::{namespace::Identifier, types};
use std::process::Command;
use std::{
	ffi::OsString,
	io::{self, Write},
	sync::{atomic::Ordering, Arc, Mutex},
	time::Instant,
};

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct ComuneCLI {
	// Verbose flag
	#[clap(short = 'v', long = "verbose", default_value_t = false, value_parser)]
	verbose: bool,

	#[clap(value_parser, default_value = "")]
	input_file: OsString,

	#[clap(long = "emit-llvm", default_value_t = false, value_parser)]
	emit_llvm: bool,

	#[clap(long = "backtrace", default_value_t = false, value_parser)]
	backtrace: bool,

	#[clap(short = 'j', long = "jobs", default_value_t = 0, value_parser)]
	num_jobs: usize,
}

fn main() -> color_eyre::eyre::Result<()> {
	color_eyre::install()?;

	let args = ComuneCLI::parse();
	let build_time = Instant::now();

	if args.input_file.is_empty() {
		println!("{} {}", "fatal:".red().bold(), "no input module");
		return Ok(());
	}

	rayon::ThreadPoolBuilder::new()
		.num_threads(args.num_jobs)
		.build_global()
		.unwrap();

	let manager_state = Arc::new(modules::ManagerState {
		working_dir: "./test".into(),
		import_paths: vec![],
		max_threads: args.num_jobs,
		verbose_output: args.verbose,
		output_modules: Mutex::new(vec![]),
		emit_llvm: args.emit_llvm,
		backtrace_on_error: args.backtrace,
	});

	// Launch multithreaded compilation

	rayon::in_place_scope(|s| {
		let _ = modules::launch_module_compilation(
			manager_state.clone(),
			Identifier::from_name(args.input_file.clone().to_string_lossy().into(), true),
			s,
		);
	});

	if errors::ERROR_COUNT.load(Ordering::Acquire) > 0 {
		println!(
			"\n{:>10} build due to {} previous error(s)\n",
			"aborted".bold().red(),
			errors::ERROR_COUNT.load(Ordering::Acquire)
		);
		return Ok(());
	}

	let compile_time = build_time.elapsed();

	// Link into binary

	let mut output_file = modules::get_out_folder(&manager_state);
	output_file.push(args.input_file);
	output_file.set_extension("");

	let build_name = output_file
		.file_name()
		.unwrap()
		.to_string_lossy()
		.to_string();

	println!(
		"\n{:>10} target {}",
		"linking".bold().green(),
		build_name.bold()
	);

	// Link into executable
	// We use clang here because fuck dude i don't know how to use ld manually
	let mut output = Command::new("clang");

	for module in &*manager_state.output_modules.lock().unwrap() {
		output.arg(module);
	}

	let output_result = output
		.arg("-nodefaultlibs")
		.arg("-lc")
		.arg("-fno-rtti")
		.arg("-fno-exceptions")
		.arg("-o")
		.arg(output_file)
		.output()
		.expect("fatal: failed to link executable");

	io::stdout().write(&output_result.stdout).unwrap();
	io::stderr().write(&output_result.stderr).unwrap();

	let link_time = build_time.elapsed() - compile_time;

	println!(
		"{:>10} building {} in {}s (compile: {}s, link: {}s)\n",
		"finished".bold().green(),
		build_name.bold(),
		build_time.elapsed().as_millis() as f64 / 1000.0,
		compile_time.as_millis() as f64 / 1000.0,
		link_time.as_millis() as f64 / 1000.0
	);

	Ok(())
}
