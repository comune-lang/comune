mod ast;
mod cir;
mod clang;
mod constexpr;
mod driver;
mod errors;
mod lexer;
mod llvm;
mod parser;

use ast::module::Name;
use ast::{module::Identifier, types};
use clap::Parser;
use colored::Colorize;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::RwLock;
use std::{
	ffi::OsString,
	io::{self, Write},
	sync::{atomic::Ordering, Arc, Mutex},
	time::Instant,
};

use crate::driver::EmitType;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
struct ComuneCLI {
	// Verbose flag
	#[clap(short = 'v', long = "verbose", default_value_t = false, value_parser)]
	verbose: bool,

	#[clap(value_parser)]
	input_files: Vec<OsString>,

	#[clap(long = "backtrace", default_value_t = false, value_parser)]
	backtrace: bool,

	#[clap(short = 'j', long = "jobs", default_value_t = 0, value_parser)]
	num_jobs: usize,

	#[clap(long = "out-dir", default_value = "./", value_parser)]
	output_dir: OsString,

	#[clap(short = 'o', long = "output", default_value = "a.out", value_parser)]
	output_file: OsString,

	#[clap(short = 'e', long = "emit", value_parser)]
	emit_types: Vec<String>,
}

fn main() -> color_eyre::eyre::Result<()> {
	color_eyre::install()?;

	let args = ComuneCLI::parse();
	let build_time = Instant::now();

	if args.input_files.is_empty() {
		println!("{} no input modules", "fatal:".red().bold());
		return Ok(());
	}

	let mut emit_types = vec![];

	for ty in args.emit_types {
		emit_types.extend(ty.split(',').map(|arg| {
			EmitType::from_string(arg)
				.unwrap_or_else(|| panic!("invalid argument to --emit: {arg}"))
		}));
	}

	if emit_types.is_empty() {
		emit_types = vec![EmitType::Binary];
	}

	rayon::ThreadPoolBuilder::new()
		.num_threads(args.num_jobs)
		.build_global()
		.unwrap();

	let manager_state = Arc::new(driver::ManagerState {
		libcomune_dir: "./libcomune".into(),
		import_paths: vec![],
		max_threads: args.num_jobs,
		verbose_output: args.verbose,
		output_modules: Mutex::new(vec![]),
		output_dir: args.output_dir,
		emit_types,
		backtrace_on_error: args.backtrace,
		module_states: RwLock::default(),
	});

	if manager_state.backtrace_on_error {
		unsafe {
			errors::CAPTURE_BACKTRACE = true;
		}
	}

	// Launch multithreaded compilation

	let error_sender = errors::spawn_logger(args.backtrace);

	rayon::in_place_scope(|s| {
		for input_file in &args.input_files {
			let input_file = fs::canonicalize(input_file).unwrap();
			let module_name = Identifier::from_name(get_file_suffix(&input_file).unwrap(), true);

			let _ = driver::launch_module_compilation(
				manager_state.clone(),
				input_file,
				module_name,
				error_sender.clone(),
				s,
			);
		}
	});

	if errors::ERROR_COUNT.load(Ordering::Acquire) > 0 {
		error_sender
			.send(errors::CMNMessageLog::Raw(format!(
				"\n{:>10} build due to {} previous error(s)\n\n",
				"aborted".bold().red(),
				errors::ERROR_COUNT.load(Ordering::Acquire)
			)))
			.unwrap();

		// Block until the error logger is done writing, so we don't exit early
		let _ = std::io::stdout().lock();

		return Ok(());
	}

	let compile_time = build_time.elapsed();

	// Link into binary

	let mut output_file = PathBuf::from(&manager_state.output_dir);
	output_file.push(args.output_file);

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

	// invoke linker for all EmitTypes that need it
	// We use clang here because fuck dude i don't know how to use ld manually

	let mut link_errors = 0;

	for emit_type in &manager_state.emit_types {
		if let EmitType::Binary | EmitType::DynamicLib | EmitType::StaticLib = emit_type {
			let mut output = Command::new("clang");

			for module in &*manager_state.output_modules.lock().unwrap() {
				output.arg(module);
			}

			output
				.arg("-nodefaultlibs")
				.arg("-lstdc++")
				.arg("-lc")
				//.arg("-fno-rtti")
				//.arg("-fno-exceptions")
				.arg("-fdiagnostics-color=always")
				.arg("-no-pie");

			match emit_type {
				EmitType::Binary => {
					output.arg("-o").arg(output_file.clone());
				}

				_ => {}
			}

			let output_result = output.output().expect("fatal: failed to invoke linker");

			if !output_result.status.success() {
				link_errors += 1;
				println!("");
				io::stdout().write_all(&output_result.stdout).unwrap();
				io::stderr().write_all(&output_result.stderr).unwrap();
				println!("");
			}
		}
	}

	if !manager_state.emit_types.contains(&EmitType::Object) {
		for module in &*manager_state.output_modules.lock().unwrap() {
			let _ = fs::remove_file(module);
		}
	}

	if link_errors > 0 {
		std::process::exit(1);
	}

	let link_time = build_time.elapsed() - compile_time;

	println!(
		"{:>10} building in {}s (compile: {}s, link: {}s)\n",
		"finished".bold().green(),
		build_time.elapsed().as_millis() as f64 / 1000.0,
		compile_time.as_millis() as f64 / 1000.0,
		link_time.as_millis() as f64 / 1000.0
	);

	// Block until all output is written
	let _ = std::io::stdout().lock();

	Ok(())
}

fn get_file_suffix(path: &Path) -> Option<Name> {
	let mut name = path.file_name()?.to_string_lossy().to_string();
	name.truncate(name.rfind('.').unwrap_or(name.len()));

	Some(name.into())
}
