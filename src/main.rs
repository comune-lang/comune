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
use errors::CMNMessageLog;
use itertools::Itertools;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::mpsc::Sender;
use std::sync::RwLock;
use std::{
	ffi::OsString,
	io::{self, Write},
	sync::{atomic::Ordering, Arc, Mutex},
	time::Instant,
};

use crate::cir::monoize::MonomorphServer;
use crate::driver::{EmitType, COMUNE_TOOLCHAIN_KEY};

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
		eprintln!("{} no input modules", "fatal:".red().bold());
		std::process::exit(1);
	}

	if let Err(e) = std::env::var(COMUNE_TOOLCHAIN_KEY) {
		eprintln!(
			"{} no comune toolchain found!\nplease point the {COMUNE_TOOLCHAIN_KEY} environment variable to a valid comune toolchain. ({e})",
			"error:".red().bold(),
		);
		std::process::exit(1);
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
	
	let emit_types = emit_types.into_iter().unique().collect_vec();

	if emit_types.contains(&EmitType::None) && emit_types.len() != 1 {
		eprintln!("{} emit type `none` cannot be used in combination with other options.", "error:".red().bold());
		std::process::exit(1);
	}

	rayon::ThreadPoolBuilder::new()
		.num_threads(args.num_jobs)
		.build_global()
		.unwrap();

	let compiler_state = Arc::new(driver::CompilerState {
		import_paths: vec![],
		max_threads: args.num_jobs,
		verbose_output: args.verbose,
		output_modules: Mutex::new(vec![]),
		output_dir: args.output_dir,
		emit_types,
		backtrace_on_error: args.backtrace,
		module_states: RwLock::default(),
		monomorph_server: MonomorphServer::new(),
	});

	if compiler_state.backtrace_on_error {
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
				compiler_state.clone(),
				input_file,
				module_name,
				error_sender.clone(),
				s,
			);
		}
	});

	if !check_last_phase_ok(&error_sender) {
		return Ok(());
	}

	rayon::in_place_scope(|_| {
		match driver::generate_monomorph_module(compiler_state.clone(), &error_sender) {
			Ok(()) => {}
			Err(_) => {
				errors::ERROR_COUNT.fetch_add(1, Ordering::Relaxed);
			}
		};
	});

	if !check_last_phase_ok(&error_sender) {
		std::process::exit(1);
	}

	let compile_time = build_time.elapsed();

	// Link into binary

	let mut output_file = PathBuf::from(&compiler_state.output_dir);
	output_file.push(args.output_file);

	let build_name = output_file
		.file_name()
		.unwrap()
		.to_string_lossy()
		.to_string();

	println!();
	// invoke linker for all EmitTypes that need it
	// We use clang here because fuck dude i don't know how to use ld manually

	let mut link_errors = 0;
	let mut link_jobs = 0;

	for emit_type in &compiler_state.emit_types {
		if let EmitType::Binary | EmitType::DynamicLib | EmitType::StaticLib = emit_type {
			link_jobs += 1;
			
			println!(
				"{:>10} target {}",
				"linking".bold().green(),
				build_name.bold()
			);

			let mut output = Command::new("clang");

			for module in &*compiler_state.output_modules.lock().unwrap() {
				output.arg(module);
			}

			output
				.arg("-lstdc++")
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

	if !compiler_state.emit_types.contains(&EmitType::Object) {
		for module in &*compiler_state.output_modules.lock().unwrap() {
			let _ = fs::remove_file(module);
		}
	}

	if link_errors > 0 {
		std::process::exit(1);
	}

	let link_time = build_time.elapsed() - compile_time;

	print!(
		"{:>10} building in {}s",
		"finished".bold().green(),
		build_time.elapsed().as_millis() as f64 / 1000.0,
	);

	if link_jobs > 0 {
		print!(
			" (compile: {}s, link: {}s)",
			compile_time.as_millis() as f64 / 1000.0,
			link_time.as_millis() as f64 / 1000.0
		);
	}
	
	print!("\n\n");

	// Block until all output is written
	let _ = std::io::stdout().lock();

	Ok(())
}

fn get_file_suffix(path: &Path) -> Option<Name> {
	let mut name = path.file_name()?.to_string_lossy().to_string();
	name.truncate(name.rfind('.').unwrap_or(name.len()));

	Some(name.into())
}

fn check_last_phase_ok(error_sender: &Sender<CMNMessageLog>) -> bool {
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

		return false;
	}

	true
}
