use clap::Parser;
use colored::Colorize;
use comune::llvm::LLVMBackend;
use std::fs;
use std::path::PathBuf;
use std::sync::mpsc::Sender;
use std::{ffi::OsString, sync::atomic::Ordering, time::Instant};

use comune::ast::module::Identifier;
use comune::driver::{Compiler, COMUNE_TOOLCHAIN_KEY};
use comune::errors::{self, MessageLog};

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

	for ty in &args.emit_types {
		emit_types.push(ty.as_str());
	}

	if emit_types.contains(&"none") && emit_types.len() != 1 {
		eprintln!(
			"{} emit type `none` cannot be used in combination with other options.",
			"error:".red().bold()
		);
		std::process::exit(1);
	}

	rayon::ThreadPoolBuilder::new()
		.num_threads(args.num_jobs)
		.build_global()
		.unwrap();

	if args.backtrace {
		unsafe {
			comune::errors::CAPTURE_BACKTRACE = true;
		}
	}

	let compiler = Compiler::<LLVMBackend>::new(
		&[],
		args.verbose,
		args.output_dir,
		args.output_file,
		&emit_types,
		1,
	);

	// Launch multithreaded compilation

	let error_sender = comune::errors::spawn_logger(args.backtrace);

	rayon::in_place_scope(|s| {
		for input_file in &args.input_files {
			let input_file = fs::canonicalize(input_file).unwrap();
			let module_name =
				Identifier::from_name(comune::driver::get_file_suffix(&input_file).unwrap(), true);

			let _ = compiler.launch_module_compilation(
				input_file,
				module_name,
				error_sender.clone(),
				s,
			);
		}
	});

	if !check_last_phase_ok(&error_sender) {
		std::process::exit(1);
	}

	rayon::in_place_scope(|_| {
		match compiler.generate_monomorph_module(&error_sender) {
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
	let output_file = PathBuf::from(&compiler.output_file);

	println!();

	if compiler.requires_linking() {
		let build_name = output_file
			.file_name()
			.unwrap()
			.to_string_lossy()
			.to_string();

		println!(
			"{:>10} target {}",
			"linking".bold().green(),
			build_name.bold()
		);

		match compiler.link() {
			Ok(_) => {}
			Err(_) => std::process::exit(1),
		}

		let link_time = build_time.elapsed() - compile_time;

		println!(
			"{:>10} building in {}s (compile: {}s, link: {}s)\n",
			"finished".bold().green(),
			build_time.elapsed().as_millis() as f64 / 1000.0,
			compile_time.as_millis() as f64 / 1000.0,
			link_time.as_millis() as f64 / 1000.0
		);
	} else {
		println!(
			"{:>10} building in {}s\n",
			"finished".bold().green(),
			build_time.elapsed().as_millis() as f64 / 1000.0,
		);
	}

	/*for emit_type in compiler.emit_types {
		if let EmitType::Binary | EmitType::DynamicLib | EmitType::StaticLib = emit_type {

			let mut output = Command::new("clang");

			for module in &*compiler.output_modules.lock().unwrap() {
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

	if !compiler.emit_types.contains(&EmitType::Object) {
		for module in &*compiler.output_modules.lock().unwrap() {
			let _ = fs::remove_file(module);
		}
	}*/

	// Block until all output is written
	let _ = std::io::stdout().lock();

	Ok(())
}

fn check_last_phase_ok(error_sender: &Sender<MessageLog>) -> bool {
	if errors::ERROR_COUNT.load(Ordering::Acquire) > 0 {
		error_sender
			.send(errors::MessageLog::Raw(format!(
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
