use clap::{Parser, ArgAction};
use colored::Colorize;
use crate::backend::Backend;
use crate::llvm::LLVMBackend;
use std::fs;
use std::path::PathBuf;

// ironic, isn't it?
#[cfg(not(feature = "concurrent"))]
use std::sync::{RwLock, Arc};

use std::{ffi::OsString, sync::atomic::Ordering, time::Instant, io::Write};

use crate::ast::module::Identifier;
use crate::driver::{Compiler, COMUNE_TOOLCHAIN_KEY, JobSpawner, get_file_suffix};
use crate::errors;

#[derive(Parser, Debug)]
#[clap(author, version, about, long_about = None)]
pub struct ComuneCLI {
	#[clap(short = 'v', long = "verbose", default_value_t = false, value_parser)]
	pub verbose: bool,

	#[clap(value_parser)]
	pub input_files: Vec<OsString>,

	#[clap(long = "backtrace", default_value_t = false, value_parser)]
	pub backtrace: bool,

	#[clap(short = 'j', long = "jobs", default_value_t = 0, value_parser)]
	pub num_jobs: usize,

	#[clap(long = "out-dir", default_value = "./", value_parser)]
	pub output_dir: OsString,

	#[clap(short = 'o', long = "output", default_value = "a.out", value_parser)]
	pub output_file: OsString,

	#[clap(short = 'e', long = "emit", value_parser)]
	pub emit_types: Vec<String>,

	#[clap(short = 'O', default_value_t = 0, value_parser)]
	pub opt_level: u32,

	#[clap(short = 'd', long = "debug-info", action = ArgAction::Set, default_value_t = true, value_parser)]
	pub debug_info: bool,

	#[clap(long = "no-std", default_value_t = false, value_parser)]
	pub no_std: bool,
}

pub fn run(args: ComuneCLI) -> Result<(), ()> {
	let build_time = Instant::now();

	if args.input_files.is_empty() {
		eprintln!("{} no input modules", "fatal:".red().bold());
		return Err(())
	}

	if let Err(e) = std::env::var(COMUNE_TOOLCHAIN_KEY) {
		eprintln!(
			"{} no comune toolchain found!\nplease point the {COMUNE_TOOLCHAIN_KEY} environment variable to a valid comune toolchain. ({e})",
			"error:".red().bold(),
		);
		return Err(())
	}

	let mut emit_types = vec![];

	for ty in &args.emit_types {
		emit_types.extend(ty.as_str().split(','));
	}

	if emit_types.contains(&"none") && emit_types.len() != 1 {
		eprintln!(
			"{} emit type `none` cannot be used in combination with other options.",
			"error:".red().bold()
		);
		return Err(())
	}

	#[cfg(feature = "concurrent")]
	let thread_pool = rayon::ThreadPoolBuilder::new()
		.num_threads(args.num_jobs)
		.build()
		.unwrap();


	if args.backtrace {
		unsafe {
			errors::CAPTURE_BACKTRACE = true;
		}
	}

	let compiler = Compiler::<LLVMBackend>::new(
		&[],
		args.verbose,
		args.output_dir,
		args.output_file,
		&emit_types,
		args.opt_level,
		args.debug_info,
		args.no_std,
	);
	
	#[cfg(not(feature = "concurrent"))]
	{
		// Launch single-threaded compilation
		let jobs = Arc::new(RwLock::new(vec![]));
		let spawner = JobSpawner::Synchronous(jobs.clone());

		for input_file in &args.input_files {
			let input_file = fs::canonicalize(input_file).unwrap();
			let module_name = Identifier::from_name(get_file_suffix(&input_file).unwrap(), true);

			let Ok(parsers) = compiler.launch_module_compilation(
				input_file,
				module_name,
				spawner.clone(),
			) else {
				continue
			};

			for parser in parsers {
				let _ = compiler.generate_typed_interface(
					parser, 
					spawner.clone()
				);
			}
		}

		for job in jobs.write().unwrap().drain(..) {
			compiler.finish_module_job(job)
		}
	}
	
	#[cfg(feature = "concurrent")]
	{
		// Launch multithreaded compilation
		thread_pool.in_place_scope(|s| {
			let spawner = JobSpawner::Concurrent(s);

			for input_file in &args.input_files {
				let input_file = fs::canonicalize(input_file).unwrap();
				let module_name = Identifier::from_name(get_file_suffix(&input_file).unwrap(), true);

				let Ok(parsers) = compiler.launch_module_compilation(
					input_file,
					module_name,
					spawner.clone(),
				) else {
					continue
				};

				for parser in parsers {
					let _ = compiler.generate_typed_interface(
						parser, 
						spawner.clone()
					);
				}
			}
		});
	}

	if !check_last_phase_ok(&compiler) {
		await_output_written();
		return Err(())
	}

	#[cfg(not(feature = "concurrent"))]
	match compiler.generate_monomorph_module() {
		Ok(()) => {}
		Err(_) => {
			errors::ERROR_COUNT.fetch_add(1, Ordering::Relaxed);
		}
	};

	#[cfg(feature = "concurrent")]
	thread_pool.in_place_scope(|_| {
		match compiler.generate_monomorph_module() {
			Ok(()) => {}
			Err(_) => {
				compiler.error_count.fetch_add(1, Ordering::Relaxed);
			}
		};
	});
	

	if !check_last_phase_ok(&compiler) {
		await_output_written();
		return Err(())
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

	await_output_written();
	Ok(())
}

fn check_last_phase_ok<T: Backend>(compiler: &Compiler<'_, T>) -> bool {
	if compiler.error_count.load(Ordering::Acquire) > 0 {
		let mut io = std::io::stderr().lock();

		write!(
			io,
			"\n{:>10} build due to {} previous error(s)\n\n",
				"aborted".bold().red(),
				compiler.error_count.load(Ordering::Acquire)
		).unwrap();

		// Block until the error logger is done writing, so we don't exit early

		return false;
	}

	true
}

fn await_output_written() {
	// Block until all output is written
	let _ = std::io::stdout().lock();
	let _ = std::io::stderr().lock();
}