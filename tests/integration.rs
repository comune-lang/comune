use std::ffi::OsString;

use comune::cli::ComuneCLI;

fn default_cli(file: impl Into<OsString>) -> ComuneCLI {
	ComuneCLI {
		verbose: false,
		input_files: vec![file.into()],
		backtrace: false,
		num_jobs: 1,
		output_dir: "".into(),
		output_file: "".into(),
		emit_types: vec!["none".into()],
		debug_info: true,
		opt_level: 0,
		no_std: false,
	}
}

fn check_file(file: impl Into<OsString>) -> bool {
	comune::cli::run(default_cli(file)).is_ok()
}


#[test]
fn basic_test() {
	assert!(check_file("tests/basic.co"));
}

#[test]
fn no_std_test() {
	assert!(comune::cli::run(ComuneCLI {
		no_std: true,
		..default_cli("tests/no_std.co")
	}).is_ok());
}