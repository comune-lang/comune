use std::ffi::OsString;

use comune::cli::ComuneCLI;

fn check_file(file: impl Into<OsString>) -> bool {
	comune::cli::run(ComuneCLI {
		verbose: false,
		input_files: vec![file.into()],
		backtrace: false,
		num_jobs: 1,
		output_dir: "".into(),
		output_file: "".into(),
		emit_types: vec!["none".into()],
	}).is_ok()
}


#[test]
fn basic_test() {
	assert!(check_file("tests/basic.co"));
}