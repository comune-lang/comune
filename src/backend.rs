use std::path::Path;

use crate::{cir::CIRModule, driver::Compiler, parser::ComuneResult};

pub trait Backend {
	type Output<'out>;

	fn create_instance(compiler: &Compiler<Self>) -> Self;

	fn generate_code<'out>(
		&'out self,
		module: &CIRModule,
		compiler: &Compiler<Self>,
		module_name: &str,
		source_file: &str,
	) -> ComuneResult<Self::Output<'out>>;

	fn emit(
		&self,
		compiler: &Compiler<Self>,
		output: &Self::Output<'_>,
		emit_types: &[&str],
		out_path: &Path,
	);
	
	fn link(compiler: &Compiler<Self>, link_type: &str) -> ComuneResult<()>;

	const SUPPORTED_EMIT_TYPES: &'static [&'static str];
	const SUPPORTED_LINK_TYPES: &'static [&'static str];
	const DEFAULT_LINK_TYPES: &'static [&'static str];

	fn get_required_emit_types(link_type: &str) -> &'static [&'static str];
}
