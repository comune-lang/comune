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
		emit_type: &str,
		out_path: &Path,
	);
	
	fn link(compiler: &Compiler<Self>, link_type: &str) -> ComuneResult<()>;

	fn supported_emit_types() -> &'static [&'static str];
	fn supported_link_types() -> &'static [&'static str];
	fn default_link_types() -> &'static [&'static str];
	fn required_emit_types(link_type: &str) -> &'static [&'static str];
}
