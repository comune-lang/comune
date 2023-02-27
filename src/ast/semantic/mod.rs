use std::sync::Arc;

use crate::{
	driver::ManagerState,
	parser::{ComuneResult, Parser},
};

use self::func::validate_function_body;

use super::module::{ModuleImpl, ModuleInterface};

pub mod expr;
pub mod func;
pub mod ty;

pub fn validate_module_impl(
	interface: &ModuleInterface,
	module_impl: &mut ModuleImpl,
) -> ComuneResult<()> {
	for (proto, ast) in &mut module_impl.fn_impls {
		let mut scope = proto.read().unwrap().path.clone();
		scope.path.pop();

		validate_function_body(scope.clone(), &*proto.read().unwrap(), ast, interface)?
	}

	Ok(())
}

pub fn validate_interface(_state: &Arc<ManagerState>, parser: &mut Parser) -> ComuneResult<()> {
	// At this point, all imports have been resolved, so validate namespace-level types
	ty::resolve_interface_types(&mut parser.interface)?;

	// Check for cyclical dependencies without indirection
	// TODO: Nice error reporting for this
	ty::check_module_cyclical_deps(&mut parser.interface)?;

	Ok(())
}
