use std::sync::Arc;

use crate::{
	driver::ManagerState,
	parser::{ComuneResult, Parser}, lexer::Token,
};

use self::func::validate_function_body;

use super::{module::{ModuleImpl, ModuleInterface, ModuleItemInterface}, get_attribute, traits::{LangTrait, TraitRef}};

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

	validate_attributes(&mut parser.interface)?;

	Ok(())
}


fn validate_attributes(interface: &mut ModuleInterface) -> ComuneResult<()> {
	
	for (id, child) in &interface.children {
		match child {

			ModuleItemInterface::Trait(tr) => {
			
				if let Some(lang_attrib) = get_attribute(&tr.read().unwrap().attributes, "lang") {
					let Some(names) = lang_attrib.args.get(0) else  {
						panic!();
					};

					let [Token::Name(name)] = names.as_slice() else {
						panic!()
					};

					let lang_trait = match &**name {
						"Sized" => LangTrait::Sized,
						"Copy" => LangTrait::Copy,
						"Clone" => LangTrait::Clone,
						"Drop" => LangTrait::Drop,
						"Send" => LangTrait::Send,
						"Sync" => LangTrait::Sync,
						_ => panic!(),
					};

					interface.trait_solver.register_lang_trait(lang_trait, TraitRef {
						def: Arc::downgrade(tr),
						name: id.clone(),
						args: vec![],
					});
				}
			}
			
			_ => {}
		}
	}

	Ok(())
}