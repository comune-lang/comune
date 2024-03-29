use std::sync::Arc;

use crate::{
	lexer::Token,
	parser::{ComuneResult, Parser},
};

use self::func::validate_function_body;

use super::{
	get_attribute,
	module::{ModuleImpl, ModuleInterface, ModuleItemInterface},
	traits::{LangTrait, TraitRef},
};

pub mod expr;
pub mod func;
pub mod stmt;
pub mod ty;

pub fn validate_module_impl(
	interface: &ModuleInterface,
	module_impl: &mut ModuleImpl,
) -> ComuneResult<()> {
	for (proto, ast) in &mut module_impl.fn_impls {
		validate_function_body(interface.name.clone(), &*proto, ast, interface)?
	}

	Ok(())
}

pub fn validate_interface(parser: &mut Parser) -> ComuneResult<()> {
	// At this point, all imports have been resolved, so validate namespace-level types
	ty::resolve_interface_types(parser)?;

	// Check for cyclical dependencies without indirection
	// TODO: Nice error reporting for this
	ty::check_module_cyclical_deps(&mut parser.interface)?;

	validate_attributes(&mut parser.interface)?;

	parser.interface.is_typed = true;

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

					let lang_trait = match name.as_str() {
						"Sized" => LangTrait::Sized,
						"Move" => LangTrait::Move,
						"Copy" => LangTrait::Copy,
						"Send" => LangTrait::Send,
						"Sync" => LangTrait::Sync,
						_ => panic!(),
					};

					interface.impl_solver.register_lang_trait(
						lang_trait,
						TraitRef {
							def: Some(Arc::downgrade(tr)),
							name: id.clone(),
							scope: Arc::new(interface.name.clone()),
							args: vec![],
						},
					);
				}
			}

			_ => {}
		}
	}

	Ok(())
}
