// verify pass - basic sanity check for CIRModules

use super::CIRPass;
use crate::{
	cir::{CIRFunction, CIRStmt},
	errors::{CMNError, CMNErrorCode},
	ast::TokenData,
};

pub struct Verify;

impl CIRPass for Verify {
	fn on_function(&self, func: &CIRFunction) -> Vec<(CMNError, TokenData)> {
		let mut errors = vec![];

		for block in &func.blocks {
			if matches!(
				block.last().unwrap(),
				CIRStmt::Return(_) | CIRStmt::Branch(..) | CIRStmt::Jump(_)
			) {
				continue;
			} else {
				errors.push((
					CMNError::new(CMNErrorCode::Custom(
						"cIR block doesn't have a terminator".to_string(),
					)),
					(0, 0),
				)); // TODO: Proper error reporting
			}
		}

		errors
	}
}
