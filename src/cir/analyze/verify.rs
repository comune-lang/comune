// verify pass - basic sanity check for CIRModules

use super::CIRPass;
use crate::{
	ast::TokenData,
	cir::{CIRFunction, CIRStmt},
	errors::{CMNError, CMNErrorCode},
};
pub struct CFGWalkerTest;
pub struct Verify;

impl CIRPass for Verify {
	fn on_function(&self, func: &CIRFunction) -> Vec<(CMNError, TokenData)> {
		let mut errors = vec![];

		// Check for empty blocks & blocks without terminators
		for block in &func.blocks {
			if let Some(last) = block.items.last() {
				if !matches!(
					last,
					CIRStmt::Return(_)
						| CIRStmt::Switch(..) | CIRStmt::Jump(_)
						| CIRStmt::FnCall { .. }
				) {
					errors.push((
						CMNError::new(CMNErrorCode::Custom(
							"cIR block doesn't have a terminator".to_string(),
						)),
						(0, 0),
					));
				}
			} else {
				errors.push((
					CMNError::new(CMNErrorCode::Custom(
						"found empty block during cIR verification!".to_string(),
					)),
					(0, 0),
				))
			}
		}

		errors
	}
}
