// verify pass - basic sanity check for CIRModules

use super::CIRPass;
use crate::{
	cir::{CIRFunction, CIRStmt},
	errors::{CMNError, CMNErrorCode},
	lexer::SrcSpan,
};
pub struct CFGWalkerTest;
pub struct Verify;

impl CIRPass for Verify {
	fn on_function(&self, func: &CIRFunction) -> Vec<(CMNError, SrcSpan)> {
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
						SrcSpan::new(),
					));
				}
			} else {
				errors.push((
					CMNError::new(CMNErrorCode::Custom(
						"found empty block during cIR verification!".to_string(),
					)),
					SrcSpan::new(),
				))
			}
		}

		errors
	}
}
