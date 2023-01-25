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
			if let Some(last) = block.last() {
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

#[derive(Clone)]
struct CFGWalkerTestState {
	pub blocks_walked: Vec<usize>,
}

impl CIRPass for CFGWalkerTest {
	fn on_function(&self, func: &CIRFunction) -> Vec<(CMNError, TokenData)> {
		println!("\n\nfunction {func}:\n\n");
		func.walk_cfg(
			CFGWalkerTestState { blocks_walked: vec![] },
			|state, _, block| {
				
				if state.blocks_walked.is_empty() || *state.blocks_walked.last().unwrap() != block {
					state.blocks_walked.push(block);
					println!("walked {:?}", state.blocks_walked);
				}

				Ok(())
			}
		);

		vec![]
	}
}