// verify pass - basic sanity check for CIRModules

use super::CIRPass;
use crate::{
	cir::{CIRFunction, CIRStmt},
	errors::{CMNError, CMNErrorCode},
	parser::AnalyzeResult,
	semantic::ast::TokenData,
};

pub struct Verify;

impl CIRPass for Verify {
	fn on_function(&self, func: &CIRFunction) -> Vec<(CMNError, TokenData)> {
		let mut errors = vec![];

		for block in &func.blocks {
			if let CIRStmt::Return(_) | CIRStmt::Branch(..) | CIRStmt::Jump(_) =
				block.last().unwrap()
			{
				continue;
			} else {
				errors.push((
					CMNError::new(CMNErrorCode::Custom(
						"cIR block doesn't have a terminator!".to_string(),
					)),
					(0, 0),
				)); // TODO: Proper error reporting
			}
		}

		errors
	}
}
