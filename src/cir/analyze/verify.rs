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

		// Check for empty blocks & blocks without terminators
		for block in &func.blocks {
			if let Some(last) = block.last() {
				if !matches!(last, CIRStmt::Return(_) | CIRStmt::Switch(..) | CIRStmt::Jump(_)) {
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

		// Perform basic typecheck
		for block in &func.blocks {
			for stmt in block {
				match stmt {					
					CIRStmt::Assignment((lval, _), (rval, _)) => {
						//let lval_ty = &func.variables[lval.local].0;
						//let rval_ty = rval.get_type();

						//if lval_ty != rval_ty {
						//	errors.push((
						//		CMNError::new(CMNErrorCode::Custom(
						//			format!("assignment type mismatch in cIR! {lval_ty} != {rval_ty}")
						//		)),
						//		(0, 0)
						//	))
						//}
					},
					
					CIRStmt::Switch(switch, branches, _) => {
						let switch_ty = switch.get_type();

						for (branch_ty, ..) in branches {
							if branch_ty != switch_ty {
								errors.push((
									CMNError::new(CMNErrorCode::Custom(
										format!("switch type mismatch in cIR! {branch_ty} != {switch_ty}")
									)),
									(0, 0)
								))
							}
						}
					},
					
					_ => {}
				}
			}
		}


		errors
	}
}
