// verify pass - basic sanity check for CIRModules

use super::CIRPass;
use crate::cir::{CIRFunction, CIRStmt};

pub struct Verify;

impl CIRPass for Verify {
	fn on_function(&self, func: &CIRFunction) {
		for block in &func.blocks {
			if let CIRStmt::Return(_) | CIRStmt::Branch(..) | CIRStmt::Jump(_) =
				block.last().unwrap()
			{
				continue;
			} else {
				panic!("cIR block doesn't have a terminator!"); // TODO: Proper error reporting
			}
		}
	}
}
