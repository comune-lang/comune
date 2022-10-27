// the comune borrow checker

use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use super::CIRPass;
use crate::cir::{CIRFunction, CIRStmt};

pub struct BorrowCheck;

impl CIRPass for BorrowCheck {
	fn on_function(&self, func: &CIRFunction) {
		&func.blocks.par_iter().for_each(|block| todo!());
	}
}
