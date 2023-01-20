// cleanup passes - remove no-ops etc
use super::CIRPassMut;
use crate::{
	ast::TokenData,
	cir::{CIRFunction, CIRStmt},
	errors::CMNError,
};

pub struct RemoveNoOps;

impl CIRPassMut for RemoveNoOps {
	fn on_function(&self, func: &mut CIRFunction) -> Vec<(CMNError, TokenData)> {
		let mut indices = vec![];

		for i in 0..func.blocks.len() {
			let mut offset = 0;
			for j in 0..func.blocks[i].len() {
				if let CIRStmt::Expression(expr, _) = &func.blocks[i][j] {
					indices.push((i, j - offset));
					offset += 1;
				}
			}
		}

		for (i, j) in indices {
			func.blocks[i].remove(j);
		}

		vec![]
	}
}
