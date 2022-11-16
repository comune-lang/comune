// cleanup passes - remove no-ops etc
use super::CIRPassMut;
use crate::{
	cir::{CIRFunction, CIRStmt, Operand, RValue},
	errors::CMNError,
	semantic::TokenData,
};

pub struct RemoveNoOps;

impl CIRPassMut for RemoveNoOps {
	fn on_function(&self, func: &mut CIRFunction) -> Vec<(CMNError, TokenData)> {
		let mut indices = vec![];

		for i in 0..func.blocks.len() {
			let mut offset = 0;
			for j in 0..func.blocks[i].len() {
				if let CIRStmt::Expression(expr, _) = &func.blocks[i][j] {
					if !rval_has_side_effects(expr) {
						indices.push((i, j - offset));
						offset += 1;
					}
				}
			}
		}

		for (i, j) in indices {
			func.blocks[i].remove(j);
		}

		vec![]
	}
}

fn rval_has_side_effects(expr: &RValue) -> bool {
	match expr {
		RValue::Atom(_, _, op) => op_has_side_effects(op),
		RValue::Cons(_, [(_, lhs), (_, rhs)], _) => {
			op_has_side_effects(lhs) || op_has_side_effects(rhs)
		}
		RValue::Cast { val, .. } => op_has_side_effects(val),
	}
}

fn op_has_side_effects(expr: &Operand) -> bool {
	match expr {
		Operand::FnCall(..) => true,
		_ => false,
	}
}
