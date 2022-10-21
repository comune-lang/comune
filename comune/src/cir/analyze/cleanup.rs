// cleanup passes - remove no-ops etc
use super::CIRPassMut;
use crate::cir::{CIRFunction, CIRStmt, Operand, RValue};

pub struct RemoveNoOps;

impl CIRPassMut for RemoveNoOps {
	fn on_function(&self, func: &mut CIRFunction) {
		let mut indices = vec![];

		for i in 0..func.blocks.len() {
			for j in 0..func.blocks[i].len() {
				if let CIRStmt::Expression(expr) = &func.blocks[i][j] {
					if !rval_has_side_effects(expr) {
						indices.push((i, j));
					}
				}
			}
		}

		for (i, j) in indices {
			func.blocks[i].remove(j);
		}
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
		Operand::FnCall(_, _, _) => true,
		Operand::LValue(_) => true, // TODO: Refine this
		_ => false,
	}
}
