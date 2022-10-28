// the comune borrow checker

use std::collections::HashMap;

use super::CIRPassMut;
use crate::cir::{CIRFunction, CIRStmt, LValue, RValue, Operand, CIRType, PlaceElem};

pub struct BorrowCheck;

struct Borrow {
	place: LValue,
}


#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum LivenessState {
	Uninit,
	Live,
	Moved,
	PartialMoved,
	Dropped
}

#[derive(Clone)]
struct LiveVarCheckState {
	// TODO: Create Path type, for canonicalized LValues
	liveness: HashMap<LValue, LivenessState>,
}

impl LiveVarCheckState {
	fn set_all_sublocations(&mut self, lval: &LValue, state: LivenessState) {
		let mut keys = vec![];

		for key in self.liveness.keys().filter(|key| key.local == lval.local && key.projection.len() >= lval.projection.len()) {
			
			// Check if current key is a sublocation of our lvalue
	
			for proj in 0..lval.projection.len() {
				if key.projection[proj] != lval.projection[proj] {
					continue;
				}
			}

			keys.push(key.clone());
		}
	
		// Update all sublocations

		for key in keys {
			self.liveness.insert(key, state);
		}

		// If we moved a sublocation, set all its parent locations as PartialMoved
		if state == LivenessState::Moved && !lval.projection.is_empty() {
			let mut len = lval.projection.len();
			
			while len > 0 {
				let mut parent_lval = lval.clone();

				len -= 1;
				parent_lval.projection.resize(len, PlaceElem::Deref); // Dummy PlaceElem, never used
				
				self.liveness.insert(parent_lval, LivenessState::PartialMoved);
			}
		}
	}

	fn get_sublocation_liveness(&self, mut lval: LValue) -> LivenessState {
		loop {
			if let Some(state) = self.liveness.get(&lval) {
				return *state;
			}

			if lval.projection.len() == 0 {
				return LivenessState::Uninit;
			} else {
				lval.projection.pop();
			}
		}
	}


	fn eval_rvalue(&mut self, rval: &RValue) {
		match rval {
			RValue::Atom(ty, _, op) => {
				self.eval_operand(ty, op)
			}

			RValue::Cons(_, [(lty, lhs), (rty, rhs)], _) => {
				self.eval_operand(lty, lhs);
				self.eval_operand(rty, rhs);
			}

			RValue::Cast { from, val, .. } => {
				self.eval_operand(from, val)
			}
		}
	}

	fn eval_operand(&mut self, _ty: &CIRType, op: &Operand) {
		match op {
			Operand::LValue(lval) => {
				let sub_liveness = self.get_sublocation_liveness(lval.clone());
				
				// TODO: Check for `Copy` types? Might be handled earlier

				if sub_liveness == LivenessState::Live {
					self.set_all_sublocations(lval, LivenessState::Moved);
				} else {
					panic!("borrowck error! cannot move from local {} with state {sub_liveness:?}", lval.local); // TODO: Real error handling
				}
			}

			Operand::FnCall(_, args, _) => {
				for arg in args {
					self.eval_rvalue(arg);
				}
			}

			_ => {}
		}
	}
}

impl CIRPassMut for BorrowCheck {
	fn on_function(&self, func: &mut CIRFunction) {
		let mut liveness = LiveVarCheckState { liveness: HashMap::new() };

		for i in 0..func.arg_count {
			// Set first `arg_count` variables as pre-initialized
			liveness.liveness.insert(LValue { local: i, projection: vec![] }, LivenessState::Live);
		}
		
		let result = func.walk_cfg(liveness, |state, stmt| {
			match stmt {
				CIRStmt::Assignment(lval, rval) => {
					state.eval_rvalue(rval);
					state.liveness.insert(lval.clone(), LivenessState::Live);
				}
				
				CIRStmt::Expression(rval) => {
					state.eval_rvalue(rval);
				}
				
				CIRStmt::Return(rval_opt) => {
					if let Some(rval) = rval_opt {
						state.eval_rvalue(rval);
					}
				}

				_ => {}
			}
		});
	}
}
