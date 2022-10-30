// the comune borrow checker

use std::collections::HashMap;

use super::CIRPassMut;
use crate::cir::{CIRFunction, CIRStmt, LValue, RValue, Operand, CIRType};

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
	fn set_liveness(&mut self, lval: &LValue, state: LivenessState) {
		let mut keys = vec![];

		// Clear liveness state for all sublocations
		
		for key in self.liveness.keys().filter(|key| key.local == lval.local && key.projection.len() >= lval.projection.len()) {

			for proj in 0..lval.projection.len() {
				if key.projection[proj] != lval.projection[proj] {
					continue;
				}
			}

			keys.push(key.clone());
		}
	
		for key in keys {
			self.liveness.insert(key, state);
		}

		self.liveness.insert(lval.clone(), state);
	}

	fn get_liveness(&self, lval: &LValue) -> LivenessState {
		if self.liveness.get(&lval).is_some() {
			// This state has a defined liveness value, so look through its children to check for partial moves
			
			// Get all keys that are sublocations of this lvalue
			for (_, val) in self.liveness.iter().filter(|(key, _)| key.local == lval.local && key.projection[0..lval.projection.len()] == *lval.projection.as_slice()) {
				if *val == LivenessState::Moved {
					return LivenessState::PartialMoved;
				}
			}
		}

		let mut lval = lval.clone();

		// Look through superlocations for a defined LivenessState
		// (If the provided lval has a defined state, it'll just return that)
		
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
				let sub_liveness = self.get_liveness(lval);
				
				// TODO: Check for `Copy` types? Might be handled earlier

				if sub_liveness == LivenessState::Live {
					self.set_liveness(lval, LivenessState::Moved);
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
				CIRStmt::Assignment((lval, _), (rval, _)) => {
					state.eval_rvalue(rval);
					state.liveness.insert(lval.clone(), LivenessState::Live);
				}
				
				CIRStmt::Expression(rval, _) => {
					state.eval_rvalue(rval);
				}
				
				CIRStmt::Return(rval_opt) => {
					if let Some((rval, _)) = rval_opt {
						state.eval_rvalue(rval);
					}
				}

				_ => {}
			}
		});
	}
}
