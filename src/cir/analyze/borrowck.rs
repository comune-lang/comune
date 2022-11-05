// the comune borrow checker

use std::collections::HashMap;

use super::CIRPassMut;
use crate::{
	cir::{CIRFunction, CIRStmt, CIRType, LValue, Operand, RValue, PlaceElem},
	errors::{CMNError, CMNErrorCode},
	parser::AnalyzeResult,
	semantic::{ast::TokenData, namespace::Identifier},
};

pub struct BorrowCheck;

struct Borrow {
	place: LValue,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum LivenessState {
	Uninit,
	Live,
	Moved,
	PartialMoved,
	Dropped,
}

#[derive(Clone)]
struct LiveVarCheckState {
	// TODO: Create Path type, for canonicalized LValues
	liveness: HashMap<LValue, LivenessState>,
}

impl LiveVarCheckState {
	fn set_liveness(&mut self, lval: &LValue, state: LivenessState) {
		// Clear liveness state for all sublocations

		let keys: Vec<_> = self
			.liveness
			.keys()
			.filter(|key| {
				key.local == lval.local
					&& key.projection.len() >= lval.projection.len()
					&& key.projection[0..lval.projection.len()] == *lval.projection.as_slice()
			})
			.cloned()
			.collect();

		for key in keys {
			if !key.projection[lval.projection.len()..].contains(&PlaceElem::Deref) {
				println!("removing state for {key}");
				self.liveness.remove(&key);	
			}
		}

		println!("setting {state:?} for {lval}");
		self.liveness.insert(lval.clone(), state);
	}

	fn get_liveness(&self, lval: &LValue) -> LivenessState {
		if self.liveness.get(&lval).is_some() {
			// This state has a defined liveness value, so look through its children to check for partial moves

			// Get all keys that are sublocations of this lvalue
			for (key, val) in self.liveness.iter().filter(|(key, _)| {
				key.local == lval.local
					&& key.projection.len() > lval.projection.len()
					&& key.projection[0..lval.projection.len()] == *lval.projection.as_slice()
			}) {
				if *val == LivenessState::Moved {
					println!("returning PartialMoved for {lval} as {key} is Moved");
					return LivenessState::PartialMoved;
				}
			}
		}

		let mut lval = lval.clone();

		// Look through superlocations for a defined LivenessState
		// (If the provided lval has a defined state, it'll just return that)

		loop {
			if let Some(state) = self.liveness.get(&lval) {
				println!("returning {state:?} for {lval}");
				return *state;
			}

			if lval.projection.len() == 0 {
				return LivenessState::Uninit;
			} else {
				lval.projection.pop();
			}
		}
	}

	fn eval_rvalue(
		&mut self,
		rval: &RValue,
		token_data: TokenData,
	) -> Result<(), (LValue, LivenessState, TokenData)> {
		match rval {
			RValue::Atom(ty, _, op) => self.eval_operand(ty, op, token_data),

			RValue::Cons(_, [(lty, lhs), (rty, rhs)], _) => {
				self.eval_operand(lty, lhs, token_data)?;
				self.eval_operand(rty, rhs, token_data)?;
				Ok(())
			}

			RValue::Cast { from, val, .. } => self.eval_operand(from, val, token_data),
		}
	}

	fn eval_operand(
		&mut self,
		_ty: &CIRType,
		op: &Operand,
		token_data: TokenData,
	) -> Result<(), (LValue, LivenessState, TokenData)> {
		match op {
			Operand::LValue(lval) => {
				let sub_liveness = self.get_liveness(lval);

				// TODO: Check for `Copy` types? Might be handled earlier

				if sub_liveness == LivenessState::Live {
					self.set_liveness(lval, LivenessState::Moved);
				} else {
					return Err((lval.clone(), sub_liveness, token_data));
				}
			}

			Operand::FnCall(_, args, _) => {
				for arg in args {
					self.eval_rvalue(arg, token_data)?;
				}
			}

			_ => {}
		}
		Ok(())
	}
}

fn convert_invalid_use_error(
	func: &CIRFunction,
	mut stmt: impl FnMut() -> Result<(), (LValue, LivenessState, TokenData)>,
) -> AnalyzeResult<()> {
	match stmt() {
		Ok(()) => Ok(()),
		Err(e) => Err((
			CMNError::new(CMNErrorCode::InvalidUse {
				variable: Identifier::from_name(
					func.variables[e.0.local]
						.1
						.as_ref()
						.unwrap_or(&"(???)".into())
						.clone(),
					false,
				),
				state: e.1,
			}),
			e.2,
		)),
	}
}

impl CIRPassMut for BorrowCheck {
	fn on_function(&self, func: &mut CIRFunction) -> Vec<(CMNError, TokenData)> {
		let mut liveness = LiveVarCheckState {
			liveness: HashMap::new(),
		};

		for i in 0..func.arg_count {
			// Set first `arg_count` variables as pre-initialized
			liveness.liveness.insert(
				LValue {
					local: i,
					projection: vec![],
				},
				LivenessState::Live,
			);
		}

		let result = func.walk_cfg(liveness, |state, stmt| {
			convert_invalid_use_error(func, || {
				match stmt {
					CIRStmt::Assignment((lval, _), (rval, token_data)) => {
						state.eval_rvalue(rval, *token_data)?;
						state.liveness.insert(lval.clone(), LivenessState::Live);
					}

					CIRStmt::Expression(rval, token_data) => {
						state.eval_rvalue(rval, *token_data)?;
					}

					CIRStmt::Return(rval_opt) => {
						if let Some((rval, token_data)) = rval_opt {
							state.eval_rvalue(rval, *token_data)?;
						}
					}

					_ => {}
				}

				Ok(())
			})
		});

		result
	}
}
