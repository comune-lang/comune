// lifeline - the comune liveness & borrow checker

use std::collections::HashMap;

use super::{CIRPassMut, AnalysisDomain, JoinSemiLattice, Analysis, Forward};
use crate::{
	ast::TokenData,
	cir::{CIRFunction, CIRStmt, CIRType, LValue, Operand, PlaceElem, RValue},
	errors::CMNError,
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
	MaybeUninit,
}

#[derive(Clone)]
pub struct LiveVarCheckState {
	// TODO: Create Path type, for canonicalized LValues
	liveness: HashMap<LValue, LivenessState>,
}

impl LiveVarCheckState {
	pub fn set_liveness(&mut self, lval: &LValue, state: LivenessState) {
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
				//println!("removing state for {key}");
				self.liveness.remove(&key);
			}
		}

		//println!("setting {state:?} for {lval}");
		self.liveness.insert(lval.clone(), state);
	}

	pub fn get_liveness(&self, lval: &LValue) -> LivenessState {
		if self.liveness.get(lval).is_some() {
			// This state has a defined liveness value, so look through its children to check for partial moves

			// Get all keys that are sublocations of this lvalue
			for (key, val) in self.liveness.iter().filter(|(key, _)| {
				key.local == lval.local
					&& key.projection.len() > lval.projection.len()
					&& key.projection[0..lval.projection.len()] == *lval.projection.as_slice()
			}) {
				if *val == LivenessState::Moved {
					//println!("returning PartialMoved for {lval} as {key} is Moved");
					return LivenessState::PartialMoved;
				}
			}
		}

		let mut lval = lval.clone();

		// Look through superlocations for a defined LivenessState
		// (If the provided lval has a defined state, it'll just return that)

		loop {
			if let Some(state) = self.liveness.get(&lval) {
				//println!("returning {state:?} for {lval}");
				return *state;
			}

			if lval.projection.is_empty() {
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
			Operand::LValue(lval) => self.eval_lvalue(_ty, lval, token_data)?,

			_ => {}
		}
		Ok(())
	}

	fn eval_lvalue(
		&mut self,
		_ty: &CIRType,
		lval: &LValue,
		token_data: TokenData,
	) -> Result<(), (LValue, LivenessState, TokenData)> {
		let sub_liveness = self.get_liveness(lval);

		// TODO: Check for `Copy` types? Might be handled earlier

		if sub_liveness == LivenessState::Live {
			self.set_liveness(lval, LivenessState::Moved);
			Ok(())
		} else {
			Err((lval.clone(), sub_liveness, token_data))
		}
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
		vec![]
	}
}

pub struct VarInitCheck;

impl JoinSemiLattice for LiveVarCheckState {
	fn join(&mut self, other: &Self) -> bool {
		let mut changed = false;

		for (lval, liveness) in &other.liveness {
			let own_liveness = self.get_liveness(lval);
			
			if liveness != &own_liveness {
				changed = true;

				match (*liveness, own_liveness) {
					(LivenessState::Live, _) | (_, LivenessState::Live) => {
						self.set_liveness(lval, LivenessState::MaybeUninit)
					}

					_ => {}
				}
			}
		}

		changed
	}
}

impl AnalysisDomain for VarInitCheck {
	type Domain = LiveVarCheckState;
	type Direction = Forward;

	fn bottom_value(&self, func: &CIRFunction) -> Self::Domain {
		LiveVarCheckState { 
			liveness: (0..func.variables.len())
				.into_iter()
				.map(|idx| (
					LValue { local: idx, projection: vec![] }, 
					LivenessState::Uninit
				))
				.collect()
			}
	}

	fn initialize_start_block(&self, func: &CIRFunction, state: &mut Self::Domain) {
		// There is *definitely* a way to do this with bit math but fuck if i know lol
		for var in 0..func.arg_count {
			state.liveness.insert(LValue { local: var, projection: vec![] }, LivenessState::Live);
		}
	}
}

impl Analysis for VarInitCheck {
	fn apply_effect(
		&self,
		stmt: &CIRStmt,
		position: (crate::cir::BlockIndex, crate::cir::StmtIndex),
		state: &mut Self::Domain
	) {
		match stmt {
			CIRStmt::Assignment((lval, _), (rval, token_data)) => {
				state.eval_rvalue(rval, *token_data);
				state.set_liveness(lval, LivenessState::Live);
			}

			CIRStmt::FnCall { result: Some(lval), .. } => {
				state.set_liveness(lval, LivenessState::Live);
			}

			_ => {}
		}
	}
}