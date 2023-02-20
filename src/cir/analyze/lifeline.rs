// lifeline - the comune liveness & borrow checker

use std::{collections::HashMap, fmt::Display};

use super::{
	Analysis, AnalysisDomain, AnalysisResultHandler, CIRPassMut, Forward, JoinSemiLattice,
	ResultVisitor,
};
use crate::{
	cir::{CIRFunction, CIRStmt, CIRType, LValue, Operand, PlaceElem, RValue},
	errors::{ComuneErrCode, ComuneError},
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

#[derive(Debug, Clone)]
pub struct LiveVarCheckState {
	// TODO: Create Path type, for canonicalized LValues
	liveness: HashMap<LValue, LivenessState>,
}

impl Display for LiveVarCheckState {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for (lval, liveness) in &self.liveness {
			writeln!(f, "{lval}: {liveness:?}")?;
		}
		Ok(())
	}
}

impl LiveVarCheckState {
	pub fn set_liveness(&mut self, lval: &LValue, state: LivenessState) {
		// Clear liveness state for all sublocations

		let keys: Vec<_> = self
			.get_active_sublocations(lval)
			.map(|(a, b)| (a.clone(), b.clone()))
			.collect();

		for (key, _) in keys {
			if !key.projection[lval.projection.len()..].contains(&PlaceElem::Deref) {
				self.liveness.remove(&key);
			}
		}

		self.liveness.insert(lval.clone(), state);
	}

	pub fn get_liveness(&self, lval: &LValue) -> LivenessState {
		if self.liveness.get(lval).is_some() {
			// This state has a defined liveness value, so look through its children to check for partial moves

			// Get all keys that are sublocations of this lvalue
			for (_, val) in self.get_active_sublocations(lval) {
				if *val == LivenessState::Moved {
					return LivenessState::PartialMoved;
				}
			}
		}

		let mut lval = lval.clone();

		// Look through superlocations for a defined LivenessState

		loop {
			if let Some(state) = self.liveness.get(&lval) {
				return *state;
			}

			if lval.projection.is_empty() {
				return LivenessState::Uninit;
			} else {
				lval.projection.pop();
			}
		}
	}

	fn get_active_sublocations<'a>(
		&'a self,
		lval: &'a LValue,
	) -> impl Iterator<Item = (&'a LValue, &'a LivenessState)> {
		self.liveness.iter().filter_map(|(key, val)| {
			if key.local != lval.local {
				return None;
			}

			if key.projection.len() <= lval.projection.len() {
				return None;
			}

			if key.projection[0..lval.projection.len()] != *lval.projection.as_slice() {
				return None;
			}

			if key.projection[lval.projection.len()..].contains(&PlaceElem::Deref) {
				return None;
			}

			Some((key, val))
		})
	}

	fn eval_rvalue(&mut self, rval: &RValue) {
		match rval {
			RValue::Atom(ty, _, op, _) => self.eval_operand(ty, op),

			RValue::Cons(_, [(lty, lhs), (rty, rhs)], ..) => {
				self.eval_operand(lty, lhs);
				self.eval_operand(rty, rhs);
			}

			RValue::Cast { from, val, .. } => self.eval_operand(from, val),
		}
	}

	fn eval_operand(
		&mut self,
		_ty: &CIRType,
		op: &Operand,
	) {
		match op {
			Operand::LValue(lval, _) => self.eval_lvalue(_ty, lval),

			_ => {}
		}
	}

	fn eval_lvalue(
		&mut self,
		_ty: &CIRType,
		lval: &LValue,
	) {
		// TODO: Check for `Copy` types? Might be handled earlier

		self.set_liveness(lval, LivenessState::Moved);
	}
}

impl CIRPassMut for BorrowCheck {
	fn on_function(&self, func: &mut CIRFunction) -> Vec<ComuneError> {
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

				self.set_liveness(lval, LivenessState::MaybeUninit)
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
				.map(|idx| {
					(
						LValue {
							local: idx,
							projection: vec![],
						},
						LivenessState::Uninit,
					)
				})
				.collect(),
		}
	}

	fn initialize_start_block(&self, func: &CIRFunction, state: &mut Self::Domain) {
		// There is *definitely* a way to do this with bit math but fuck if i know lol
		for var in 0..func.arg_count {
			state.liveness.insert(
				LValue {
					local: var,
					projection: vec![],
				},
				LivenessState::Live,
			);
		}
	}
}

impl Analysis for VarInitCheck {
	fn apply_effect(
		&self,
		stmt: &CIRStmt,
		_position: (crate::cir::BlockIndex, crate::cir::StmtIndex),
		state: &mut Self::Domain,
	) {
		match stmt {
			CIRStmt::Assignment((lval, _), rval) => {
				state.eval_rvalue(rval);
				state.set_liveness(lval, LivenessState::Live);
			}

			CIRStmt::FnCall {
				result: Some(lval), ..
			} => {
				state.set_liveness(lval, LivenessState::Live);
			}

			_ => {}
		}
	}
}

impl AnalysisResultHandler for VarInitCheck {
	fn process_result(result: ResultVisitor<Self>, func: &CIRFunction) -> Vec<ComuneError> {
		let mut errors = vec![];

		for (i, block) in func.blocks.iter().enumerate() {
			//let state = result.get_state_before(i, 0);
			//println!("state at start of block {i}:\n {state}\n\n");

			for (j, stmt) in block.items.iter().enumerate() {
				let state = result.get_state_before(i, j);

				// Check for uses of uninit/moved lvalues
				match stmt {
					CIRStmt::Assignment(_, RValue::Atom(_, _, Operand::LValue(lval, _), span))
					| CIRStmt::Assignment(_, RValue::Cons(_, [(_, Operand::LValue(lval, span)), _], ..))
					| CIRStmt::Assignment(_, RValue::Cons(_, [_, (_, Operand::LValue(lval, span))], ..))
					| CIRStmt::Switch(Operand::LValue(lval, span), ..)
					| CIRStmt::Return(Some(Operand::LValue(lval, span))) => {
						let liveness = state.get_liveness(lval);

						match liveness {
							LivenessState::Live => {}

							_ => errors.push(ComuneError::new(
								ComuneErrCode::InvalidUse {
									variable: func.get_variable_name(lval.local),
									state: liveness,
								},
								*span,
							)),
						}
					}

					_ => {}
				}

				// Check for mutation of immutable lvalues
				if let CIRStmt::Assignment((lval, tk), _) = stmt {
					if state.get_liveness(lval) != LivenessState::Uninit
						&& !func.variables[lval.local].1.is_mut
					{
						errors.push(ComuneError::new(
							ComuneErrCode::ImmutVarMutation {
								variable: func.get_variable_name(lval.local),
							},
							*tk,
						))
					}
				}
			}

			//let state = result.get_state_before(i, block.items.len() - 1);
			//println!("state at end of block {i}:\n {state}\n\n");
		}

		errors
	}
}
