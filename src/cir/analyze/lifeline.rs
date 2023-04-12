// lifeline - the comune liveness & borrow checker

use std::{collections::HashMap, fmt::Display};

use super::{
	Analysis, AnalysisDomain, AnalysisResultHandler, Forward, JoinSemiLattice, ResultVisitor,
};
use crate::{
	ast::{
		traits::{ImplSolver, LangTrait},
		types::{Basic, BindingProps},
	},
	cir::{CIRBlock, CIRCallId, CIRFunction, CIRStmt, LValue, Operand, PlaceElem, RValue, Type},
	errors::{ComuneErrCode, ComuneError},
	lexer::SrcSpan,
};

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

	pub fn get_liveness(&self, lval: &LValue) -> Option<LivenessState> {
		if self.liveness.get(lval).is_some() {
			// This state has a defined liveness value, so look through its children to check for partial moves

			// Get all keys that are sublocations of this lvalue
			for (_, val) in self.get_active_sublocations(lval) {
				if *val == LivenessState::Moved {
					return Some(LivenessState::PartialMoved);
				}
			}
		}

		let mut lval = lval.clone();

		// Look through superlocations for a defined LivenessState

		loop {
			if let Some(state) = self.liveness.get(&lval) {
				return Some(*state);
			}

			if lval.projection.is_empty() {
				return None;
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

			RValue::Cons(_, _, ..) => {
				//self.eval_operand(lty, lhs);
				//self.eval_operand(rty, rhs);
			}

			RValue::Cast { from, val, .. } => self.eval_operand(from, val),
		}
	}

	fn eval_operand(&mut self, _ty: &Type, op: &Operand) {
		match op {
			Operand::LValue(lval, _) => self.eval_lvalue(_ty, lval),

			_ => {}
		}
	}

	fn eval_lvalue(&mut self, _ty: &Type, lval: &LValue) {
		// TODO: Check for `Copy` types? Might be handled earlier

		self.set_liveness(lval, LivenessState::Moved);
	}
}

pub struct VarInitCheck;

impl JoinSemiLattice for LiveVarCheckState {
	fn join(&mut self, other: &Self) -> bool {
		let mut changed = false;

		let mut result = LiveVarCheckState {
			liveness: HashMap::new(),
		};

		for lval in self.liveness.keys().chain(other.liveness.keys()) {
			if result.liveness.contains_key(lval) {
				continue;
			}

			match (self.liveness.get(lval), other.liveness.get(lval)) {
				(Some(own), Some(other)) => {
					if own != other {
						changed = true;

						result
							.liveness
							.insert(lval.clone(), LivenessState::MaybeUninit);
					} else {
						result.liveness.insert(lval.clone(), *own);
					}
				}

				(Some(liveness), None) => {
					result.liveness.insert(lval.clone(), *liveness);
				}

				(None, Some(liveness)) => {
					changed = true;

					result.liveness.insert(lval.clone(), *liveness);
				}

				(None, None) => unreachable!(),
			}
		}

		if changed {
			*self = result;
		}

		changed
	}
}

impl AnalysisDomain for VarInitCheck {
	type Domain = LiveVarCheckState;
	type Direction = Forward;

	fn bottom_value(&self, _func: &CIRFunction) -> Self::Domain {
		LiveVarCheckState {
			liveness: HashMap::new(),
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

			CIRStmt::Invoke {
				result: Some(lval), ..
			}
			| CIRStmt::Call {
				result: Some(lval), ..
			} => {
				state.set_liveness(lval, LivenessState::Live);
			}

			CIRStmt::StorageLive(local) => {
				state.set_liveness(
					&LValue {
						local: *local,
						projection: vec![],
					},
					LivenessState::Uninit,
				);
			}

			CIRStmt::StorageDead { var, .. } => {
				let lval = LValue {
					local: *var,
					projection: vec![],
				};
				// Clear all sublocation states
				state.set_liveness(&lval, LivenessState::Dropped);

				state.liveness.remove(&lval);
			}

			_ => {}
		}
	}
}

impl AnalysisResultHandler for VarInitCheck {
	fn process_result(
		mut result: ResultVisitor<Self>,
		func: &CIRFunction,
		impl_solver: &ImplSolver,
	) -> Result<Option<CIRFunction>, Vec<ComuneError>> {
		validate_uses(&mut result, func, impl_solver)?;
		let new_func = elaborate_drops(&mut result, func, impl_solver)?;

		Ok(Some(new_func))
	}
}

fn validate_uses(
	result: &mut ResultVisitor<VarInitCheck>,
	func: &CIRFunction,
	_impl_solver: &ImplSolver,
) -> Result<(), Vec<ComuneError>> {
	let mut errors = vec![];

	for (i, block) in func.blocks.iter().enumerate() {
		for (j, stmt) in block.items.iter().enumerate() {
			let state = result.get_state_before(i, j);

			// Check for uses of uninit/moved lvalues
			match stmt {
				CIRStmt::Assignment(_, RValue::Atom(_, _, Operand::LValue(lval, _), span))
				| CIRStmt::Switch(Operand::LValue(lval, span), ..)
				| CIRStmt::Assignment(
					_,
					RValue::Cons(_, [(_, Operand::LValue(lval, span)), _], ..),
				)
				| CIRStmt::Assignment(
					_,
					RValue::Cons(_, [_, (_, Operand::LValue(lval, span))], ..),
				)
				| CIRStmt::Invoke {
					id: CIRCallId::Indirect {
						local: lval, span, ..
					},
					..
				}
				| CIRStmt::Call {
					id: CIRCallId::Indirect {
						local: lval, span, ..
					},
					..
				} => {
					let liveness = state.get_liveness(lval);

					match liveness {
						Some(LivenessState::Live) => {}

						_ => errors.push(ComuneError::new(
							ComuneErrCode::InvalidUse {
								variable: func.get_variable_name(lval.local),
								state: liveness.unwrap_or(LivenessState::Uninit),
							},
							*span,
						)),
					}
				}

				CIRStmt::Invoke { args, .. } | CIRStmt::Call { args, .. } => {
					for (lval, span) in args {
						let liveness = state.get_liveness(lval);

						match liveness {
							Some(LivenessState::Live) => {}

							_ => errors.push(ComuneError::new(
								ComuneErrCode::InvalidUse {
									variable: func.get_variable_name(lval.local),
									state: liveness.unwrap_or(LivenessState::Uninit),
								},
								*span,
							)),
						}
					}
				}

				_ => {}
			}

			// Check for mutation of immutable lvalues
			if let CIRStmt::Assignment((lval, tk), _) = stmt {
				if !matches!(
					state.get_liveness(lval),
					None | Some(LivenessState::Uninit) | Some(LivenessState::Moved)
				) && !func.variables[lval.local].1.is_mut
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
	}

	if errors.is_empty() {
		Ok(())
	} else {
		Err(errors)
	}
}

enum DropStyle {
	Live,
	Conditional,
	Open,
	Dead,
}

fn elaborate_drops(
	result: &mut ResultVisitor<VarInitCheck>,
	func: &CIRFunction,
	impl_solver: &ImplSolver,
) -> Result<CIRFunction, Vec<ComuneError>> {
	let errors = vec![];
	let drop_trait = impl_solver.get_lang_trait(LangTrait::Drop);

	let mut func_out = func.clone();
	let mut block_obligations = vec![];
	let mut drop_flags = HashMap::new();

	for (i, block) in func.blocks.iter().enumerate() {
		let mut obligations = vec![];

		if let CIRStmt::StorageDead { var, .. } = block.items.last().unwrap() {
			let lvalue = LValue {
				local: *var,
				projection: vec![],
			};
			let state = result.get_state_before(i, block.items.len() - 1);

			get_drop_obligations(&state, &lvalue, &mut obligations);
		}

		block_obligations.push(obligations);
	}

	for (i, obligations) in block_obligations.into_iter().enumerate() {
		if obligations.is_empty() {
			continue;
		}

		for (lvalue, style) in obligations {
			let var_ty = func.get_lvalue_type(&lvalue);
			let needs_drop = impl_solver.is_trait_implemented(&var_ty, &drop_trait, &vec![]);

			let CIRStmt::StorageDead { next, .. } = func_out.blocks[i].items.pop().unwrap() else {
				panic!()
			};

			if !needs_drop {
				func_out.blocks[i].items.push(CIRStmt::Jump(next));
				continue;
			}

			match style {
				DropStyle::Live => {
					func_out.blocks[i].items.push(CIRStmt::Jump(next));
				}

				DropStyle::Conditional => {
					let flag = if let Some(flag) = drop_flags.get(&lvalue) {
						*flag
					} else {
						func_out.variables.push((
							Type::Basic(Basic::Bool),
							BindingProps::default(),
							None,
						));

						drop_flags.insert(lvalue, func_out.variables.len() - 1);

						func_out.variables.len() - 1
					};

					let drop_block = CIRBlock {
						items: vec![CIRStmt::Jump(next)],
						preds: vec![i],
						succs: vec![next],
					};

					let flag_lval = LValue {
						local: flag,
						projection: vec![],
					};
					let drop_idx = func_out.blocks.len();

					func_out.blocks.push(drop_block);

					func_out.blocks[i].items.push(CIRStmt::Switch(
						Operand::LValue(flag_lval, SrcSpan::new()),
						vec![(
							Type::bool_type(),
							Operand::BoolLit(true, SrcSpan::new()),
							drop_idx,
						)],
						next,
					));

					func_out.blocks[i].succs.push(drop_idx);
				}

				DropStyle::Dead | DropStyle::Open => {
					func_out.blocks[i].items.push(CIRStmt::Jump(next));
				}
			}
		}
	}

	if !errors.is_empty() {
		Err(errors)
	} else {
		Ok(func_out)
	}
}

fn get_drop_obligations(
	state: &LiveVarCheckState,
	lvalue: &LValue,
	obligations: &mut Vec<(LValue, DropStyle)>,
) {
	match state.get_liveness(&lvalue) {
		None | Some(LivenessState::Moved) | Some(LivenessState::Uninit) => {
			// Don't emit drop
			obligations.push((lvalue.clone(), DropStyle::Dead));
			return;
		}

		Some(LivenessState::Live) | Some(LivenessState::PartialMoved) => {
			// Emit drop + sublocation drops
			obligations.push((lvalue.clone(), DropStyle::Live));
		}

		Some(LivenessState::MaybeUninit) => {
			// Emit conditional drop
			obligations.push((lvalue.clone(), DropStyle::Conditional));
		}

		_ => return,
	}

	for (subloc, _) in state.get_active_sublocations(&lvalue) {
		get_drop_obligations(state, subloc, obligations);
	}
}
