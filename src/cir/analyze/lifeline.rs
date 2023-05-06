// lifeline - the comune liveness & borrow checker

use std::{collections::HashMap, fmt::Display, sync::Arc};

use super::{
	Analysis, AnalysisDomain, AnalysisResultHandler, Forward, JoinSemiLattice, ResultVisitor,
};
use crate::{
	ast::{
		traits::ImplSolver,
		types::{Basic, BindingProps, TupleKind},
	},
	cir::{CIRBlock, CIRCallId, CIRFunction, CIRStmt, LValue, Operand, PlaceElem, RValue, Type, VarIndex, BlockIndex},
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

pub struct DefInitFlow;
pub struct VarInitCheck;
pub struct ElaborateDrops;

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
			RValue::Atom(.., op, _) => self.eval_operand(op),

			RValue::Cons(..) => {
				//self.eval_operand(lhs);
				//self.eval_operand(rhs);
			}

			RValue::Cast { val, .. } => self.eval_operand(val),
		}
	}

	fn eval_operand(&mut self, op: &Operand) {
		match op {
			Operand::Move(lval) => self.eval_lvalue(lval),

			_ => {}
		}
	}

	fn eval_lvalue(&mut self, lval: &LValue) {
		// TODO: Check for `Copy` types? Might be handled earlier
		if !lval.binding.is_ref {
			self.set_liveness(lval, LivenessState::Moved);
		}
	}
}

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

impl AnalysisDomain for DefInitFlow {
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
					binding: func.variables[var].1
				},
				LivenessState::Live,
			);
		}
	}
}

impl Analysis for DefInitFlow {
	fn apply_effect(
		&self,
		stmt: &CIRStmt,
		_position: (crate::cir::BlockIndex, crate::cir::StmtIndex),
		state: &mut Self::Domain,
	) {
		match stmt {
			CIRStmt::Assignment(lval, rval) => {
				state.eval_rvalue(rval);
				state.set_liveness(lval, LivenessState::Live);
			}

			CIRStmt::Invoke { result, args, .. } | CIRStmt::Call { result, args, .. } => {
				for (arg, _) in args {
					state.eval_lvalue(arg);
				}

				if let Some(result) = result {
					state.set_liveness(result, LivenessState::Live);
				}
			}

			CIRStmt::StorageLive(local) => {
				state.set_liveness(
					&LValue::new(*local),
					LivenessState::Uninit,
				);
			}

			CIRStmt::DropShim { var, .. } => {
				// `drop` is a no-op for uninitialized variables, so only update the
				// liveness state if the variable is (potentially) initialized
				if !matches!(state.get_liveness(var), None | Some(LivenessState::Uninit)) {
					state.set_liveness(var, LivenessState::Dropped);
				}
			}

			_ => {}
		}
	}
}

impl AnalysisResultHandler<DefInitFlow> for VarInitCheck {
	fn process_result(
		&self,
		result: ResultVisitor<DefInitFlow>,
		func: &CIRFunction,
		_: &ImplSolver,
	) -> Result<Option<CIRFunction>, Vec<ComuneError>> {
		let mut errors = vec![];

		for (i, block) in func.blocks.iter().enumerate() {
			for (j, stmt) in block.items.iter().enumerate() {
				let state = result.get_state_before(i, j);

				// Check for uses of uninit/moved lvalues
				match stmt {
					CIRStmt::Assignment(_, RValue::Atom(_, _, Operand::Move(lval), _))
					| CIRStmt::Switch(Operand::Move(lval), ..)
					| CIRStmt::Assignment(
						_,
						RValue::Cons(_, [(_, Operand::Move(lval)), _], ..),
					)
					| CIRStmt::Assignment(
						_,
						RValue::Cons(_, [_, (_, Operand::Move(lval))], ..),
					)
					| CIRStmt::Invoke {
						id: CIRCallId::Indirect {
							local: lval, ..
						},
						..
					}
					| CIRStmt::Call {
						id: CIRCallId::Indirect {
							local: lval, ..
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
								lval.binding.span,
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
				if let CIRStmt::Assignment(lval, _) = stmt {
					let is_var_init = !matches!(
						state.get_liveness(lval),
						None | Some(LivenessState::Uninit)
					);

					if is_var_init && !lval.binding.is_mut {
						errors.push(ComuneError::new(
							ComuneErrCode::ImmutVarMutation {
								variable: func.get_variable_name(lval.local),
							},
							lval.binding.span,
						))
					}
				}
			}
		}

		if errors.is_empty() {
			Ok(None)
		} else {
			Err(errors)
		}
	}
}

enum DropStyle {
	Live,
	Conditional,
	Dead,
}


impl AnalysisResultHandler<DefInitFlow> for ElaborateDrops {
	fn process_result(
			&self,
			result: ResultVisitor<DefInitFlow>,
			func: &CIRFunction,
			_: &ImplSolver,
	) -> Result<Option<CIRFunction>, Vec<ComuneError>> {
		let errors = vec![];

		let mut func_out = func.clone();
		let mut drop_flags = HashMap::new();

		for (i, block) in func.blocks.iter().enumerate() {
			if let CIRStmt::DropShim { var, next } = block.items.last().unwrap() {
				func_out.blocks[i].items.pop();

				let state = result.get_state_before(i, block.items.len() - 1);
								
				let mut elaborator = DropElaborator {
					current_block: i,
					current_fn: &mut func_out,
					drop_flags: &mut drop_flags,
					state: &state,
				};

				elaborator.elaborate_drop(&var, &func.get_lvalue_type(var), *next);
				elaborator.write(CIRStmt::Jump(*next));
			}
		}

		if !errors.is_empty() {
			Err(errors)
		} else {
			Ok(Some(func_out))
		}
	}
}

struct DropElaborator<'func> {
	current_block: BlockIndex,
	current_fn: &'func mut CIRFunction,
	drop_flags: &'func mut HashMap<LValue, VarIndex>,
	state: &'func LiveVarCheckState,
}

impl<'func> DropElaborator<'func> {
	fn write(&mut self, stmt: CIRStmt) {
		self.current_fn.blocks[self.current_block]
			.items
			.push(stmt)
	}

	fn append_block(&mut self) -> BlockIndex {
		self.current_fn.blocks.push(CIRBlock {
			items: vec![],
			preds: vec![],
			succs: vec![],
		});
		self.current_block = self.current_fn.blocks.len() - 1;
		self.current_block
	}

	fn elaborate_drop(&mut self, lval: &LValue, ty: &Type, next: BlockIndex) {
		match self.state.get_liveness(lval) {
			Some(LivenessState::Live) => {
				self.build_destructor(lval, ty, next);
			}
	
			Some(LivenessState::MaybeUninit) => {
				let flag = if let Some(flag) = self.drop_flags.get(&lval) {
					*flag
				} else {
					self.current_fn.variables.push((
						Type::Basic(Basic::Bool),
						BindingProps::default(),
						None,
					));
	
					self.drop_flags.insert(lval.clone(), self.current_fn.variables.len() - 1);
	
					self.current_fn.variables.len() - 1
				};
				
				let start_idx = self.current_block;
				let drop_idx = self.current_fn.blocks.len();

				let drop_block = CIRBlock {
					items: vec![],
					preds: vec![self.current_block],
					succs: vec![next],
				};
	
				let flag_lval = LValue::new(flag);
	
				self.current_fn.blocks.push(drop_block);
				self.current_block = drop_idx;

				self.build_destructor(lval, ty, next);

				self.current_block = start_idx;
				self.write(CIRStmt::Switch(
					Operand::Move(flag_lval),
					vec![(
						Type::bool_type(),
						Operand::BoolLit(true, SrcSpan::new()),
						drop_idx,
					)],
					next,
				));
				
				self.current_fn.blocks[self.current_block].succs.push(drop_idx);
				self.current_block = self.current_fn.blocks.len() - 1;
			}
	
			_ => {}
		}
	}

	fn build_destructor(&mut self, lval: &LValue, ty: &Type, next: BlockIndex) {
		match ty {
			Type::TypeRef { def, args } => {
				let def = def.upgrade().unwrap();
				let def = def.read().unwrap();
				
				if let Some(drop) = &def.drop {
					if self.state.get_liveness(lval) == Some(LivenessState::Live) {
						let drop = Arc::new(drop.read().unwrap().clone());
	
						self.write(CIRStmt::Call { 
							id: CIRCallId::Direct(drop, SrcSpan::new()), 
							args: vec![(lval.clone(), SrcSpan::new())], 
							generic_args: args.clone(),
							result: None,
						});
					}
				}
	
				for (_, member, _) in def.members.iter() {
					self.elaborate_drop(lval, member, next);
				}
	
			}
	
			Type::Tuple(TupleKind::Sum, _) => {}
	
			Type::Tuple(TupleKind::Product, types) => {
				for (i, ty) in types.iter().enumerate() {
					let mut lval = lval.clone();
					lval.projection.push(PlaceElem::Field(i));
					
					self.elaborate_drop(&lval, ty, next);
				}
			}
	
			Type::Tuple(TupleKind::Newtype, types) => {
				let [ty] = types.as_slice() else {
					panic!()
				};
	
				self.elaborate_drop(lval, ty, next);
			}
	
			_ => {}
		}
	}
}