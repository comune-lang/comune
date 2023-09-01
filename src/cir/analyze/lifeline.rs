// lifeline - the comune liveness & borrow checker

use std::{collections::HashMap, fmt::Display, sync::{RwLock, Arc}};

use super::{
	Analysis, AnalysisDomain, AnalysisResultHandler, Forward, JoinSemiLattice, ResultVisitor,
};
use crate::{
	ast::{
		traits::{ImplSolver, LangTrait},
		types::{BindingProps, Generics, TupleKind, GenericArgs, TypeDef},
	},
	cir::{
		BlockIndex, CIRBlock, CIRCallId, CIRFunction, CIRStmt, LValue, Operand, PlaceElem, RValue,
		Type, VarIndex,
	},
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

impl CIRStmt {
	fn inspect_lvalue_uses(&self, mut f: impl FnMut(&LValue, &BindingProps)) {
		match self {
			CIRStmt::Assignment(_, rval) => self.inspect_rvalue(rval, f),

			CIRStmt::Call { args, .. } | CIRStmt::Invoke { args, .. } => {
				for (lval, _, props) in args {
					f(lval, props)
				}
			}

			// FIXME: Store BindingProps in RefInit
			CIRStmt::RefInit(_, lval) => f(lval, &BindingProps::reference()),

			CIRStmt::Switch(op, branches, _) => {
				if let Operand::LValueUse(lval, props) = op {
					f(lval, props)
				}

				for (_, branch, _) in branches {
					if let Operand::LValueUse(lval, props) = branch {
						f(lval, props)
					}
				}
			}

			// FIXME: Incorrect for reference bindings
			CIRStmt::DropShim { var, .. } => f(var, &BindingProps::value()),

			_ => {}
		}
	}

	fn inspect_rvalue(&self, rval: &RValue, mut f: impl FnMut(&LValue, &BindingProps)) {
		match rval {
			RValue::Atom(.., Operand::LValueUse(lval, props), _) => f(lval, props),

			RValue::Cons(_, [(_, lhs), (_, rhs)], ..) => {
				if let Operand::LValueUse(lval, props) = lhs {
					f(lval, props)
				}
				if let Operand::LValueUse(lval, props) = rhs {
					f(lval, props)
				}
			}

			RValue::Cast {
				val: Operand::LValueUse(lval, props),
				..
			} => f(lval, props),

			_ => {}
		}
	}
}

#[derive(Debug, Clone)]
pub struct LiveVarCheckState {
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

	fn eval_rvalue(&mut self, rval: &RValue, solver: &ImplSolver, generics: &Generics) {
		match rval {
			RValue::Atom(ty, _, op, _) => self.eval_operand(op, ty, solver, generics),

			RValue::Cons(_, [(lty, lhs), (rty, rhs)], ..) => {
				self.eval_operand(lhs, lty, solver, generics);
				self.eval_operand(rhs, rty, solver, generics);
			}

			RValue::Cast { val, from, .. } => self.eval_operand(val, from, solver, generics),
		}
	}

	fn eval_operand(&mut self, op: &Operand, ty: &Type, solver: &ImplSolver, generics: &Generics) {
		match op {
			Operand::LValueUse(lval, kind) => {
				self.eval_lvalue_use(lval, ty, *kind, solver, generics)
			}

			_ => {}
		}
	}

	fn eval_lvalue_use(
		&mut self,
		lval: &LValue,
		ty: &Type,
		props: BindingProps,
		solver: &ImplSolver,
		_generics: &Generics, // will be used to query whether a type implements Copy
	) {
		let _copy_trait = solver.get_lang_trait(LangTrait::Copy);

		// temp hack
		let is_copy = matches!(ty, Type::Basic(_) | Type::Pointer { .. } | Type::Slice(_));

		if !props.is_ref && !is_copy {
			self.set_liveness(lval, LivenessState::Moved);
		}

		// if the lvalue is borrowed as a `new&`,
		// it'll be initialized after this use.
		if props.is_new {
			self.set_liveness(lval, LivenessState::Live);
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
			if func.variables[var].1.is_new {
				state.liveness.insert(
					LValue {
						local: var,
						projection: vec![],
						props: func.variables[var].1,
					},
					LivenessState::Uninit,
				);
			} else {
				state.liveness.insert(
					LValue {
						local: var,
						projection: vec![],
						props: func.variables[var].1,
					},
					LivenessState::Live,
				);
			}
		}
	}
}

impl Analysis for DefInitFlow {
	fn apply_effect(
		&self,
		stmt: &CIRStmt,
		_position: (crate::cir::BlockIndex, crate::cir::StmtIndex),
		state: &mut Self::Domain,
		func: &CIRFunction,
		solver: &ImplSolver,
	) {
		match stmt {
			CIRStmt::Assignment(lval, rval) => {
				state.eval_rvalue(rval, solver, &func.generics);
				state.set_liveness(lval, LivenessState::Live);
			}

			CIRStmt::RefInit(var, _) => {
				let lval = LValue {
					local: *var,
					projection: vec![],
					props: func.variables[*var].1,
				};

				state.set_liveness(&lval, LivenessState::Live);
			}

			CIRStmt::Invoke { result, args, .. } | CIRStmt::Call { result, args, .. } => {
				for (arg, ty, props) in args {
					state.eval_lvalue_use(arg, ty, *props, solver, &func.generics);
				}

				if let Some(result) = result {
					state.set_liveness(result, LivenessState::Live);
				}
			}

			CIRStmt::StorageLive(local) => {
				state.set_liveness(&LValue::new(*local), LivenessState::Uninit);
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
					CIRStmt::Assignment(
						_,
						RValue::Atom(_, _, Operand::LValueUse(lval, use_props), _),
					)
					| CIRStmt::Switch(Operand::LValueUse(lval, use_props), ..)
					| CIRStmt::Assignment(
						_,
						RValue::Cons(_, [(_, Operand::LValueUse(lval, use_props)), _], ..),
					)
					| CIRStmt::Assignment(
						_,
						RValue::Cons(_, [_, (_, Operand::LValueUse(lval, use_props))], ..),
					) => {
						if !use_props.is_new {
							let liveness = state.get_liveness(lval);

							match liveness {
								Some(LivenessState::Live) => {}

								_ => errors.push(ComuneError::new(
										ComuneErrCode::InvalidUse {
											variable: func.get_variable_name(lval.local),
											state: liveness.unwrap_or(LivenessState::Uninit),
										},
										lval.props.span,
									))
								,
							}
						}
					}
					
					CIRStmt::Invoke { args, id, .. } | CIRStmt::Call { args, id, .. } => {
						if let CIRCallId::Indirect { local: lval, .. } = id {
							let liveness = state.get_liveness(lval);

							match liveness {
								Some(LivenessState::Live) => {}

								_ => errors.push(ComuneError::new(
									ComuneErrCode::InvalidUse {
										variable: func.get_variable_name(lval.local),
										state: liveness.unwrap_or(LivenessState::Uninit),
									},
									lval.props.span,
								)),
							}
						}

						for (lval, _, use_props) in args {
							let liveness = state.get_liveness(lval);

							if use_props.is_new {
								match liveness {
									None
									| Some(
										LivenessState::Uninit
										| LivenessState::Dropped
										| LivenessState::Moved,
									) => {}

									_ => errors.push(ComuneError::new(
										ComuneErrCode::InvalidNewReference {
											variable: func.get_variable_name(lval.local),
										},
										lval.props.span,
									)),
								}
							} else {
								match liveness {
									Some(LivenessState::Live) => {}

									_ => errors.push(ComuneError::new(
										ComuneErrCode::InvalidUse {
											variable: func.get_variable_name(lval.local),
											state: liveness.unwrap_or(LivenessState::Uninit),
										},
										lval.props.span,
									)),
								}
							}
						}
					}

					// Check for uninitialized `new&` and `mut&` bindings
					CIRStmt::Return => {
						for (i, (_, props, _)) in func.variables.iter().enumerate() {
							if !props.is_ref {
								continue;
							}

							let lval = LValue {
								local: i,
								projection: vec![],
								props: *props,
							};

							match state.get_liveness(&lval) {
								Some(LivenessState::Live) => {}

								_ => errors.push(ComuneError::new(
									if props.is_new {
										ComuneErrCode::UninitNewReference
									} else {
										ComuneErrCode::UninitMutReference
									},
									props.span,
								)),
							}
						}
					}

					_ => {}
				}

				// Check for mutation of immutable lvalues
				if let CIRStmt::Assignment(lval, _) = stmt {
					let is_var_init =
						!matches!(state.get_liveness(lval), None | Some(LivenessState::Uninit));

					if is_var_init && !lval.is_access_mutable(func.variables[lval.local].0.clone()) {
						errors.push(ComuneError::new(
							ComuneErrCode::ImmutVarMutation {
								variable: func.get_variable_name(lval.local),
							},
							lval.props.span,
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

		// Collect drop flags
		for (i, block) in func.blocks.iter().enumerate() {
			if let CIRStmt::DropShim { var, .. } = block.items.last().unwrap() {
				let state = result.get_state_before(i, block.items.len() - 1);

				let mut elaborator = DropElaborator {
					current_block: i,
					current_fn: &mut func_out,
					state: &state,
				};

				elaborator.collect_drop_flags(&var, &mut drop_flags);
			}
		}

		// Generate destructors
		for (i, block) in func.blocks.iter().enumerate() {
			if let CIRStmt::DropShim { var, next } = block.items.last().unwrap() {
				let state = result.get_state_before(i, block.items.len() - 1);
				let ty = var.get_projected_type(func.variables[var.local].0.clone());

				func_out.blocks[i].items.pop();

				let mut elaborator = DropElaborator {
					current_block: i,
					current_fn: &mut func_out,
					state: &state,
				};

				elaborator.elaborate_drop(&var, &ty, *next, &drop_flags);
				elaborator.write(CIRStmt::Jump(*next));
			}
		}

		// Go through all the dynamic drop flags we've generated
		// and generate their appropriate assignments
		for block in func_out.blocks.iter_mut() {
			let mut j = 0;

			while j < block.items.len() {
				block.items[j].clone().inspect_lvalue_uses(|lval, props| {
					if props.is_ref && !props.is_new {
						return;
					}

					if let Some(flag) = drop_flags.get(lval) {
						block.items.insert(
							j + 1,
							CIRStmt::Assignment(
								LValue {
									local: *flag,
									projection: vec![],
									props: BindingProps::mut_value(),
								},
								if props.is_new {
									RValue::const_bool(true)
								} else {
									RValue::const_bool(false)
								},
							),
						);
					}
				});

				match &block.items[j] {
					CIRStmt::Assignment(lval, _)
					| CIRStmt::Call {
						result: Some(lval), ..
					}
					| CIRStmt::Invoke {
						result: Some(lval), ..
					} => {
						if let Some(flag) = drop_flags.get(lval) {
							block.items.insert(
								j + 1,
								CIRStmt::Assignment(
									LValue {
										local: *flag,
										projection: vec![],
										props: BindingProps::mut_value(),
									},
									RValue::const_bool(true),
								),
							);
						}
					}

					_ => {}
				}

				j += 1
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
	state: &'func LiveVarCheckState,
}

impl<'func> DropElaborator<'func> {
	fn write(&mut self, stmt: CIRStmt) {
		self.current_fn.blocks[self.current_block].items.push(stmt)
	}

	fn collect_drop_flags(&mut self, lval: &LValue, drop_flags: &mut HashMap<LValue, VarIndex>) {
		if drop_flags.contains_key(lval) {
			return;
		}

		match self.state.get_liveness(lval) {
			Some(LivenessState::MaybeUninit) => {
				self.current_fn.variables.push((
					Type::bool_type(),
					BindingProps::mut_value(),
					None,
				));

				let flag = self.current_fn.variables.len() - 1;

				// Write a zero-initializer
				self.current_fn.blocks[0].items.insert(
					0,
					CIRStmt::Assignment(
						LValue::new(flag),
						RValue::Atom(
							Type::bool_type(),
							None,
							Operand::BoolLit(false, SrcSpan::new()),
							SrcSpan::new(),
						),
					),
				);

				drop_flags.insert(lval.clone(), flag);
			}

			_ => {}
		}
	}

	fn elaborate_drop(
		&mut self,
		lval: &LValue,
		ty: &Type,
		next: BlockIndex,
		drop_flags: &HashMap<LValue, VarIndex>,
	) {	
		match self.state.get_liveness(lval) {
			Some(LivenessState::Live) => {
				self.build_destructor(lval, ty, next, drop_flags);
			}

			Some(LivenessState::MaybeUninit) => {
				if !drop_flags.contains_key(lval) {
					eprintln!("COMPILER BUG: no drop flag for MaybeUninit lvalue {lval}, omitting destructor\n");
					return
				}

				let flag = drop_flags[&lval];
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

				self.build_destructor(lval, ty, next, drop_flags);

				self.current_block = start_idx;
				self.write(CIRStmt::Switch(
					Operand::LValueUse(flag_lval, BindingProps::value()),
					vec![(
						Type::bool_type(),
						Operand::BoolLit(true, SrcSpan::new()),
						drop_idx,
					)],
					next,
				));

				self.current_fn.blocks[self.current_block]
					.succs
					.push(drop_idx);
				self.current_block = self.current_fn.blocks.len() - 1;
			}

			_ => {}
		}
	}

	fn build_destructor(
		&mut self,
		lval: &LValue,
		ty: &Type,
		next: BlockIndex,
		drop_flags: &HashMap<LValue, VarIndex>,
	) {
		match ty {
			Type::TypeRef { def, args } => self.build_typedef_destructor(
				lval, 
				&def.upgrade().unwrap(), 
				args, 
				next, 
				drop_flags
			),

			Type::Tuple(TupleKind::Sum, _) => {}

			Type::Tuple(TupleKind::Product, types) => {
				for (i, ty) in types.iter().enumerate() {
					let mut lval = lval.clone();
					lval.projection.push(PlaceElem::Field(i));

					self.elaborate_drop(&lval, ty, next, drop_flags);
				}
			}

			Type::Tuple(TupleKind::Newtype, types) => {
				let [ty] = types.as_slice() else {
					panic!()
				};

				self.elaborate_drop(lval, ty, next, drop_flags);
			}

			_ => {}
		}
	}

	fn build_typedef_destructor(
		&mut self,
		lval: &LValue,
		def: &Arc<RwLock<TypeDef>>,
		args: &GenericArgs,
		next: BlockIndex,
		drop_flags: &HashMap<LValue, VarIndex>,
	) {
		let def_lock = def.read().unwrap();

		assert!(args.is_empty(), "un-monomorphized typedef found during drop elaboration!");

		if let Some(drop) = &def_lock.drop {
			let drop = drop.clone();

			self.write(CIRStmt::Call {
				id: CIRCallId::Direct(drop, SrcSpan::new()),
				args: vec![(
					lval.clone(), 
					Type::TypeRef { 
						def: Arc::downgrade(def),
						args: args.clone()
					}, 
					BindingProps::mut_reference()
				)],
				generic_args: args.clone(),
				result: None,
			});

			if let Some(flag) = drop_flags.get(lval) {
				self.write(CIRStmt::Assignment(
					LValue {
						local: *flag,
						projection: vec![],
						props: BindingProps::mut_value(),
					},
					RValue::const_bool(false),
				));
			}
		}
		
		if !def_lock.variants.is_empty() {
			let start_block = self.current_block;
			let cont_block = self.current_fn.blocks.len();

			// add cont block
			self.current_fn.blocks.push(CIRBlock::new());
			
			let mut branches = vec![];

			for (_, variant) in def_lock.variants.iter() {
				self.current_block = self.current_fn.blocks.len();
				self.current_fn.blocks.push(CIRBlock::new());
				
				branches.push(self.current_block);
				
				let mut variant_lval = lval.clone();
				variant_lval.projection.push(PlaceElem::SumData(
					Type::TypeRef { 
						def: Arc::downgrade(variant), 
						args: args.clone()
					}
				));

				self.build_typedef_destructor(
					&variant_lval,
					variant,
					args,
					next,
					drop_flags
				);

				self.write(CIRStmt::Jump(cont_block));
				self.current_fn.blocks[cont_block].preds.push(self.current_block);
			}

			let mut discriminant = lval.clone();
			
			discriminant.projection.push(PlaceElem::SumDisc);

			// Generate switch to all the variants' destructors
			self.current_fn.blocks[start_block].items.push(
				CIRStmt::Switch(
					Operand::LValueUse(discriminant, BindingProps::value()), 
					branches
						.iter()
						.cloned()
						.enumerate()
						.map(|(i, idx)| (Type::i32_type(true), Operand::IntegerLit(i as i128, SrcSpan::new()), idx))
						.collect(),
					cont_block
				)
		 	);

			self.current_block = cont_block;
			self.current_fn.blocks[start_block].succs = branches;
		}

		for (i, (_, member_ty, _)) in def_lock.members.iter().enumerate() {
			let mut member = lval.clone();

			member.projection.push(PlaceElem::Field(i));

			if def_lock.drop.is_some() {
				self.build_destructor(&member, member_ty, next, drop_flags)
			} else {
				self.elaborate_drop(&member, member_ty, next, drop_flags)
			}
		}
	}
}
