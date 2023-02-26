use std::collections::{VecDeque, BTreeMap};

use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use crate::errors::ComuneError;

use super::{BlockIndex, CIRFunction, CIRModule, CIRStmt, StmtIndex};

pub mod cleanup;
pub mod lifeline;
pub mod verify;

pub trait CIRPass: Send + Sync {
	fn on_function(&self, _func: &CIRFunction) -> Vec<ComuneError> {
		vec![]
	}

	fn on_module(&self, _module: &CIRModule) -> Vec<ComuneError> {
		vec![]
	}
}

pub trait CIRPassMut {
	fn on_function(&self, _func: &mut CIRFunction) -> Vec<ComuneError> {
		vec![]
	}

	fn on_module(&self, _module: &mut CIRModule) -> Vec<ComuneError> {
		vec![]
	}
}

impl<T> CIRPassMut for T
where
	T: CIRPass,
{
	fn on_function(&self, func: &mut CIRFunction) -> Vec<ComuneError> {
		self.on_function(func)
	}

	fn on_module(&self, module: &mut CIRModule) -> Vec<ComuneError> {
		self.on_module(module)
	}
}

enum Pass {
	Shared(Vec<Box<dyn CIRPass>>),
	Unique(Box<dyn CIRPassMut>),
}

pub struct CIRPassManager {
	passes: Vec<Pass>,
}

impl CIRPassManager {
	pub fn new() -> Self {
		CIRPassManager { passes: vec![] }
	}

	pub fn add_pass(&mut self, pass: impl CIRPass + 'static) {
		match self.passes.last_mut() {
			Some(Pass::Shared(passes)) => passes.push(Box::new(pass)),

			None | Some(Pass::Unique(_)) => self.passes.push(Pass::Shared(vec![Box::new(pass)])),
		}
	}

	pub fn add_mut_pass(&mut self, pass: impl CIRPassMut + 'static) {
		self.passes.push(Pass::Unique(Box::new(pass)))
	}

	pub fn run_on_module(&self, module: &mut CIRModule) -> Vec<ComuneError> {
		let mut errors = vec![];

		// Run on each function
		for func in module.functions.iter_mut().filter(|func| !func.1.is_extern) {
			errors.append(&mut self.run_on_function(func.1));
		}

		// Run on module as a whole
		for pass in &self.passes {
			match pass {
				Pass::Shared(shared) => {
					let results: Vec<_> = shared.par_iter().map(|p| p.on_module(module)).collect();

					for mut result in results {
						errors.append(&mut result);
					}
				}

				Pass::Unique(unique) => {
					errors.append(&mut unique.on_module(module));
				}
			}
		}

		errors
	}

	pub fn run_on_function(&self, func: &mut CIRFunction) -> Vec<ComuneError> {
		let mut errors = vec![];

		for pass in &self.passes {
			match pass {
				Pass::Shared(shared) => {
					let results: Vec<_> = shared.par_iter().map(|p| p.on_function(func)).collect();
					for mut result in results {
						errors.append(&mut result);
					}
				}

				Pass::Unique(unique) => {
					errors.append(&mut unique.on_function(func));
				}
			}
		}

		errors
	}
}

// Static Program Analysis
//
// listen. i have stared at so many fucking pages of arcane
// math symbols these past few days, and i finally *think* i
// understand just enough to write this shit. but i can make
// no promises of explaining it clearly.
//
// basically, this framework lets us do Weird Math Shit to
// turn CFG analysis into a problem of finding the fixpoint
// of a "join-semilattice". if you wanna know more, check out:
// https://cs.au.dk/~amoeller/spa/spa.pdf
//
// oh also this API is pretty much taken verbatim from rustc lol

pub trait JoinSemiLattice {
	fn join(&mut self, other: &Self) -> bool;
}

pub trait AnalysisDomain {
	type Domain: Clone + JoinSemiLattice;
	type Direction: Direction;

	fn bottom_value(&self, func: &CIRFunction) -> Self::Domain;
	fn initialize_start_block(&self, func: &CIRFunction, state: &mut Self::Domain);
}

pub trait Analysis: AnalysisDomain {
	fn apply_before_effect(
		&self,
		_stmt: &CIRStmt,
		_position: (BlockIndex, StmtIndex),
		_state: &mut Self::Domain,
	) {
	}

	fn apply_effect(
		&self,
		stmt: &CIRStmt,
		position: (BlockIndex, StmtIndex),
		state: &mut Self::Domain,
	);
}

pub trait Direction {
	const IS_FORWARD: bool;
}

pub struct Forward;
pub struct Backward;

impl Direction for Forward {
	const IS_FORWARD: bool = true;
}

impl Direction for Backward {
	const IS_FORWARD: bool = false;
}

pub trait AnalysisResultHandler: Analysis {
	fn process_result(result: ResultVisitor<Self>, func: &CIRFunction) -> Vec<ComuneError>
	where
		Self: Sized;
}

pub struct DataFlowPass<T>
where
	T: AnalysisResultHandler + Send + Sync,
{
	analysis: T,
}

impl<T> DataFlowPass<T>
where
	T: AnalysisResultHandler + Send + Sync,
{
	pub fn new(analysis: T) -> Self {
		Self { analysis }
	}
}

impl<T> CIRPass for DataFlowPass<T>
where
	T: AnalysisResultHandler + Send + Sync,
{
	fn on_function(&self, func: &CIRFunction) -> Vec<ComuneError> {
		let mut entry_state  = self.analysis.bottom_value(func);

		self.analysis.initialize_start_block(func, &mut entry_state);

		// Prevent entry_state from being mutated
		let entry_state = entry_state;

		let mut in_states = BTreeMap::new();
		let mut out_states = BTreeMap::new();
		let mut work_list = VecDeque::new();

		// Initialize blocks
		
		in_states.insert(0, entry_state.clone());

		let mut block_state = entry_state.clone();

		for (j, stmt) in func.blocks[0].items.iter().enumerate() {
			self.analysis.apply_before_effect(stmt, (0, j), &mut block_state);
			self.analysis.apply_effect(stmt, (0, j), &mut block_state);
		}

		out_states.insert(0, block_state.clone());

		work_list.extend(func.blocks[0].succs.iter().cloned());

		// While we haven't reached fixpoint, update blocks iteratively
		// If a block's in-state changes, process it and its successors

		while let Some(i) = work_list.pop_front() {
			let block = &func.blocks[i];
			let mut changed = false;

			if !block.preds.is_empty() {
				let mut preds = block.preds.iter();

				let mut in_state = out_states[preds.next().unwrap()].clone();

				for pred in preds {
					if let Some(out_state) = out_states.get(pred) {					
						in_state.join(out_state);
					}
				}
				
				// check if in_state is different from in_states[i]
				if let Some(prev_state) = in_states.get(&i) {
					changed |= in_state.clone().join(prev_state);
				} else {
					changed = true;
				}
				
				in_states.insert(i, in_state);
			}

			if changed {
				let block_state: &T::Domain = &in_states[&i];
				
				let mut block_state = block_state.clone();

				for (j, stmt) in block.items.iter().enumerate() {
					self.analysis.apply_before_effect(stmt, (i, j), &mut block_state);
					self.analysis.apply_effect(stmt, (i, j), &mut block_state);
				}
				
				if let Some(out_state) = out_states.get(&i) {
					if out_state.clone().join(&block_state) {
						out_states.insert(i, block_state.clone());
						work_list.extend(block.succs.clone().into_iter());
					}
				} else {
					out_states.insert(i, block_state.clone());
					work_list.extend(block.succs.clone().into_iter());
				}
			}
		}

		// Fill unreachable blocks with bottom value
		for i in 0..func.blocks.len() {
			if !in_states.contains_key(&i) {
				in_states.insert(i, self.analysis.bottom_value(func));
			}
		}

		let in_states = in_states.into_iter().map(|(_, state)| state).collect();

		T::process_result(ResultVisitor::new(func, &self.analysis, in_states), func)
	}
}

pub struct ResultVisitor<'a, T>
where
	T: Analysis,
{
	func: &'a CIRFunction,
	analysis: &'a T,
	block_start_states: Vec<T::Domain>,
}

impl<'a, T> ResultVisitor<'a, T>
where
	T: Analysis,
{
	fn new(func: &'a CIRFunction, analysis: &'a T, block_start_states: Vec<T::Domain>) -> Self {
		Self {
			func,
			analysis,
			block_start_states,
		}
	}

	pub fn get_state_before(&self, block: BlockIndex, stmt: StmtIndex) -> T::Domain {
		if stmt == 0 {
			self.block_start_states[block].clone()
		} else {
			let mut result = self.block_start_states[block].clone();

			for i in 0..stmt {
				let s = &self.func.blocks[block].items[i];
				self.analysis
					.apply_before_effect(s, (block, i), &mut result);
				self.analysis.apply_effect(s, (block, i), &mut result);
			}

			self.analysis.apply_before_effect(&self.func.blocks[block].items[stmt], (block, stmt), &mut result);

			result
		}
	}
}
