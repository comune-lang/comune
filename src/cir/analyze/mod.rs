use std::collections::HashSet;

use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use crate::{errors::CMNError, parser::AnalyzeResult, semantic::ast::TokenData};

use super::{BlockIndex, CIRBlock, CIRFunction, CIRModule, CIRStmt, StmtIndex};

pub mod cleanup;
pub mod lifeline;
pub mod verify;

pub trait CIRPass: Send + Sync {
	fn on_function(&self, _func: &CIRFunction) -> Vec<(CMNError, TokenData)> {
		vec![]
	}

	fn on_module(&self, _module: &CIRModule) -> Vec<(CMNError, TokenData)> {
		vec![]
	}
}

pub trait CIRPassMut {
	fn on_function(&self, _func: &mut CIRFunction) -> Vec<(CMNError, TokenData)> {
		vec![]
	}

	fn on_module(&self, _module: &mut CIRModule) -> Vec<(CMNError, TokenData)> {
		vec![]
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

	pub fn run_on_module(&self, module: &mut CIRModule) -> Vec<(CMNError, TokenData)> {
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

	pub fn run_on_function(&self, func: &mut CIRFunction) -> Vec<(CMNError, TokenData)> {
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

// CFG Walking

type JumpID = ((BlockIndex, StmtIndex), BlockIndex);

impl CIRFunction {
	// Walk the MIR, calling a closure on every unique statement sequence (minus terminators)

	pub fn walk_cfg<State: Clone>(
		&self,
		initial_state: State,
		f: impl Fn(&mut State, &CIRStmt) -> AnalyzeResult<()>,
	) -> Vec<(CMNError, TokenData)> {
		self.walk_block(0, initial_state, &f, &mut HashSet::new())
	}

	pub fn walk_cfg_mut<State: Clone>(
		&mut self,
		initial_state: State,
		f: impl Fn(&mut State, &mut CIRBlock, StmtIndex) -> AnalyzeResult<()>,
	) -> Vec<(CMNError, TokenData)> {
		self.walk_block_mut(0, initial_state, &f, &mut HashSet::new())
	}

	fn walk_block<State: Clone>(
		&self,
		i: usize,
		mut state: State,
		f: &impl Fn(&mut State, &CIRStmt) -> AnalyzeResult<()>,
		processed_jumps: &mut HashSet<JumpID>,
	) -> Vec<(CMNError, TokenData)> {
		let mut errors = vec![];

		for j in 0..self.blocks[i].len() {
			if let Err(e) = f(&mut state, &self.blocks[i][j]) {
				errors.push(e);
			};
		}

		let j = self.blocks[i].len() - 1;

		match &self.blocks[i][j] {
			// Handle terminators
			CIRStmt::Jump(jmp) => {
				errors.append(&mut self.walk_block(*jmp, state, f, processed_jumps))
			}

			CIRStmt::Branch(_, a, b) => {
				if !processed_jumps.contains(&((j, i), *a)) {
					processed_jumps.insert(((j, i), *a));
					errors.append(&mut self.walk_block(*a, state.clone(), f, processed_jumps));
				}

				if !processed_jumps.contains(&((j, i), *b)) {
					processed_jumps.insert(((j, i), *b));
					errors.append(&mut self.walk_block(*b, state, f, processed_jumps));
				}
			}

			CIRStmt::Return(_) => {}

			_ => panic!("no terminator!"),
		}

		errors
	}

	fn walk_block_mut<State: Clone>(
		&mut self,
		i: usize,
		mut state: State,
		f: impl Fn(&mut State, &mut CIRBlock, StmtIndex) -> AnalyzeResult<()>,
		processed_jumps: &mut HashSet<JumpID>,
	) -> Vec<(CMNError, TokenData)> {
		let mut errors = vec![];

		for j in 0..self.blocks[i].len() {
			if let Err(e) = f(&mut state, &mut self.blocks[i], j) {
				errors.push(e)
			}
		}

		let j = self.blocks[i].len() - 1;

		match &self.blocks[i][j] {
			// Handle terminators
			CIRStmt::Jump(jmp) => {
				if !processed_jumps.contains(&((j, i), *jmp)) {
					processed_jumps.insert(((j, i), *jmp));
					errors.append(&mut self.walk_block_mut(*jmp, state, f, processed_jumps))
				}
			}

			CIRStmt::Branch(_, a, b) => {
				let a = *a;
				let b = *b; // Make the borrow checker happy

				if !processed_jumps.contains(&((j, i), a)) {
					processed_jumps.insert(((j, i), a));
					errors.append(&mut self.walk_block_mut(a, state.clone(), &f, processed_jumps));
				}

				if !processed_jumps.contains(&((j, i), b)) {
					processed_jumps.insert(((j, i), b));
					errors.append(&mut self.walk_block_mut(b, state, &f, processed_jumps));
				}
			}

			CIRStmt::Return(_) => {}

			_ => panic!("no terminator!"),
		}

		errors
	}
}
