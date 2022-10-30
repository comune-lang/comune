use std::collections::HashSet;

use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use super::{CIRFunction, CIRModule, CIRBlock, CIRStmt, BlockIndex, StmtIndex};

pub mod borrowck;
pub mod cleanup;
pub mod verify;

pub trait CIRPass: Send + Sync {
	fn on_function(&self, _func: &CIRFunction) {}

	fn on_module(&self, _module: &CIRModule) {}
}

pub trait CIRPassMut {
	fn on_function(&self, _func: &mut CIRFunction) {}

	fn on_module(&self, _module: &mut CIRModule) {}
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

	pub fn run_on_module(&self, module: &mut CIRModule) {
		// Run on each function
		for func in module.functions.iter_mut().filter(|func| !func.1.0.is_extern) {
			self.run_on_function(&mut func.1 .0)
		}

		// Run on module as a whole
		for pass in &self.passes {
			match pass {
				Pass::Shared(shared) => shared.par_iter().for_each(|p| p.on_module(module)),

				Pass::Unique(unique) => unique.on_module(module),
			}
		}
	}

	pub fn run_on_function(&self, func: &mut CIRFunction) {
		for pass in &self.passes {
			match pass {
				Pass::Shared(shared) => shared.par_iter().for_each(|p| p.on_function(func)),

				Pass::Unique(unique) => unique.on_function(func),
			}
		}
	}
}

// CFG Walking

type JumpID = ((BlockIndex, StmtIndex), BlockIndex);

impl CIRFunction {
	// Walk the MIR, calling a closure on every unique statement sequence (minus terminators)

	pub fn walk_cfg<State: Clone>(&self, initial_state: State, f: impl Fn(&mut State, &CIRStmt)) -> Vec<State> {
		self.walk_block(0, initial_state, &f, &mut HashSet::new())
	}

	pub fn walk_cfg_mut<State: Clone>(&mut self, initial_state: State, f: impl Fn(&mut State, &mut CIRBlock, StmtIndex)) -> Vec<State> {
		self.walk_block_mut(0, initial_state, &f, &mut HashSet::new())
	}
	
	fn walk_block<State: Clone>(&self, i: usize, mut state: State, f: &impl Fn(&mut State, &CIRStmt), processed_jumps: &mut HashSet<JumpID>) -> Vec<State> {
		for j in 0..self.blocks[i].len() {
			f(&mut state, &self.blocks[i][j]);
		}
		
		let j = self.blocks[i].len() - 1;

		match &self.blocks[i][j] {

			// Handle terminators
			
			CIRStmt::Jump(jmp) => self.walk_block(*jmp, state, f, processed_jumps),
			

			CIRStmt::Branch(_, a, b) => {
				let mut result = vec![];

				if !processed_jumps.contains(&((j, i), *a)) {
					processed_jumps.insert(((j, i), *a));
					result.append(&mut self.walk_block(*a, state.clone(), f, processed_jumps));
				}
				
				if !processed_jumps.contains(&((j, i), *b)) {
					processed_jumps.insert(((j, i), *b));
					result.append(&mut self.walk_block(*b, state, f, processed_jumps));
				}

				result
			}

			CIRStmt::Return(_) => vec![state],

			_ => panic!("no terminator!")
		}
	}

	fn walk_block_mut<State: Clone>(&mut self, i: usize, mut state: State, f: impl Fn(&mut State, &mut CIRBlock, StmtIndex), processed_jumps: &mut HashSet<JumpID>) -> Vec<State> {
		for j in 0..self.blocks[i].len() {
			f(&mut state, &mut self.blocks[i], j);
		}
		
		let j = self.blocks[i].len() - 1;

		match &self.blocks[i][j] {

			// Handle terminators
			
			CIRStmt::Jump(jmp) => {
				if !processed_jumps.contains(&((j, i), *jmp)) {
					processed_jumps.insert(((j, i), *jmp));
					self.walk_block_mut(*jmp, state, f, processed_jumps)
				} else {
					vec![]
				}
			}

			CIRStmt::Branch(_, a, b) => {
				let mut result = vec![];
				let a = *a;
				let b = *b; // Make the borrow checker happy

				if !processed_jumps.contains(&((j, i), a)) {
					processed_jumps.insert(((j, i), a));
					result.append(&mut self.walk_block_mut(a, state.clone(), &f, processed_jumps));
				}
				
				if !processed_jumps.contains(&((j, i), b)) {
					processed_jumps.insert(((j, i), b));
					result.append(&mut self.walk_block_mut(b, state, &f, processed_jumps));
				}

				result
			}

			CIRStmt::Return(_) => vec![state],

			_ => panic!("no terminator!")
		}
	}
}