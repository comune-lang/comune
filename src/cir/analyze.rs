use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use super::{CIRFunction, CIRModule};

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
		for pass in &self.passes {
			match pass {
				Pass::Shared(shared) => shared.par_iter().for_each(|p| p.on_module(module)),

				Pass::Unique(unique) => unique.on_module(module),
			}
		}

		for func in &mut module.functions {
			self.run_on_function(&mut func.1 .0)
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
