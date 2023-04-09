// cleanup passes. TODO: write any, lmao
// (there used to be a RemoveNoOps pass, but recent cIR refactors made it redundant)

use std::collections::BTreeMap;

use crate::{
	cir::{CIRFunction, CIRStmt},
	errors::ComuneError,
};

use super::CIRPassMut;

pub struct SimplifyCFG;

impl CIRPassMut for SimplifyCFG {
	fn on_function(&self, func: &mut CIRFunction) -> Vec<ComuneError> {
		// SimplifyCFG cIR pass

		// This cIR pass removes "no-op" blocks that consist of a single
		// CIRStmt::Jump instruction. These blocks can crop up from nested
		// control flow expressions, where the builder doesn't have enough
		// context to combine the blocks while building the CFG.

		let mut block_map = BTreeMap::from_iter((0..func.blocks.len()).map(|i| (i, i)));

		for (i, block) in func.blocks.iter().enumerate() {
			if let [CIRStmt::Jump(idx)] = block.items.as_slice() {
				// idx might have already shifted, so get the mapped index instead
				block_map.insert(i, block_map[idx]);

				// Decrease all greater block indices by one
				for j in (i + 1)..func.blocks.len() {
					block_map.insert(j, block_map[&j] - 1);
				}
			}
		}

		let mut new_blocks = vec![];

		for block in func.blocks.iter() {
			if !matches!(block.items.as_slice(), [CIRStmt::Jump(_)]) {
				let mut new_block = block.clone();

				for succ in &mut new_block.succs {
					*succ = block_map[succ];
				}

				match new_block.items.last_mut().unwrap() {
					CIRStmt::Jump(idx) => *idx = block_map[idx],

					CIRStmt::Switch(_, branches, else_branch) => {
						for (.., branch) in branches {
							*branch = block_map[branch];
						}

						*else_branch = block_map[else_branch];
					}

					CIRStmt::Invoke { next, except, .. } => {
						*next = block_map[next];
						*except = block_map[except];
					}

					_ => {}
				}

				new_block.preds.clear();

				new_blocks.push(new_block);
			}
		}

		// Rebuild preds
		for i in 0..new_blocks.len() {
			let succs = new_blocks[i].succs.clone();

			for succ in succs {
				new_blocks[succ].preds.push(i);
			}
		}

		func.blocks = new_blocks;

		vec![]
	}
}
