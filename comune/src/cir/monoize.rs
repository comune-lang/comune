// cIR monomorphization module

use crate::semantic::{get_attribute, namespace::Identifier, types::Basic};

use super::{CIRFunction, CIRModule, CIRStmt, CIRType, Operand, RValue};

impl CIRModule {
	// monoize() consumes `self` and returns a CIRModule with all generics monomorphized, names mangled, etc.
	// This is necessary to prepare the module for LLVM codegen, but should be done after semantic analysis is complete.
	pub fn monoize(mut self) -> Self {
		// Mangle functions

		for func in &mut self.functions {
			// Check if the function has a `no_mangle` attribute, or if it's `main`. If not, mangle the name
			if get_attribute(&func.1 .0.attributes, "no_mangle").is_some()
				|| (&**func.0.name() == "main" && !func.0.is_qualified())
			{
				func.1 .1 = Some(func.0.name().to_string());
			} else {
				// Mangle name
				func.1 .1 = Some(mangle_name(func.0, &func.1 .0));
			}
		}

		for func in &self.functions {
			for block in &func.1 .0.blocks {
				for stmt in block {
					match stmt {
						CIRStmt::Expression(expr) => {
							self.monoize_rvalue(&expr);
						}

						CIRStmt::Assignment(_, expr) => {
							self.monoize_rvalue(&expr);
						}

						CIRStmt::Branch(cond, _, _) => {
							self.monoize_rvalue(&cond);
						}

						CIRStmt::Return(Some(expr)) => {
							self.monoize_rvalue(expr);
						}

						_ => {}
					}
				}
			}
		}

		self
	}

	fn monoize_rvalue(&self, expr: &RValue) {
		match expr {
			RValue::Atom(_, _, op) => self.monoize_operand(op),

			RValue::Cons(_, [(_, lhs), (_, rhs)], _) => {
				self.monoize_operand(lhs);
				self.monoize_operand(rhs);
			}

			RValue::Cast { val, .. } => self.monoize_operand(val),
		}
	}

	fn monoize_operand(&self, op: &Operand) {
		match op {
			Operand::FnCall(id, _, mangled) => {
				mangled
					.write()
					.unwrap()
					.replace(self.functions[&id].1.as_ref().unwrap().clone());
			}
			_ => {}
		}
	}
}

// Basic implementation of the Itanium C++ ABI, which is used by GCC and Clang.
// This is not complete or robust at all, but it should do for now.

fn mangle_name(name: &Identifier, func: &CIRFunction) -> String {
	let mut result = String::from("_Z");

	assert!(name.absolute);

	if !name.is_qualified() {
		result.push_str(&name.name().len().to_string());
		result.push_str(name.name());
	} else {
		result.push('N');
		for scope in &name.path {
			result.push_str(&scope.len().to_string());
			result.push_str(scope);
		}
		result.push('E');
	}

	if func.arg_count == 0 {
		result.push('v');
	} else {
		for i in 0..func.arg_count {
			result.push_str(&func.variables[i].0.mangle());
		}
	}

	result
}

impl CIRType {
	fn mangle(&self) -> String {
		match self {
			CIRType::Basic(b) => String::from(b.mangle()),
			CIRType::Pointer(p) => String::from("P") + &p.mangle(),
			CIRType::Reference(r) => String::from("R") + &r.mangle(),
			CIRType::TypeRef(_) => format!("S_"),
			_ => todo!(),
		}
	}
}

// See https://itanium-cxx-abi.github.io/cxx-abi/abi.html#mangle.builtin-type
impl Basic {
	fn mangle(&self) -> &str {
		match self {
			Basic::BOOL => "b",

			Basic::INTEGRAL { signed, size_bytes } => {
				if *signed {
					match size_bytes {
						8 => "x",
						4 => "i",
						2 => "s",
						1 => "c",
						_ => unimplemented!(),
					}
				} else {
					match size_bytes {
						8 => "y",
						4 => "j",
						2 => "t",
						1 => "h",
						_ => unimplemented!(),
					}
				}
			}

			Basic::SIZEINT { signed } => {
				if *signed {
					"x"
				} else {
					"y"
				}
			}

			Basic::FLOAT { size_bytes } => match size_bytes {
				8 => "d",
				4 => "f",
				_ => unimplemented!(),
			},

			Basic::CHAR => "c",
			Basic::VOID => "v",
			Basic::STR => "cj", // TODO: Figure this out
		}
	}
}
