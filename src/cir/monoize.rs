// cIR monomorphization module

use std::collections::{HashSet, HashMap};

use crate::{
	lexer::Token,
	semantic::{get_attribute, namespace::Identifier, types::Basic},
};

use super::{CIRFunction, CIRModule, CIRStmt, CIRType, Operand, RValue, CIRTypeDef, TypeIndex};

// A set of requested Generic monomorphizations, with a Vec of type arguments
// TODO: Extend system to support constants as arguments
type MonoizationList = HashSet<(Identifier, Vec<CIRType>)>;

// Map from TypeIndex + parameters to existing instance TypeIndexes
type TypeInstanceMap = HashMap<TypeIndex, HashMap<Vec<CIRType>, TypeIndex>>;

impl CIRModule {
	// monoize() consumes `self` and returns a CIRModule with all generics monomorphized, names mangled, etc.
	// This is necessary to prepare the module for LLVM codegen, but should be done after semantic analysis is complete.
	// The function takes `self` by value to convey that this is a destructive operation.
	pub fn monoize(mut self) -> Self {
		self.monoize_generics();
		self.mangle();
		self
	}

	fn monoize_generics(&mut self) {
		let mut fn_instances = HashSet::new();

		for func in &self.functions {
			let func = &func.1 .0;

			for block in &func.blocks {
				for stmt in block {
					match &stmt {
						CIRStmt::Expression(expr, _)
						| CIRStmt::Assignment(_, (expr, _))
						| CIRStmt::Branch(expr, _, _)
						| CIRStmt::Return(Some((expr, _))) => {
							fn_instances.extend(self.get_rvalue_monoizations(expr));
						}

						_ => {}
					}
				}
			}
		}
	}

	fn get_rvalue_monoizations(&self, rval: &RValue) -> MonoizationList {
		match rval {
			RValue::Atom(_, _, op) => self.get_operand_monoizations(op),
			
			RValue::Cons(_, [(_, lhs), (_, rhs)], _) => {
				let mut result = self.get_operand_monoizations(lhs);
				result.extend(self.get_operand_monoizations(rhs));
				result
			}

			RValue::Cast { val, .. } => self.get_operand_monoizations(val),
		}
	}

	fn get_operand_monoizations(&self, op: &Operand) -> MonoizationList {
		match op {
			Operand::FnCall(name, args, _) => {
				let mut result = HashSet::new();

				// TODO: Add type parameters to Atom::FnCall and Operand::FnCall
				
				for arg in args {
					result.extend(self.get_rvalue_monoizations(arg));
				}

				result
			}

			_ => HashSet::new()
		}
	}

	fn monoize_type(&mut self, ty: &mut CIRType, params: &Vec<CIRType>, instances: &mut TypeInstanceMap) {
		match ty {
			CIRType::Basic(_) => {},
			
			CIRType::Pointer(pointee) => self.monoize_type(pointee, params, instances),
			CIRType::Array(arr_ty, _) => self.monoize_type(arr_ty, params, instances),
			CIRType::Reference(refee) => self.monoize_type(refee, params, instances),

			CIRType::TypeRef(idx, params) => {
				if !params.is_empty() {
					if !instances.contains_key(idx) {
						instances.insert(*idx, HashMap::new());
					}

					if !instances[idx].contains_key(params) { // TODO: Fix wasteful clone
						*idx = self.instantiate_type_def(*idx, params, instances);
						params.clear();
					}
				}
			}
		}
	}

	// Takes a Generic CIRTypeDef with parameters and instantiates it.
	fn instantiate_type_def(&mut self, idx: TypeIndex, params: &Vec<CIRType>, instances: &mut TypeInstanceMap) -> TypeIndex {
		let mut instance = self.types[&idx].clone();

		match &mut instance {
			CIRTypeDef::Algebraic { members, .. } => {
				for member in members {
					self.monoize_type(member, params, instances);
				}
			}

			CIRTypeDef::Class {  } => todo!(),
			
			CIRTypeDef::TypeParam(_) => panic!(), // This shouldn't be in the module's type list!
		}
		let insert_idx = self.types.len();
		self.types.insert(insert_idx, instance);
		insert_idx
	}

	fn mangle(&mut self) {
		// Mangle functions

		for func in &mut self.functions {
			// Check if the function has a `no_mangle` or `export_as` attribute, or if it's `main`. If not, mangle the name
			if get_attribute(&func.1 .0.attributes, "no_mangle").is_some()
				|| (&**func.0.name() == "main" && !func.0.is_qualified())
			{
				func.1 .1 = Some(func.0.name().to_string());
			} else if let Some(export_name) = get_attribute(&func.1 .0.attributes, "export_as") {
				// Export with custom symbol name
				if let Some(first_arg) = export_name.args.get(0) {
					if let Some(Token::StringLiteral(name)) = first_arg.get(0) {
						func.1 .1 = Some(name.clone())
					} else {
						panic!() //TODO: Proper error handling
					}
				}
			} else {
				// Mangle name
				func.1 .1 = Some(mangle_name(func.0, &func.1 .0));
			}
		}

		for func in &self.functions {
			for block in &func.1 .0.blocks {
				for stmt in block {
					match stmt {
						CIRStmt::Expression(expr, _) => {
							self.mangle_rvalue(&expr);
						}

						CIRStmt::Assignment(_, (expr, _)) => {
							self.mangle_rvalue(&expr);
						}

						CIRStmt::Branch(cond, _, _) => {
							self.mangle_rvalue(&cond);
						}

						CIRStmt::Return(Some((expr, _))) => {
							self.mangle_rvalue(expr);
						}

						_ => {}
					}
				}
			}
		}
	}

	fn mangle_rvalue(&self, expr: &RValue) {
		match expr {
			RValue::Atom(_, _, op) => self.mangle_operand(op),

			RValue::Cons(_, [(_, lhs), (_, rhs)], _) => {
				self.mangle_operand(lhs);
				self.mangle_operand(rhs);
			}

			RValue::Cast { val, .. } => self.mangle_operand(val),
		}
	}

	fn mangle_operand(&self, op: &Operand) {
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
			CIRType::TypeRef(_, _) => format!("S_"),
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
