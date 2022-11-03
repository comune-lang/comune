// cIR monomorphization module

use std::collections::{HashMap, HashSet};

use crate::{
	lexer::Token,
	semantic::{get_attribute, namespace::Identifier, types::Basic},
};

use super::{CIRFunction, CIRModule, CIRStmt, CIRType, CIRTypeDef, Operand, RValue, TypeName};

// A set of requested Generic monomorphizations, with a Vec of type arguments
// TODO: Extend system to support constants as arguments
type MonoizationList = HashSet<(Identifier, Vec<CIRType>)>;

type TypeSubstitutions = Vec<CIRType>;

// Map from TypeIndex + parameters to existing instance TypeIndexes
type TypeInstances = HashMap<TypeName, HashMap<TypeSubstitutions, TypeName>>;

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
		
		let mut instantiations = HashMap::new();

		for func in &mut self.functions {
			for (var, _) in &mut func.1 .0.variables {
				Self::monoize_type(&mut self.types, var, &vec![], &mut instantiations);
			}

			for block in &mut func.1 .0.blocks {
				for mut stmt in block {
					match &mut stmt {
						CIRStmt::Expression(expr, _)
						| CIRStmt::Assignment(_, (expr, _))
						| CIRStmt::Branch(expr, _, _)
						| CIRStmt::Return(Some((expr, _))) => {
							Self::monoize_rvalue_types(
								&mut self.types,
								expr,
								&vec![],
								&mut instantiations,
							);
						}

						_ => {}
					}

					if let CIRStmt::Assignment((_lval, _), _) = &mut stmt {
						// TODO: Find RValues in LValue projection
					}
				}
			}
		}

		// Remove generics
		for generic in instantiations.keys() {
			self.types.remove(generic);
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
			Operand::FnCall(_name, args, _) => {
				let mut result = HashSet::new();

				// TODO: Add type parameters to Atom::FnCall and Operand::FnCall

				for arg in args {
					result.extend(self.get_rvalue_monoizations(arg));
				}

				result
			}

			_ => HashSet::new(),
		}
	}

	fn monoize_rvalue_types(
		types: &mut HashMap<String, CIRTypeDef>,
		rval: &mut RValue,
		// Maps parameter indices to the actual types being instantiated
		param_map: &TypeSubstitutions,
		instances: &mut TypeInstances,
	) {
		match rval {
			RValue::Atom(ty, _, _) => {
				Self::monoize_type(types, ty, param_map, instances);
			}

			RValue::Cons(ty, [(lty, _), (rty, _)], _) => {
				Self::monoize_type(types, lty, param_map, instances);
				Self::monoize_type(types, rty, param_map, instances);
				Self::monoize_type(types, ty, param_map, instances);
			}

			RValue::Cast { from, to, .. } => {
				Self::monoize_type(types, from, param_map, instances);
				Self::monoize_type(types, to, param_map, instances);
			}
		}
	}

	fn monoize_type(
		types: &mut HashMap<String, CIRTypeDef>,
		ty: &mut CIRType,
		param_map: &TypeSubstitutions,
		instances: &mut TypeInstances,
	) {
		match ty {
			CIRType::Basic(_) => {}

			CIRType::Pointer(pointee) => Self::monoize_type(types, pointee, param_map, instances),
			CIRType::Array(arr_ty, _) => Self::monoize_type(types, arr_ty, param_map, instances),
			CIRType::Reference(refee) => Self::monoize_type(types, refee, param_map, instances),

			CIRType::TypeRef(idx, args) => {

				// If we're referring to a type with generics, check if the 
				// instantation we want exists already. If not, create it.
				if !args.is_empty() {
					if !instances.contains_key(idx) {
						instances.insert(idx.clone(), HashMap::new());
					}

					if !instances[idx].contains_key(param_map) {
						*idx =
							Self::instantiate_type_def(types, idx.clone(), &args, instances);
					}
				}
			}
			
			CIRType::TypeParam(idx) => {
				*ty = param_map[*idx].clone();
			}
		}
	}

	// Takes a Generic CIRTypeDef with parameters and instantiates it.
	fn instantiate_type_def(
		types: &mut HashMap<String, CIRTypeDef>,
		name: TypeName,
		param_map: &TypeSubstitutions,
		instances: &mut TypeInstances,
	) -> TypeName {

		let mut instance = types[&name].clone();

		match &mut instance {
			CIRTypeDef::Algebraic { members, type_params, .. } => {
				for member in members {
					Self::monoize_type(types, member, param_map, instances);
				}
				type_params.clear();
			}

			CIRTypeDef::Class {} => todo!(),
		}

		let mut iter = param_map.iter();
		let mut insert_idx = name + "<" + &iter.next().unwrap().to_string();

		for param in iter {
			insert_idx.push_str(&param.to_string())
		}

		insert_idx += ">";

		types.insert(insert_idx.clone(), instance);
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
