use std::fmt::Display;

use crate::semantic::types::DataLayout;

use super::{
	CIRFunction, CIRModule, CIRStmt, CIRType, CIRTypeDef, LValue, Operand, PlaceElem, RValue,
};

impl Display for CIRModule {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for ty in &self.types {
			write!(f, "{ty}")?;
		}

		for func in &self.functions {
			write!(f, "fn {} {}", func.0, func.1)?;
		}

		Ok(())
	}
}

impl Display for CIRFunction {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if self.arg_count > 0 {
			write!(f, "({}", self.variables[0])?;

			for i in 1..self.arg_count {
				write!(f, ", {}", self.variables[i])?;
			}

			write!(f, ") -> {} {{\n", self.ret)?;
		} else {
			write!(f, "() -> {} {{\n", self.ret)?;
		}

		for block in 0..self.blocks.len() {
			write!(f, "bb{block}:\n")?;

			for stmt in &self.blocks[block] {
				write!(f, "\t{stmt}")?;
			}
		}

		write!(f, "}}\n\n")
	}
}

impl Display for CIRStmt {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CIRStmt::Expression(expr) => write!(f, "{expr};\n"),
			CIRStmt::Assignment(lval, expr) => write!(f, "let {lval} = {expr};\n"),
			CIRStmt::Jump(block) => write!(f, "jmp {block};\n"),
			CIRStmt::Branch(cond, a, b) => write!(f, "branch {cond}, {a}, {b};\n"),

			CIRStmt::Return(expr_opt) => {
				if let Some(expr) = expr_opt {
					write!(f, "ret {expr};\n")
				} else {
					write!(f, "ret;\n")
				}
			}
		}
	}
}

impl Display for RValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			RValue::Atom(ty, op_opt, value) => {
				if let Some(op) = op_opt {
					write!(f, "{op} {ty} {value}")
				} else {
					write!(f, "{ty} {value}")
				}
			}

			RValue::Cons([(lhs_ty, lhs), (rhs_ty, rhs)], op) => {
				write!(f, "({lhs_ty} {lhs} {op} {rhs_ty} {rhs})")
			}

			RValue::Cast(ty, value) => {
				write!(f, "{value} as {ty}")
			}
		}
	}
}

impl Display for LValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "%{}", self.local)?;

		for proj in &self.projection {
			match proj {
				PlaceElem::Deref => write!(f, "*"),
				PlaceElem::Field(i) => write!(f, ".{i}"),
				PlaceElem::Index(i) => write!(f, "[{i}]"),
			}?;
		}
		Ok(())
	}
}

impl Display for Operand {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Operand::IntegerLit(num) => write!(f, "{num}"),
			Operand::FloatLit(num) => write!(f, "{num}"),
			Operand::StringLit(s) => write!(f, "\"{s}\""),
			Operand::BoolLit(b) => write!(f, "{b}"),
			Operand::LValue(lval) => write!(f, "{lval}"),

			Operand::FnCall(name, args) => {
				write!(f, "call {name}(")?;
			
				if !args.is_empty() {
					write!(f, "{}", args[0])?;
					
					for i in 1..args.len() {
						write!(f, ", {}", args[i])?;
					}
				}
			
				write!(f, ")")
			}
		}
	}
}

impl Display for CIRType {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CIRType::Basic(b) => write!(f, "{}", b.as_str()),
			CIRType::Pointer(p) => write!(f, "{p}*"),
			CIRType::Array(_, _) => todo!(),
			CIRType::Reference(r) => write!(f, "{r}&"),
			CIRType::TypeRef(idx) => write!(f, "${idx}"),
		}
	}
}

impl Display for CIRTypeDef {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CIRTypeDef::Algebraic {
				members,
				variants,
				layout,
				..
			} => {
				write!(f, "ty layout({layout}) {{\n")?;

				for var in variants {
					write!(f, "\tvariant {var}\n")?;
				}

				for mem in members {
					write!(f, "\tmember {mem},\n")?;
				}

				write!(f, "}}\n\n")
			}
		}
	}
}

impl Display for DataLayout {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			match self {
				DataLayout::Declared => "@decl",
				DataLayout::Optimized => "@opt",
				DataLayout::Packed => "@pack",
			}
		)
	}
}
