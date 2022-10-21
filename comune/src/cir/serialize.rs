use std::fmt::Display;

use crate::{semantic::types::DataLayout, lexer};

use super::{
	CIRFunction, CIRModule, CIRStmt, CIRType, CIRTypeDef, LValue, Operand, PlaceElem, RValue,
};

impl Display for CIRModule {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for ty in &self.types {
			write!(f, "{ty}")?;
		}

		for func in &self.functions {
			write!(f, "fn {}{}", func.0, func.1 .0)?;
		}

		Ok(())
	}
}

impl Display for CIRFunction {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if self.arg_count > 0 {
			write!(
				f,
				"({}:{}",
				self.variables[0].1.as_ref().unwrap_or(&"_".into()),
				&self.variables[0].0,
			)?;

			for i in 1..self.arg_count {
				write!(
					f,
					", {}:{}",
					self.variables[i].1.as_ref().unwrap_or(&i.to_string().into()),
					&self.variables[i].0
				)?;
			}

			write!(f, ") -> {}", self.ret)?;
		} else {
			write!(f, "() -> {}", self.ret)?;
		}

		if self.is_extern {
			write!(f, ";\n\n")
		} else {
			write!(f, " {{\n")?;

			for i in 0..self.variables.len() {
				if let Some(name) = &self.variables[i].1 {
					write!(f, "\tlet _{i}: {}; ({name})\n", &self.variables[i].0)?;
				} else {
					write!(f, "\tlet _{i}: {};\n", &self.variables[i].0)?;
				}
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
}

impl Display for CIRStmt {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CIRStmt::Expression(expr) => write!(f, "{expr};\n"),
			CIRStmt::Assignment(lval, expr) => write!(f, "{lval} = {expr};\n"),
			CIRStmt::Jump(block) => write!(f, "jmp bb{block};\n"),
			CIRStmt::Branch(cond, a, b) => write!(f, "branch {cond}, bb{a}, bb{b};\n"),

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
					write!(f, "{op} {value}:{ty}")
				} else {
					write!(f, "{value}:{ty}")
				}
			}

			RValue::Cons(expr_ty, [(lhs_ty, lhs), (rhs_ty, rhs)], op) => {
				write!(f, "({lhs}:{lhs_ty} {op} {rhs}:{rhs_ty}):{expr_ty}")
			}

			RValue::Cast { from, to, val: op } => {
				write!(f, "{op}:{from} as {to}")
			}
		}
	}
}

impl Display for LValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "_{}", self.local)?;

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
			Operand::StringLit(s) => {
				write!(f, "\"{}\"", lexer::get_unescaped(s))
			}
			Operand::BoolLit(b) => write!(f, "{b}"),
			Operand::LValue(lval) => write!(f, "{lval}"),
			Operand::Undef => write!(f, "undef"),

			Operand::FnCall(name, args, _) => {
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

			CIRTypeDef::Class {} => todo!(),
		}
	}
}

impl Display for DataLayout {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			match self {
				DataLayout::Declared => "decl",
				DataLayout::Optimized => "opt",
				DataLayout::Packed => "pack",
			}
		)
	}
}
