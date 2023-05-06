use std::fmt::{Display, Write};

use crate::{ast::types::DataLayout, lexer};

use super::{
	CIRCallId, CIRFunction, CIRModule, CIRStmt, LValue, Operand, PlaceElem, RValue,
};

impl Display for CIRModule {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for (name, ty) in &self.types {
			let ty = &*ty.read().unwrap();
			write!(f, "type {name} {ty}")?;
		}

		for (proto, func) in &self.functions {
			write!(f, "fn {proto}{func}")?;
		}

		Ok(())
	}
}

impl Display for CIRFunction {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if self.is_extern {
			writeln!(f, ";\n")
		} else {
			writeln!(f, " {{")?;

			for (i, (ty, props, name)) in self.variables.iter().enumerate() {
				if let Some(name) = name {
					writeln!(f, "\tlet _{i}: {ty}{props}; ({name})")?;
				} else {
					writeln!(f, "\tlet _{i}: {ty}{props};")?;
				}
			}

			for idx in 0..self.blocks.len() {
				let block = &self.blocks[idx];

				writeln!(
					f,
					"\nbb{idx}:\t\t\t\t\t\t\t\t\t\t\t; preds: {:?}, succs: {:?}",
					block.preds, block.succs
				)?;

				for stmt in &block.items {
					write!(f, "\t{stmt}")?;
				}
			}

			writeln!(f, "}}\n")
		}
	}
}

impl Display for CIRStmt {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CIRStmt::Expression(expr) => writeln!(f, "{expr};"),
			CIRStmt::Assignment(lval, expr) => writeln!(f, "{lval} = {expr};"),
			CIRStmt::Jump(block) => writeln!(f, "jmp bb{block};"),
			CIRStmt::Switch(expr, branches, else_branch) => {
				writeln!(f, "switch {expr} {{")?;

				for (ty, val, branch) in branches {
					writeln!(f, "\t\t{val}:{ty} => bb{branch},")?;
				}

				writeln!(f, "\t\telse => bb{else_branch},\n\t}}")
			}

			CIRStmt::Return => writeln!(f, "ret;"),

			CIRStmt::Call {
				id,
				args,
				generic_args,
				result,
			} => {
				if let Some(result) = result {
					write!(f, "{result} = ")?;
				}

				write!(f, "call {id} with")?;

				if !generic_args.is_empty() {
					let mut args_iter = generic_args.iter();

					write!(f, "<{}", args_iter.next().unwrap())?;

					for arg in args_iter {
						write!(f, ", {arg}")?;
					}

					write!(f, ">")?;
				}

				if !args.is_empty() {
					let mut args_iter = args.iter();
					write!(f, "({}", args_iter.next().unwrap().0)?;

					for (arg, _) in args_iter {
						write!(f, ", {arg}")?;
					}

					writeln!(f, ");")
				} else {
					writeln!(f, "();")
				}
			}

			CIRStmt::Invoke {
				id,
				args,
				generic_args,
				result,
				next,
				except,
			} => {
				if let Some(result) = result {
					write!(f, "{result} = ")?;
				}

				write!(f, "invoke {id} with")?;

				if !generic_args.is_empty() {
					let mut args_iter = generic_args.iter();

					write!(f, "<{}", args_iter.next().unwrap())?;

					for arg in args_iter {
						write!(f, ", {arg}")?;
					}

					write!(f, ">")?;
				}

				if !args.is_empty() {
					let mut args_iter = args.iter();
					write!(f, "({}", args_iter.next().unwrap().0)?;

					for (arg, _) in args_iter {
						write!(f, ", {arg}")?;
					}

					write!(f, ")")?;
				} else {
					write!(f, "()")?;
				}

				writeln!(f, " => [bb{next}, bb{except}];")
			}

			CIRStmt::StorageLive(var) => write!(f, "StorageLive(_{var});\n"),
			CIRStmt::StorageDead(var) => write!(f, "StorageDead(_{var});\n"),
			CIRStmt::DropShim { var, next } => write!(f, "drop {var} => bb{next};\n"),
		}
	}
}

impl Display for RValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			RValue::Atom(ty, op_opt, value, _) => {
				if let Some(op) = op_opt {
					write!(f, "{op} {ty} {value}")
				} else {
					write!(f, "{ty} {value}")
				}
			}

			RValue::Cons(expr_ty, [(lhs_ty, lhs), (rhs_ty, rhs)], op, _) => {
				write!(f, "{expr_ty} ({lhs_ty} {lhs} {op} {rhs_ty} {rhs})")
			}

			RValue::Cast {
				from, to, val: op, ..
			} => {
				write!(f, "{from} {op} as {to}")
			}
		}
	}
}

impl Display for LValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut result = String::new();

		write!(&mut result, "_{}", self.local)?;

		for proj in &self.projection {
			match proj {
				PlaceElem::Deref => {
					result.insert(0, '*');
					result.insert(1, '(');
					result.push(')');
				}
				PlaceElem::Field(i) => {
					write!(&mut result, ".{i}")?;
				}
				PlaceElem::Index(t, i, _) => {
					write!(&mut result, "[{t} {i}]")?;
				}
			};
		}

		write!(f, "{result}")
	}
}

impl Display for Operand {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Operand::IntegerLit(num, _) => write!(f, "{num}"),
			Operand::FloatLit(num, _) => write!(f, "{num}"),
			Operand::StringLit(s, _) => {
				write!(f, "\"{}\"", lexer::get_unescaped(s))
			}
			Operand::CStringLit(s, _) => {
				write!(f, "{s:#?}")
			}
			Operand::BoolLit(b, _) => write!(f, "{b}"),
			Operand::Move(lval) => write!(f, "move {lval}"),
			Operand::Copy(lval) => write!(f, "copy {lval}"),
			Operand::Borrow(lval, props) => write!(f, "borrow {lval} as {props}"),
			Operand::Undef => write!(f, "undef"),
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

impl Display for CIRCallId {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CIRCallId::Direct(id, _) => write!(f, "{id}"),
			CIRCallId::Indirect {
				local, ret, args, ..
			} => {
				write!(f, "{ret}(")?;

				if !args.is_empty() {
					let mut iter = args.iter();
					let (ty, _, props) = iter.next().unwrap();

					write!(f, "{props}{ty}")?;

					for (ty, _, props) in iter {
						write!(f, ", {ty}{props}")?;
					}
				}

				write!(f, "){local}")
			}
		}
	}
}
