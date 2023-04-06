use std::fmt::{Display, Write};

use crate::{ast::types::DataLayout, lexer};

use super::{
	CIRCallId, CIRFnPrototype, CIRFunction, CIRModule, CIRStmt, LValue, Operand, PlaceElem, RValue,
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

impl Display for CIRFnPrototype {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.name)?;

		// Print type parameters
		if !self.type_params.is_empty() {

			for (i, (param, traits, ty)) in self.type_params.iter().enumerate() {
				if i == 0 {
					write!(f, "<")?;
				} else {
					write!(f, ", ")?;
				}

				write!(f, "{param}")?;

				if !traits.is_empty() {
					let mut traits_iter = traits.iter();

					write!(f, ": {:?}", traits_iter.next().unwrap())?;

					for tr in traits_iter {
						write!(f, " + {tr:?}")?;
					}
				}
				
				if let Some(ty) = ty {
					write!(f, " = {ty}")?;
				}
			}

			write!(f, ">")?;
		}

		// Print parameters
		if self.params.is_empty() {
			write!(f, "()")?;
		} else {
			let mut iter = self.params.iter();
			let (props, param) = iter.next().unwrap();
			write!(f, "({param}{props}")?;

			for (props, param) in iter {
				write!(f, ", {param}{props}")?;
			}

			write!(f, ")")?;
		}

		write!(f, " -> {}{}", self.ret.1, self.ret.0)
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
			CIRStmt::Assignment((lval, _), expr) => writeln!(f, "{lval} = {expr};"),
			CIRStmt::Jump(block) => writeln!(f, "jmp bb{block};"),
			CIRStmt::Switch(expr, branches, else_branch) => {
				writeln!(f, "switch {expr} {{")?;

				for (ty, val, branch) in branches {
					writeln!(f, "\t\t{val}:{ty} => bb{branch},")?;
				}

				writeln!(f, "\t\telse => bb{else_branch},\n\t}}")
			}

			CIRStmt::Return(expr_opt) => {
				if let Some(expr) = expr_opt {
					writeln!(f, "ret {expr};")
				} else {
					writeln!(f, "ret;")
				}
			}
			CIRStmt::FnCall {
				id,
				args,
				type_args,
				result,
				next,
				except,
			} => {
				if let Some(result) = result {
					write!(f, "{result} = ")?;
				}

				write!(f, "call {id} with")?;

				if !type_args.is_empty() {
					let mut args_iter = type_args.iter();

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

				write!(f, " => [bb{next}")?;

				if let Some(except) = except {
					write!(f, ", bb{except}];\n")
				} else {
					write!(f, "];\n")
				}
			}

			CIRStmt::StorageLive(idx) => write!(f, "StorageLive(_{idx});\n"),
			CIRStmt::StorageDead(idx) => write!(f, "StorageDead(_{idx});\n"),
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
				PlaceElem::Offset(t, i, _) => {
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
			Operand::LValue(lval, _) => write!(f, "{lval}"),
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
					let (props, ty) = iter.next().unwrap();

					write!(f, "{props}{ty}")?;

					for (props, ty) in iter {
						write!(f, ", {ty}{props}")?;
					}
				}

				write!(f, "){local}")
			}
		}
	}
}
