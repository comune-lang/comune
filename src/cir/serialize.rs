use std::fmt::{Display, Write};

use crate::{
	ast::{types::DataLayout, write_arg_list},
	lexer,
};

use super::{CIRCallId, CIRFunction, CIRModule, CIRStmt, LValue, Operand, PlaceElem, RValue};

impl Display for CIRModule {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for (name, ty) in &self.types {
			let ty = &*ty.read().unwrap();
			write!(f, "type {name} {ty}")?;
		}

		for (name, (ty, val)) in &self.globals {
			write!(f, "{ty} {name} = {val};\n\n")?;
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

			for scope in self.scopes.iter() {
				write!(f, "\nscope {} ", scope.index)?;
				
				if scope.is_unsafe && scope.is_loop {
					write!(f, "(unsafe, loop) ")?;
				} else if scope.is_unsafe {
					write!(f, "(unsafe) ")?;
				} else if scope.is_loop {
					write!(f, "(loop) ")?;
				}

				write!(f, "{{")?;
				
				let mut empty = true;

				for (name, var) in scope.variables.iter() {
					if let Some(name) = name {
						if empty {
							writeln!(f)?;
							empty = false;
						}
						writeln!(f, "\t{name} := _{var};")?;
						
					}
				}

				writeln!(f, "}}")?;
			}

			for idx in 0..self.blocks.len() {
				let block = &self.blocks[idx];

				writeln!(
					f,
					"\nbb{idx}:\t\t\t\t\t\t\t\t\t\t\t; preds: {:?}, succs: {:?}, scope: {}",
					block.preds, block.succs, block.scope
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
			CIRStmt::Assignment(lval, expr) => writeln!(f, "{lval} = {expr};"),
			CIRStmt::RefInit(local, expr) => writeln!(f, "_{local} := {expr};"),
			CIRStmt::Jump(block) => writeln!(f, "jmp bb{block};"),
			CIRStmt::Switch(expr, branches, else_branch) => {
				writeln!(f, "switch {expr} {{")?;

				for (ty, val, branch) in branches {
					writeln!(f, "\t\t{val}:{ty} => bb{branch},")?;
				}

				writeln!(f, "\t\telse => bb{else_branch},\n\t}}")
			}
			
			CIRStmt::GlobalAccess { local, symbol } => {
				writeln!(f, "{local} := global {symbol};")
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
					write_arg_list!(f, generic_args, "<", ">");
				}

				if !args.is_empty() {
					let mut args_iter = args.iter();
					let first = args_iter.next().unwrap();

					write!(f, "({}{} {}", first.1, first.2, first.0)?;

					for (arg, ty, props) in args_iter {
						write!(f, ", {ty}{props} {arg}")?;
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
					write_arg_list!(f, generic_args, "<", ">");
				}

				if !args.is_empty() {
					let mut args_iter = args.iter();
					let first = args_iter.next().unwrap();

					write!(f, "({}{} {}", first.1, first.2, first.0)?;

					for (arg, ty, props) in args_iter {
						write!(f, ", {ty}{props} {arg}")?;
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
			CIRStmt::Unreachable => write!(f, "unreachable;\n"),
			CIRStmt::SourceLoc(line, column) => write!(f, "sourceloc {line}:{column};"),
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
				PlaceElem::Index { index_ty, index, op } => {
					write!(&mut result, "[{op}{index_ty} {index}]")?;
				}
				PlaceElem::SumData(ty) => {
					result.insert(0, '(');
					write!(&mut result, ": {ty})")?;
				}
				PlaceElem::SumDisc => {
					write!(&mut result, ".sum_disc")?;
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
			Operand::StringLit(s, _) => write!(f, "\"{}\"", lexer::get_unescaped(s)),
			Operand::CStringLit(s, _) => write!(f, "{s:#?}"),
			Operand::BoolLit(b, _) => write!(f, "{b}"),
			Operand::LValueUse(lval, props) => write!(f, "{lval}{props}"),
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
