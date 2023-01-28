use std::fmt::Display;

use crate::{
	ast::types::{DataLayout, TupleKind},
	lexer,
};

use super::{
	CIRFnPrototype, CIRFunction, CIRModule, CIRStmt, CIRType, CIRTypeDef, LValue, Operand,
	PlaceElem, RValue,
};

impl Display for CIRModule {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for (name, ty) in &self.types {
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
			let mut iter = self.type_params.iter();

			write!(f, "<{}", iter.next().unwrap().0)?;

			for (param, traits, ty) in iter {
				write!(f, ", {param}")?;

				if !traits.is_empty() {
					let mut traits_iter = traits.iter();

					write!(f, ": {:?}", traits_iter.next().unwrap())?;

					for tr in traits_iter {
						write!(f, " + {tr:?}")?;
					}

					if let Some(ty) = ty {
						write!(f, " = {ty}")?;
					}
				}
			}

			write!(f, ">")?;
		}

		// Print parameters
		if self.params.is_empty() {
			write!(f, "()")?;
		} else {
			let mut iter = self.params.iter();
			let first = iter.next().unwrap();
			write!(f, "({}{}", first.0, first.1)?;

			for (props, param) in iter {
				write!(f, ", {props}{param}")?;
			}

			write!(f, ")")?;
		}

		write!(f, " -> {}", self.ret)
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
					writeln!(f, "\tlet _{i}: {props}{ty}; ({name})")?;
				} else {
					writeln!(f, "\tlet _{i}: {props}{ty};")?;
				}
			}

			for idx in 0..self.blocks.len() {
				let block = &self.blocks[idx];

				writeln!(
					f,
					"bb{idx}:\t\t\t\t\t\t\t\t\t\t\t; preds: {:?}, succs: {:?}",
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
			CIRStmt::Expression(expr, _) => writeln!(f, "{expr};"),
			CIRStmt::Assignment((lval, _), (expr, _)) => writeln!(f, "{lval} = {expr};"),
			CIRStmt::Jump(block) => writeln!(f, "jmp bb{block};"),
			CIRStmt::Switch(expr, branches, else_branch) => {
				writeln!(f, "switch {expr} {{")?;

				for (ty, val, branch) in branches {
					writeln!(f, "\t\t{val}:{ty} => bb{branch},")?;
				}

				writeln!(f, "\t\telse => bb{else_branch},\n\t}}")
			}

			CIRStmt::Return(expr_opt) => {
				if let Some((expr, _)) = expr_opt {
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
					write!(f, "({}", args_iter.next().unwrap())?;

					for arg in args_iter {
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

			RValue::Cons(expr_ty, [(lhs_ty, lhs), (rhs_ty, rhs)], op) => {
				write!(f, "{expr_ty} ({lhs_ty} {lhs} {op} {rhs_ty} {rhs})")
			}

			RValue::Cast { from, to, val: op } => {
				write!(f, "{from} {op} as {to}")
			}
		}
	}
}

impl Display for LValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "_{}", self.local)?;

		for proj in &self.projection {
			match proj {
				PlaceElem::Deref => write!(f, ">"),
				PlaceElem::Field(i) => write!(f, ".{i}"),
				PlaceElem::Index(i, t) => write!(f, "[{t} {i}]"),
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
			Operand::CStringLit(s) => {
				write!(f, "{s:#?}")
			}
			Operand::BoolLit(b) => write!(f, "{b}"),
			Operand::LValue(lval) => write!(f, "{lval}"),
			Operand::Undef => write!(f, "undef"),
		}
	}
}

impl Display for CIRType {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CIRType::Basic(b) => write!(f, "{}", b.as_str()),
			CIRType::Pointer(p) => write!(f, "{p}*"),
			CIRType::Array(t, _) => write!(f, "{t}[]"),
			CIRType::Reference(r) => write!(f, "{r}&"),
			CIRType::TypeRef(name, _) => write!(f, "{name}"),
			CIRType::TypeParam(idx) => write!(f, "<{idx}>"),

			CIRType::Tuple(kind, types) => {
				if types.is_empty() {
					write!(f, "()")
				} else {
					let mut iter = types.iter();

					write!(f, "({}", iter.next().unwrap())?;

					if kind == &TupleKind::Product {
						for ty in iter {
							write!(f, ", {ty}")?;
						}
					} else {
						for ty in iter {
							write!(f, " | {ty}")?;
						}
					}

					write!(f, ")")
				}
			}
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
				type_params,
				..
			} => {
				writeln!(f, "layout({layout}) {{")?;

				for (param, ..) in type_params {
					writeln!(f, "\tparam {param:?}")?;
				}

				for var in variants {
					writeln!(f, "\tvariant {var}")?;
				}

				for mem in members {
					writeln!(f, "\tmember {mem},")?;
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
