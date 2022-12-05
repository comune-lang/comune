use crate::{
	parser::AnalyzeResult,
	ast::{
		expression::{Atom, Expr, Operator},
		types::Basic,
		FnScope,
	},
};

// Constant expression evaluation module. For stuff like array lengths, generics, you get the idea

#[derive(Clone, Debug, PartialEq)]
pub enum ConstExpr {
	Expr(Expr),
	Result(ConstValue),
}

// This might be up for extension later on, but as it stands having the most basic types oughta do the trick

#[derive(Clone, Debug, PartialEq)]
pub enum ConstValue {
	Integral(i128, Option<Basic>),
	Float(f64, Option<Basic>),
	Bool(bool),
}

pub trait ConstEval {
	fn eval_const(&self, scope: &FnScope) -> AnalyzeResult<ConstValue>;
}

impl ConstEval for Expr {
	fn eval_const(&self, scope: &FnScope) -> AnalyzeResult<ConstValue> {
		match self {
			Expr::Atom(a, _) => a.eval_const(scope),

			Expr::Unary(a, op, _) => {
				match a.eval_const(scope)? {
					// Unary operators
					ConstValue::Integral(i, b) => match op {
						Operator::UnaryMinus => Ok(ConstValue::Integral(-i, b)),
						Operator::UnaryPlus => Ok(ConstValue::Integral(i, b)),
						_ => todo!(),
					},

					ConstValue::Float(f, b) => match op {
						Operator::UnaryMinus => Ok(ConstValue::Float(-f, b)),
						Operator::UnaryPlus => Ok(ConstValue::Float(f, b)),
						_ => todo!()
					},

					ConstValue::Bool(b) => {
						if *op == Operator::LogicNot {
							return Ok(ConstValue::Bool(!b));
						}
						todo!();
					}
				}
			}

			Expr::Cons([lhs, rhs], op, _) => {
				let lhs = lhs.eval_const(scope)?;
				let rhs = rhs.eval_const(scope)?;

				match lhs {
					ConstValue::Integral(i_lhs, b) => {
						let combined_b = b; // TODO: Actually decide how this is inferred

						if let ConstValue::Integral(i_rhs, _) = rhs {
							Ok(match op {
								Operator::Add => ConstValue::Integral(i_lhs + i_rhs, combined_b),
								Operator::Sub => ConstValue::Integral(i_lhs - i_rhs, combined_b),
								Operator::Mul => ConstValue::Integral(i_lhs * i_rhs, combined_b),
								Operator::Div => ConstValue::Integral(i_lhs / i_rhs, combined_b),

								Operator::BitShiftL => {
									ConstValue::Integral(i_lhs << i_rhs, combined_b)
								}
								Operator::BitShiftR => {
									ConstValue::Integral(i_lhs >> i_rhs, combined_b)
								}
								Operator::BitXOR => ConstValue::Integral(i_lhs ^ i_rhs, combined_b),
								Operator::BitAND => ConstValue::Integral(i_lhs & i_rhs, combined_b),
								Operator::BitOR => ConstValue::Integral(i_lhs | i_rhs, combined_b),

								Operator::Greater => ConstValue::Bool(i_lhs > i_rhs),
								Operator::GreaterEq => ConstValue::Bool(i_lhs >= i_rhs),
								Operator::Less => ConstValue::Bool(i_lhs < i_rhs),
								Operator::LessEq => ConstValue::Bool(i_lhs <= i_rhs),
								Operator::Eq => ConstValue::Bool(i_lhs == i_rhs),
								Operator::NotEq => ConstValue::Bool(i_lhs != i_rhs),

								_ => panic!(),
							})
						} else {
							panic!()
						}
					}

					ConstValue::Float(f_lhs, b) => {
						let combined_b = b; // TODO: Actually decide how this is inferred

						if let ConstValue::Float(f_rhs, _) = rhs {
							Ok(match op {
								Operator::Add => ConstValue::Float(f_lhs + f_rhs, combined_b),
								Operator::Sub => ConstValue::Float(f_lhs - f_rhs, combined_b),
								Operator::Mul => ConstValue::Float(f_lhs * f_rhs, combined_b),
								Operator::Div => ConstValue::Float(f_lhs / f_rhs, combined_b),

								Operator::Greater => ConstValue::Bool(f_lhs > f_rhs),
								Operator::GreaterEq => ConstValue::Bool(f_lhs >= f_rhs),
								Operator::Less => ConstValue::Bool(f_lhs < f_rhs),
								Operator::LessEq => ConstValue::Bool(f_lhs <= f_rhs),
								Operator::Eq => ConstValue::Bool(f_lhs == f_rhs),
								Operator::NotEq => ConstValue::Bool(f_lhs != f_rhs),

								_ => panic!(),
							})
						} else {
							panic!()
						}
					}

					ConstValue::Bool(b_lhs) => {
						if let ConstValue::Bool(b_rhs) = rhs {
							Ok(match op {
								Operator::LogicAnd => ConstValue::Bool(b_lhs && b_rhs),
								Operator::LogicOr => ConstValue::Bool(b_lhs || b_rhs),

								_ => panic!(),
							})
						} else {
							panic!()
						}
					}
				}
			}
		}
	}
}

impl ConstEval for Atom {
	fn eval_const(&self, _scope: &FnScope) -> AnalyzeResult<ConstValue> {
		match self {
			Atom::IntegerLit(i, b) => Ok(ConstValue::Integral(*i, *b)),
			Atom::FloatLit(f, b) => Ok(ConstValue::Float(*f, *b)),
			Atom::BoolLit(b) => Ok(ConstValue::Bool(*b)),

			_ => todo!(),
		}
	}
}
