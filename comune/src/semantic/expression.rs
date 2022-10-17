use std::{cell::RefCell, fmt::Display};

use serde::{Deserialize, Serialize};

use super::{
	ast::{ASTElem, TokenData},
	namespace::Identifier,
	types::{Basic, Type},
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Operator {
	Add,
	Sub,
	Mul,
	Div,
	Mod,

	UnaryPlus,
	UnaryMinus,

	PostInc,
	PostDec,
	PreInc,
	PreDec,

	ScopeRes,
	MemberAccess,
	Call,
	Subscr,
	Ref,
	Deref,

	Eq,
	NotEq,
	Less,
	LessEq,
	Greater,
	GreaterEq,

	// Logical
	LogicAnd,
	LogicOr,
	LogicNot,

	// Bitwise
	BitAND,
	BitXOR,
	BitOR,

	BitShiftL,
	BitShiftR,

	// lol. ass
	// (Compound assignment)
	Assign,
	AssAdd,
	AssSub,
	AssMul,
	AssDiv,
	AssMod,
	AssBitShL,
	AssBitShR,
	AssBitAND,
	AssBitXOR,
	AssBitOR,

	Cast,
}

impl Operator {
	pub fn get_binding_power(&self) -> u8 {
		match self {
			Operator::Call
			| Operator::Subscr
			| Operator::PostInc
			| Operator::PostDec
			| Operator::ScopeRes
			| Operator::MemberAccess => 200,

			Operator::Cast => 195,

			Operator::UnaryPlus
			| Operator::UnaryMinus
			| Operator::LogicNot
			| Operator::PreInc
			| Operator::PreDec
			| Operator::Ref
			| Operator::Deref => 190,

			Operator::Mul | Operator::Div | Operator::Mod => 180,

			Operator::Add | Operator::Sub => 170,

			Operator::BitShiftL | Operator::BitShiftR => 160,

			Operator::Less | Operator::LessEq | Operator::Greater | Operator::GreaterEq => 150,

			Operator::Eq | Operator::NotEq => 140,

			Operator::BitAND => 130,
			Operator::BitXOR => 120,
			Operator::BitOR => 110,
			Operator::LogicAnd => 100,
			Operator::LogicOr => 90,

			Operator::Assign
			| Operator::AssAdd
			| Operator::AssSub
			| Operator::AssMul
			| Operator::AssDiv
			| Operator::AssMod
			| Operator::AssBitShL
			| Operator::AssBitShR
			| Operator::AssBitOR
			| Operator::AssBitXOR
			| Operator::AssBitAND => 80,
		}
	}

	pub fn is_associative_rtl(&self) -> bool {
		// Kind of a hack for the sake of being at least somewhat concise
		// If the binding power values change, be sure to update these too
		match self.get_binding_power() {
			80 | 190 => true, // Pre-inc/dec, logical not, compound assignment
			_ => false,       // All others
		}
	}

	pub fn is_compound_assignment(&self) -> bool {
		match self {
			Operator::AssAdd
			| Operator::AssSub
			| Operator::AssDiv
			| Operator::AssMul
			| Operator::AssBitAND
			| Operator::AssBitOR
			| Operator::AssBitXOR
			| Operator::AssBitShL
			| Operator::AssBitShR => true,

			_ => false,
		}
	}

	pub fn get_compound_operator(&self) -> Self {
		match self {
			Operator::AssAdd => Operator::Add,
			Operator::AssSub => Operator::Sub,
			Operator::AssMul => Operator::Mul,
			Operator::AssDiv => Operator::Div,
			Operator::AssBitAND => Operator::BitAND,
			Operator::AssBitXOR => Operator::BitXOR,
			Operator::AssBitOR => Operator::BitOR,
			Operator::AssBitShL => Operator::AssBitShL,
			Operator::AssBitShR => Operator::AssBitShR,
			_ => panic!(),
		}
	}

	pub fn get_operator(token: &str, has_lhs: bool) -> Option<Operator> {
		if has_lhs {
			match token {
				"+" => Some(Operator::Add),
				"-" => Some(Operator::Sub),
				"/" => Some(Operator::Div),
				"*" => Some(Operator::Mul),
				"%" => Some(Operator::Mod),
				"^" => Some(Operator::BitXOR),
				"|" => Some(Operator::BitOR),
				"&" => Some(Operator::BitAND),

				"=" => Some(Operator::Assign),
				"/=" => Some(Operator::AssDiv),
				"*=" => Some(Operator::AssMul),
				"+=" => Some(Operator::AssAdd),
				"-=" => Some(Operator::AssSub),
				"&=" => Some(Operator::AssBitAND),
				"|=" => Some(Operator::AssBitOR),
				"%=" => Some(Operator::AssMod),
				"^=" => Some(Operator::AssBitXOR),

				"++" => Some(Operator::PostInc),
				"--" => Some(Operator::PostDec),
				"(" => Some(Operator::Call),
				")" => None,
				"[" => Some(Operator::Subscr),
				"]" => None,
				"->" => Some(Operator::MemberAccess),
				"." => Some(Operator::MemberAccess),
				"::" => Some(Operator::ScopeRes),
				"<" => Some(Operator::Less),
				">" => Some(Operator::Greater),
				"||" => Some(Operator::LogicOr),
				"&&" => Some(Operator::LogicAnd),
				"==" => Some(Operator::Eq),
				"<=" => Some(Operator::LessEq),
				">=" => Some(Operator::GreaterEq),
				"!=" => Some(Operator::NotEq),
				"<<" => Some(Operator::BitShiftL),
				">>" => Some(Operator::BitShiftR),
				"as" => Some(Operator::Cast),

				_ => None,
			}
		} else {
			match token {
				"+" => Some(Operator::UnaryPlus),
				"-" => Some(Operator::UnaryMinus),
				"(" => Some(Operator::Call),
				"&" => Some(Operator::Ref),
				"*" => Some(Operator::Deref),
				"!" => Some(Operator::LogicNot),
				"++" => Some(Operator::PreInc),
				"--" => Some(Operator::PreDec),
				_ => None,
			}
		}
	}
}

impl Display for Operator {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			match self {
				Operator::UnaryPlus | Operator::Add => "+",
				Operator::UnaryMinus | Operator::Sub => "-",
				Operator::Mul => "*",
				Operator::Div => "/",
				Operator::Mod => "%",
				Operator::PreInc | Operator::PostInc => "++",
				Operator::PreDec | Operator::PostDec => "--",
				Operator::ScopeRes => "::",
				Operator::MemberAccess => ".",
				Operator::Call => "()",
				Operator::Subscr => "[]",
				Operator::Ref => "&",
				Operator::Deref => "*",
				Operator::Eq => "==",
				Operator::NotEq => "!=",
				Operator::Less => "<",
				Operator::LessEq => "<=",
				Operator::Greater => ">",
				Operator::GreaterEq => ">=",
				Operator::LogicAnd => "&&",
				Operator::LogicOr => "||",
				Operator::LogicNot => "!",
				Operator::BitAND => "&",
				Operator::BitXOR => "^",
				Operator::BitOR => "|",
				Operator::BitShiftL => "<<",
				Operator::BitShiftR => ">>",
				Operator::Assign => "=",
				Operator::AssAdd => "+=",
				Operator::AssSub => "-=",
				Operator::AssMul => "*=",
				Operator::AssDiv => "/=",
				Operator::AssMod => "%=",
				Operator::AssBitShL => "<<=",
				Operator::AssBitShR => ">>=",
				Operator::AssBitAND => "&=",
				Operator::AssBitXOR => "^=",
				Operator::AssBitOR => "|=",
				Operator::Cast => "as",
			}
		)
	}
}

// Expression node
// Cons' Option<Type> field carries extra type data for when the full expression's type isn't sufficient (like when using relational operators)
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
	Atom(Atom, TokenData),
	Cons(Operator, Vec<(Expr, Option<Type>, TokenData)>, TokenData),
}

impl Display for Expr {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Expr::Atom(tk, _) => write!(f, "{}", tk),

			Expr::Cons(op, params, _) => {
				write!(f, "({:?}", op)?;

				for param in params {
					write!(f, " {}", param.0)?;
				}

				write!(f, ")")
			}
		}
	}
}

#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
	IntegerLit(i128, Option<Basic>),
	FloatLit(f64, Option<Basic>),
	BoolLit(bool),
	StringLit(String),
	ArrayLit(Vec<ASTElem>),

	// Struct/enum literal
	AlgebraicLit(Type, Vec<(Option<String>, RefCell<Expr>, TokenData)>),

	Identifier(Identifier),

	Cast(Box<ASTElem>, Type),

	FnCall {
		name: Identifier,
		args: Vec<ASTElem>,
		ret: Option<Type>,
	},
}

impl Display for Atom {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Atom::IntegerLit(i, _) => write!(f, "{}", i),

			Atom::FloatLit(fl, _) => write!(f, "{}", fl),

			Atom::StringLit(s) => write!(f, "\"{}\"", s.escape_default()),

			Atom::BoolLit(b) => {
				if *b {
					write!(f, "true")
				} else {
					write!(f, "false")
				}
			}

			Atom::ArrayLit(_elems) => todo!(),

			Atom::FnCall { name, args, ret } => {
				let mut args_iter = args.iter();
				write!(f, "FnCall:{}(", name)?;

				if !args.is_empty() {
					write!(f, "{}", args_iter.next().unwrap())?;
					while let Some(arg) = args_iter.next() {
						write!(f, ", {}", arg)?;
					}
				}

				write!(f, ")")
			}

			Atom::Cast(elem, to) => write!(f, "{}({})", to, elem),

			Atom::Identifier(var) => write!(f, "{}", var),
			Atom::AlgebraicLit(_, _) => todo!(),
		}
	}
}
