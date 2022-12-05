use std::{fmt::Display, ptr};

use super::{
	controlflow::ControlFlow,
	namespace::{Identifier, Name},
	statement::Stmt,
	types::{Basic, Type},
	TokenData,
};

#[derive(Clone, Debug, PartialEq, Eq)]
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

			Operator::UnaryPlus
			| Operator::UnaryMinus
			| Operator::LogicNot
			| Operator::PreInc
			| Operator::PreDec
			| Operator::Ref
			| Operator::Deref => 190,

			Operator::Cast => 185,

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
		matches!(
			self,
			Operator::AssAdd
				| Operator::AssSub
				| Operator::AssDiv
				| Operator::AssMul
				| Operator::AssBitAND
				| Operator::AssBitOR
				| Operator::AssBitXOR
				| Operator::AssBitShL
				| Operator::AssBitShR
		)
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

				"<<=" => Some(Operator::AssBitShL),
				">>=" => Some(Operator::AssBitShR),

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

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodeData {
	pub ty: Option<Type>,
	pub tk: TokenData,
}

// Expression node
#[derive(Clone, Debug, PartialEq)]
pub enum Expr {
	Atom(Atom, NodeData),
	Unary(Box<Expr>, Operator, NodeData),
	Cons([Box<Expr>; 2], Operator, NodeData),
}

impl Expr {
	pub fn wrap_in_cast(&mut self, to: Type) {
		if let Expr::Atom(Atom::Cast(_, cast_ty), _) = self {
			if to == *cast_ty {
				return;
			}
		}

		let node_data = self.get_node_data().clone();

		// Swap out self behind a &mut
		unsafe {
			let tmp = ptr::read(self);

			// Technically unsafe if Box::new() panics here,
			// but if you managed to exhaust all the memory
			// in your system, you've got bigger problems.

			let new = Expr::Atom(
				Atom::Cast(Box::new(tmp), to.clone()),
				NodeData {
					ty: Some(to),
					tk: node_data.tk,
				},
			);

			ptr::write(self, new);
		}
	}

	pub fn get_type(&self) -> &Type {
		self.get_node_data().ty.as_ref().unwrap()
	}

	pub fn get_node_data(&self) -> &NodeData {
		match self {
			Expr::Atom(_, data) | Expr::Unary(_, _, data) | Expr::Cons(_, _, data) => data,
		}
	}

	pub fn get_node_data_mut(&mut self) -> &mut NodeData {
		match self {
			Expr::Atom(_, data) | Expr::Unary(_, _, data) | Expr::Cons(_, _, data) => data,
		}
	}

	pub fn wrap_in_block(self) -> Self {
		match self {
			Expr::Atom(Atom::Block { .. }, _) => self,

			_ => {
				let node_data = self.get_node_data().clone();
				Expr::Atom(
					Atom::Block {
						items: vec![],
						result: Some(Box::new(self)),
					},
					node_data,
				)
			}
		}
	}
}

impl Display for Expr {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			// TODO: Display operator is it's Some
			Expr::Atom(tk, _) => write!(f, "{}", tk),

			Expr::Unary(param, op, _) => write!(f, "{op} {param}"),

			Expr::Cons([lhs, rhs], op, _) => write!(f, "({lhs} {op} {rhs})"),
		}
	}
}

#[derive(Clone, Debug, PartialEq)]
pub enum Atom {
	// has_result determines whether the result of the last expression is used as the block's result value
	Block {
		items: Vec<Stmt>,
		result: Option<Box<Expr>>,
	},

	CtrlFlow(Box<ControlFlow>),

	// Basic literals
	IntegerLit(i128, Option<Basic>),
	FloatLit(f64, Option<Basic>),
	BoolLit(bool),
	StringLit(String),

	// Advanced literals
	ArrayLit(Vec<Expr>),
	AlgebraicLit(Type, Vec<(Option<Name>, Expr)>),

	Identifier(Identifier),

	Cast(Box<Expr>, Type),

	FnCall {
		name: Identifier,
		args: Vec<Expr>,
		type_args: Vec<(Name, Type)>,
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

			Atom::FnCall { name, args, .. } => {
				let mut args_iter = args.iter();
				write!(f, "FnCall:{}(", name)?;

				if !args.is_empty() {
					write!(f, "{}", args_iter.next().unwrap())?;
					for arg in args_iter {
						write!(f, ", {}", arg)?;
					}
				}

				write!(f, ")")
			}

			Atom::Cast(elem, to) => write!(f, "{}({})", to, elem),

			Atom::Identifier(var) => write!(f, "{}", var),

			Atom::Block { items, result } => {
				writeln!(f, "{{")?;

				for item in items {
					writeln!(f, "\t{item};")?
				}

				if let Some(result) = result {
					writeln!(f, "\t{result}")?
				}

				writeln!(f, "}}")
			}

			Atom::CtrlFlow(_) => todo!(),

			Atom::AlgebraicLit(_, _) => todo!(),
		}
	}
}
