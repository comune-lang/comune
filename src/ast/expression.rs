use std::{
	ffi::CString,
	fmt::Display,
	ptr,
	sync::{Arc, RwLock, Weak},
};

use crate::{
	errors::{ComuneErrCode, ComuneError},
	lexer::SrcSpan,
	parser::ComuneResult,
};

use super::{
	controlflow::ControlFlow,
	module::{Identifier, Name},
	statement::Stmt,
	types::{Basic, FnPrototype, Type, TypeDef},
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
	pub tk: SrcSpan,
}

impl NodeData {
	pub fn new() -> Self {
		NodeData {
			ty: None,
			tk: SrcSpan::new(),
		}
	}
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

	pub fn try_wrap_in_cast(&mut self, to: Type) -> ComuneResult<()> {
		if self.get_type() == &to {
			return Ok(());
		}

		if !self.get_type().castable_to(&to) {
			return Err(ComuneError::new(
				ComuneErrCode::CastTypeMismatch {
					from: self.get_type().clone(),
					to,
				},
				self.get_span(),
			));
		}

		self.wrap_in_cast(to);

		Ok(())
	}

	pub fn get_type(&self) -> &Type {
		self.get_node_data()
			.ty
			.as_ref()
			.expect("attempting to unwrap an unvalidated Expr's type!")
	}

	pub fn get_span(&self) -> SrcSpan {
		self.get_node_data().tk
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

#[derive(Clone, Debug)]
pub enum Atom {
	Block {
		items: Vec<Stmt>,
		result: Option<Box<Expr>>,
		is_unsafe: bool,
	},

	CtrlFlow(Box<ControlFlow>),

	// Basic literals
	IntegerLit(i128, Option<Basic>),
	FloatLit(f64, Option<Basic>),
	BoolLit(bool),
	StringLit(String),
	CStringLit(CString),

	// Advanced literals
	ArrayLit(Vec<Expr>),
	//AlgebraicLit(Type, Vec<(Name, Expr)>),
	Identifier(Identifier),

	Cast(Box<Expr>, Type),

	FnCall {
		name: Identifier,
		args: Vec<Expr>,
		generic_args: Vec<Type>,
		resolved: FnRef,
	},

	// Constructor call
	Constructor {
		def: Weak<RwLock<TypeDef>>,
		generic_args: Vec<Type>,
		kind: XtorKind,
		placement: Option<Box<Expr>>,
	},

	// Drop shim
	Drop(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq)]
pub enum XtorKind {
	Literal { fields: Vec<(Name, Expr)> },

	Constructor { args: Vec<Expr>, resolved: FnRef },
}

#[derive(Clone, Debug)]
pub enum FnRef {
	None,
	Direct(Arc<RwLock<FnPrototype>>),
	Indirect(Box<Expr>),
}

impl PartialEq for Atom {
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(
				Self::Block {
					items: l0,
					result: l1,
					is_unsafe: l2,
				},
				Self::Block {
					items: r0,
					result: r1,
					is_unsafe: r2,
				},
			) => l0 == r0 && l1 == r1 && l2 == r2,
			(Self::CtrlFlow(l0), Self::CtrlFlow(r0)) => l0 == r0,
			(Self::IntegerLit(l0, l1), Self::IntegerLit(r0, r1)) => l0 == r0 && l1 == r1,
			(Self::FloatLit(l0, l1), Self::FloatLit(r0, r1)) => l0 == r0 && l1 == r1,
			(Self::BoolLit(l0), Self::BoolLit(r0)) => l0 == r0,
			(Self::StringLit(l0), Self::StringLit(r0)) => l0 == r0,
			(Self::CStringLit(l0), Self::CStringLit(r0)) => l0 == r0,
			(Self::ArrayLit(l0), Self::ArrayLit(r0)) => l0 == r0,
			(Self::Identifier(l0), Self::Identifier(r0)) => l0 == r0,
			(Self::Cast(l0, l1), Self::Cast(r0, r1)) => l0 == r0 && l1 == r1,

			(
				Self::Constructor {
					def: l0,
					kind: l1,
					generic_args: l2,
					placement: l3,
				},
				Self::Constructor {
					def: r0,
					kind: r1,
					generic_args: r2,
					placement: r3,
				},
			) => {
				Arc::ptr_eq(&l0.upgrade().unwrap(), &r0.upgrade().unwrap())
					&& l1 == r1 && l2 == r2
					&& l3 == r3
			}

			(
				Self::FnCall {
					name: l_name,
					args: l_args,
					generic_args: l_type_args,
					resolved: l_res,
				},
				Self::FnCall {
					name: r_name,
					args: r_args,
					generic_args: r_type_args,
					resolved: r_res,
				},
			) => {
				l_name == r_name && l_args == r_args && l_type_args == r_type_args && l_res == r_res
			}

			// you don't want to know how much this shit's bitten me in the ass.
			_ => {
				if std::mem::discriminant(self) == std::mem::discriminant(other) {
					panic!("unimplemented PartialEq variant for Expr!")
				} else {
					false
				}
			}
		}
	}
}

impl PartialEq for FnRef {
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(FnRef::Direct(l), FnRef::Direct(r)) => &*l.read().unwrap() == &*r.read().unwrap(),
			(FnRef::Indirect(l0), FnRef::Indirect(r0)) => l0 == r0,
			(FnRef::None, FnRef::None) => true,
			_ => false,
		}
	}
}

impl Display for Atom {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Atom::IntegerLit(i, _) => write!(f, "{}", i),

			Atom::FloatLit(fl, _) => write!(f, "{}", fl),

			Atom::StringLit(s) => write!(f, "\"{}\"", s.escape_default()),

			Atom::CStringLit(s) => write!(f, "{s:#?}"),

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

			Atom::Block {
				items,
				result,
				is_unsafe,
			} => {
				if *is_unsafe {
					write!(f, "unsafe ")?;
				}

				writeln!(f, "{{")?;

				for item in items {
					writeln!(f, "\t{item};")?
				}

				if let Some(result) = result {
					writeln!(f, "\t{result}")?
				}

				writeln!(f, "}}")
			}

			_ => writeln!(f, "(display unimplemented: {self:?})"),
		}
	}
}
