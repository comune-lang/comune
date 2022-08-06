use std::fmt::Display;

use super::{types::Type, ast::{TokenData, ASTElem}, namespace::Identifier};


#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Operator {
	Add,
	Sub,
	Mult,
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
	AssMult,
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
			
			Operator::Call		| Operator::Subscr	| 
			Operator::PostInc	| Operator::PostDec |
			Operator::ScopeRes	| Operator::MemberAccess										=> { 200 }
			
			Operator::Cast																		=> { 195 }
			
			Operator::UnaryPlus | Operator::UnaryMinus | Operator::LogicNot | 
			Operator::PreInc	| Operator::PreDec |	
			Operator::Ref		| Operator::Deref												=> { 190 }


			Operator::Mult		| Operator::Div		| Operator::Mod 							=> { 180 }
			
			Operator::Add		| Operator::Sub 												=> { 170 }
			
			Operator::BitShiftL	| Operator::BitShiftR 											=> { 160 }
			
			Operator::Less		| Operator::LessEq	| Operator::Greater	| Operator::GreaterEq	=> { 150 }
			
			Operator::Eq		| Operator::NotEq												=> { 140 }


			Operator::BitAND	=> { 130 }
			Operator::BitXOR	=> { 120 }
			Operator::BitOR		=> { 110 }
			Operator::LogicAnd	=> { 100 }
			Operator::LogicOr	=> { 90 }

			
			Operator::Assign | Operator::AssAdd | Operator::AssSub | Operator::AssMult | Operator::AssDiv | Operator::AssMod | 
			Operator::AssBitShL | Operator::AssBitShR | Operator::AssBitOR | Operator::AssBitXOR | Operator::AssBitAND 
			=> { 80 }

		}
	}

	pub fn is_associative_rtl(&self) -> bool {
		// Kind of a hack for the sake of being at least somewhat concise
		// If the binding power values change, be sure to update these too
		match self.get_binding_power() {
			80 | 190	=> { true }		// Pre-inc/dec, logical not, compound assignment
			_			=> { false }	// All others
		}
	}

	
	pub fn get_operator(token: &str, has_lhs: bool) -> Option<Operator> {
		if has_lhs {
			match token {
				"+" => Some(Operator::Add),
				"-" => Some(Operator::Sub),
				"/" => Some(Operator::Div),
				"*" => Some(Operator::Mult),
				"%" => Some(Operator::Mod),
				"^" => Some(Operator::BitXOR),
				"|" => Some(Operator::BitOR),
				"&" => Some(Operator::BitAND),
				"=" => Some(Operator::Assign),
				"/=" => Some(Operator::AssDiv),
				"*=" => Some(Operator::AssMult),
				"+=" => Some(Operator::AssAdd),
				"-=" => Some(Operator::AssSub),
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


#[derive(Clone, Debug)]
pub enum Expr {
	Atom(Atom, TokenData),
	Cons(Operator, Vec<(Expr, TokenData)>, TokenData)
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
			},
		}
    }
}





#[derive(Clone, Debug)]
pub enum Atom {
	IntegerLit(isize),
	BoolLit(bool),
	FloatLit(f64),
	StringLit(String),
	Identifier(Identifier),
	ArrayLit(Vec<ASTElem>),
	Cast(Box<ASTElem>, Type),

	FnCall{
		name: Identifier, 
		args: Vec<ASTElem>
	},

	
}


impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
			Atom::IntegerLit(i) => write!(f, "{}", i),
			
            Atom::FloatLit(fl) => write!(f, "{}", fl),

            Atom::StringLit(s) => write!(f, "\"{}\"", s.escape_default()),

			Atom::BoolLit(b) => if *b { write!(f, "true") } else { write!(f, "false") }

            Atom::FnCall {name, args} => {
				let mut args_iter = args.iter();
				write!(f, "FnCall:{}(", name)?;
				
				if !args.is_empty() {
					write!(f, "{}", args_iter.next().unwrap())?;
					while let Some(arg) = args_iter.next() {
						write!(f, ", {}", arg)?;
					}
				}
				
				write!(f, ")")
			},

			Atom::Cast(elem, to) => write!(f, "{}({})", to, elem),

            Atom::Identifier(var) => write!(f, "{}", var),
			
            Atom::ArrayLit(_elems) => todo!(),
		}
    }
}


