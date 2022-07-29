use std::fmt::Display;


use super::{types::{Type, Basic, InnerType, Typed}, ParserError, semantic::Scope, ASTResult, ast::TokenData};

#[derive(Clone, Debug)]
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
	
	Call,
	Subscr,
	
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
	
}

impl Operator {

	pub fn get_binding_power(&self) -> u8 {
		match self {
			Operator::Call		| Operator::Subscr	| Operator::PostInc	| Operator::PostDec 	=> { 200 }
			
			Operator::PreInc	| Operator::PreDec	| Operator::LogicNot | 
			Operator::UnaryPlus | Operator::UnaryMinus											=> { 190 }

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
		
		match token {
			"+" => {
				if !has_lhs {
					Some(Operator::UnaryPlus)
				} else {
					Some(Operator::Add)
				}
			},

			"-" => {
				if !has_lhs {
					Some(Operator::UnaryMinus)
				} else { 
					Some(Operator::Sub) 
				}
			},

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

			"++" => {
				if has_lhs {
					Some(Operator::PostInc)
				} else {
					Some(Operator::PreInc)
				}
			},

			"--" => {
				if has_lhs {
					Some(Operator::PostDec)
				} else {
					Some(Operator::PreDec)
				}
			},


			"(" => Some(Operator::Call),
			")" => None,

			"[" => Some(Operator::Subscr),
			"]" => None,

			"->" => todo!(),
			"." => todo!(),
			"::" => todo!(),

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
			
			_ => None,
		
		}
	}
}




#[derive(Clone)]
pub enum Atom {
	IntegerLit(isize),
	FloatLit(f64),
	StringLit(String),
	Variable(String),
	ArrayLit(Vec<Expr>),

	FnCall{
		name: String, 
		args: Vec<Expr>
	},

	
}


impl Typed for Atom {
	fn get_type(&self, scope: &Scope, meta: TokenData) -> ASTResult<Type> {
		match self {
			Atom::IntegerLit(_) => Ok(Type::from_basic(Basic::I32)),
			Atom::FloatLit(_) => Ok(Type::from_basic(Basic::F32)),
			Atom::StringLit(_) => todo!(),

			Atom::Variable(name) => scope.get_identifier_type(name).ok_or((ParserError::UndeclaredIdentifier(name.clone()), meta)),

			Atom::FnCall { name, args } => {
				
				if let Some(t) = scope.get_identifier_type(name) {
					if let InnerType::Function(ret, params) = t.inner {

						// Identifier is a function, check parameter types
						if args.len() == params.len() {

							for i in 0..args.len() {
								let arg_type = args[i].get_type(scope, meta)?;
								if !arg_type.coercable_to(&params[i]) {
									return Err((ParserError::TypeMismatch(arg_type, *params[i].clone()), args[i].get_meta()));
								}
							}
							// All good, return function's return type
							Ok(*ret.clone())

						} else {
							Err((ParserError::ParameterCountMismatch, meta)) // Wrong number of parameters! 
						}
						
					} else {
						Err((ParserError::NotCallable, meta)) // Trying to call a non-function
					}

				} else {
					Err((ParserError::UndeclaredIdentifier(name.clone()), meta)) // Couldn't find symbol!
				}
			},

			Atom::ArrayLit(_) => todo!(),
		}
	}
}

impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
			Atom::IntegerLit(i) => write!(f, "{}", i),
			
            Atom::FloatLit(fl) => write!(f, "{}", fl),

            Atom::StringLit(s) => write!(f, "{}", s),

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
            Atom::Variable(var) => write!(f, "{}", var),
            Atom::ArrayLit(_elems) => todo!(),
		}
    }
}




#[derive(Clone)]
pub enum Expr {
	Atom(Atom, TokenData),
	Cons(Operator, Vec<Expr>, TokenData)
}


impl Expr {
	pub fn get_meta(&self) -> TokenData {
		match self {
			Expr::Atom(_, tk) => *tk,
			Expr::Cons(_, _, tk) => *tk
		}
	}

}

impl Typed for Expr {
	fn get_type(&self, scope: &Scope, _meta: TokenData) -> ASTResult<Type> {
		match self {
			Expr::Atom(a, _) => a.get_type(scope, self.get_meta()),

			// This should probably implement some sort of type coercion ruleset? Works for now though
			Expr::Cons(_, elems, meta) => {
				let mut iter = elems.iter();
				let mut last = iter.next().unwrap().get_type(scope, *meta)?;
				
				while let Some(item) = iter.next() {
					let current = item.get_type(scope, *meta)?;
					if last != current {
						return Err((ParserError::TypeMismatch(last, current), *meta))
					}
					last = current;
				}
				return Ok(last);
			}
		}
	}
}


impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Expr::Atom(tk, _) => write!(f, "{}", tk),

			Expr::Cons(op, params, _) => {
				write!(f, "({:?}", op)?;

				for param in params {
					write!(f, " {}", param)?;
				}
				
				write!(f, ")")
			},
		}
    }
}


