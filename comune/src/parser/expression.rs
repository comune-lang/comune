use std::{fmt::Display, cell::RefCell};


use crate::lexer;

use super::{types::{Type, Basic, InnerType, Typed}, CMNError, semantic::Scope, ASTResult, ast::{TokenData, ASTElem, ASTNode}, ParseResult, errors::{CMNWarning, CMNMessage}};

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


#[derive(Clone, Debug)]
pub enum Expr {
	Atom(RefCell<Atom>, TokenData),
	Cons(Operator, Vec<Expr>, TokenData)
}


impl Expr {
	pub fn get_type(&self, scope: &Scope, goal_t: &Type, meta: TokenData) -> ASTResult<Type> {
		match self {
			Expr::Atom(a, _) => {
				let a_t = a.borrow().get_type(scope, meta)?;
				
				if a_t != *goal_t {
					if a_t.coercable_to(goal_t) {
						// Atom is coercable to goal_t, so we place it inside a Cast node
						a.borrow().check_cast(&a_t, goal_t, scope, &meta)?;

						let mut swap = Atom::IntegerLit(0); //dummy Atom

						swap = a.replace(swap); // swap now contains old Atom
						
						// Construct a new Atom to cast the containing Atom to the goal type 
						let cast = Atom::Cast(Box::new(
							ASTElem { 
								node: ASTNode::Expression(Expr::Atom(RefCell::new(swap), meta)), 
								type_info: RefCell::new(Some(a_t)), 
								token_data: meta
							}), 
							goal_t.clone()
						);

						a.replace(cast);

						return Ok(goal_t.clone());
					} else {
						return Err((CMNError::TypeMismatch(a_t, goal_t.clone()), meta));
					}
				}

				Ok(a_t)
			},

			// This should probably implement some sort of type coercion ruleset? Works for now though
			Expr::Cons(_, elems, meta) => {
				let mut iter = elems.iter();
				let mut last = iter.next().unwrap().get_type(scope, goal_t, *meta)?;
				
				while let Some(item) = iter.next() {
					let current = item.get_type(scope, goal_t, *meta)?;
					if last != current {
						return Err((CMNError::TypeMismatch(last, current), *meta))
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
			Expr::Atom(tk, _) => write!(f, "{}", tk.borrow()),

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





#[derive(Clone, Debug)]
pub enum Atom {
	IntegerLit(isize),
	BoolLit(bool),
	FloatLit(f64),
	StringLit(String),
	Variable(String),
	ArrayLit(Vec<ASTElem>),
	Cast(Box<ASTElem>, Type),

	FnCall{
		name: String, 
		args: Vec<ASTElem>
	},

	
}



impl Atom {
	fn get_type(&self, scope: &Scope, meta: TokenData) -> ASTResult<Type> {
		match self {
			Atom::IntegerLit(_) => Ok(Type::from_basic(Basic::I32)),
			Atom::FloatLit(_) => Ok(Type::from_basic(Basic::F32)),
			Atom::BoolLit(_) => Ok(Type::from_basic(Basic::BOOL)),
			Atom::StringLit(_) => Ok(Type::from_basic(Basic::STR)),

			Atom::Variable(name) => scope.get_identifier_type(name).ok_or((CMNError::UndeclaredIdentifier(name.clone()), meta)),

			Atom::Cast(_, t) => Ok(t.clone()),

			Atom::FnCall { name, args } => {
				
				if let Some(t) = scope.get_identifier_type(name) {
					if let InnerType::Function(ret, params) = t.inner {

						// Identifier is a function, check parameter types
						if args.len() == params.len() {

							for i in 0..args.len() {
								args[i].type_info.replace(Some(*params[i].0.clone()));
								let arg_type = args[i].get_type(scope)?;
								if !arg_type.coercable_to(params[i].0.as_ref()) {
									return Err((CMNError::TypeMismatch(arg_type, params[i].0.as_ref().clone()), args[i].token_data));
								}
							}
							// All good, return function's return type
							Ok(*ret.clone())

						} else {
							Err((CMNError::ParameterCountMismatch{expected: params.len(), got: args.len()}, meta))
						}
						
					} else {
						Err((CMNError::NotCallable(name.clone()), meta)) // Trying to call a non-function
					}

				} else {
					Err((CMNError::UndeclaredIdentifier(name.clone()), meta)) // Couldn't find symbol!
				}
			},

			Atom::ArrayLit(_) => todo!(),
		}
	}


	// Check if we should issue any warnings or errors when casting
	fn check_cast(&self, from: &Type, to: &Type, scope: &Scope, meta: &TokenData) -> ASTResult<()> {
		match &from.inner {

			InnerType::Basic(b) => match b {

				Basic::STR => {
					if let Atom::StringLit(s) = self {
						if s.chars().last() != Some('\0') {
							lexer::log_msg_at(meta.0, meta.1, CMNMessage::Warning(CMNWarning::CharPtrNoNull));
						}
					}

					Ok(())
				},

				_ => Ok(())
			},

			InnerType::Alias(_, t) => {
				self.check_cast(t.as_ref(), to, scope, meta)
			},
			
			InnerType::Aggregate(_) => todo!(),
			InnerType::Pointer(_) => todo!(),
			InnerType::Function(_, _) => todo!(),
			InnerType::Unresolved(_) => todo!(),
		}
	}
}



impl Display for Atom {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
			Atom::IntegerLit(i) => write!(f, "{}", i),
			
            Atom::FloatLit(fl) => write!(f, "{}", fl),

            Atom::StringLit(s) => write!(f, "{}", s),

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

            Atom::Variable(var) => write!(f, "{}", var),
            Atom::ArrayLit(_elems) => todo!(),
		}
    }
}


