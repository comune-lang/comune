use std::{fmt::Display, cell::RefCell};

use super::{lexer, types::{Type, Basic, InnerType, Typed}, CMNError, semantic::Scope, ASTResult, ast::{TokenData, ASTElem, ASTNode}, errors::{CMNWarning, CMNMessage}};


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
	
}

impl Operator {

	pub fn get_binding_power(&self) -> u8 {
		match self {
			
			Operator::Call		| Operator::Subscr	| 
			Operator::PostInc	| Operator::PostDec |
			Operator::ScopeRes	| Operator::MemberAccess										=> { 200 }

			
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
	Cons(Operator, Vec<Expr>, TokenData)
}


impl Expr {
	pub fn get_type<'ctx>(&mut self, scope: &'ctx Scope<'ctx>, goal_t: Option<&Type>, meta: TokenData) -> ASTResult<Type> {
		let this_t = match self {
			Expr::Atom(a, _) => {
				a.get_type(scope, meta)?
			},

			// This should probably implement some sort of type coercion ruleset? Works for now though
			Expr::Cons(op, elems, meta) => {
				let mut iter = elems.iter_mut();
				let mut last = iter.next().unwrap().get_type(scope, None, *meta)?;
				
				while let Some(item) = iter.next() {
					let current = item.get_type(scope, None, *meta)?;
					if last != current {
						return Err((CMNError::TypeMismatch(last, current), *meta))
					}
					last = current;
				}

				// Handle operators that change the expression's type here
				match op {
					Operator::Ref => last.ptr_type(),

					Operator::Deref => {
						match last.inner {
							InnerType::Pointer(t) => *t.clone(),
							_ => return Err((CMNError::NonPtrDeref, *meta)),
						}
					}
					_ => last
				}
			}
		};

		if let Some(goal_t) = goal_t {
			if this_t != *goal_t {
				if this_t.coercable_to(goal_t) {
					let meta;

					match self { 
						Expr::Atom(a, m) => {
							// If self is an atom, we perform extra diagnostics for the cast here
							meta = *m;
							a.check_cast(&this_t, goal_t, scope, &meta)?;

						}
						Expr::Cons(_, _, m) => {
							meta = *m;
						}
					}

					let mut swap = Expr::Atom(Atom::IntegerLit(0), meta); //dummy Expr

					swap = std::mem::replace(self, swap); // swap now contains old Atom
					
					// Construct a new Atom to cast the containing Expr to the goal type 
					let cast = Expr::Atom(Atom::Cast(Box::new(
						ASTElem { 
							node: ASTNode::Expression(RefCell::new(swap)), 
							type_info: RefCell::new(Some(this_t)), 
							token_data: meta
						}), 
						goal_t.clone()
					), meta);

					*self = cast;

					return Ok(goal_t.clone());
				} else {
					return Err((CMNError::TypeMismatch(this_t, goal_t.clone()), meta));
				}
			} else {
				return Ok(this_t);
			}
		} else {
			return Ok(this_t);
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
	fn get_type<'ctx>(&self, scope: &'ctx Scope<'ctx>, meta: TokenData) -> ASTResult<Type> {
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

            Atom::Variable(var) => write!(f, "{}", var),
            Atom::ArrayLit(_elems) => todo!(),
		}
    }
}


