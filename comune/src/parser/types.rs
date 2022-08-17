use std::{fmt::Display, collections::HashMap};

use once_cell::sync::OnceCell;

use super::ast::ASTElem;
use super::lexer::Token;

use super::namespace::Identifier;
use super::semantic::Attribute;
use super::{semantic::FnScope, ASTResult};

type BoxedType = Box<Type>;

pub type FnParamList = Vec<(Box<Type>, Option<String>)>;


pub(crate) static PTR_SIZE_BYTES: OnceCell<u32> = OnceCell::new();


pub trait Typed {
	fn get_type<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> ASTResult<Type>;
}


#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Basic {
	I64,
	U64,
	I32,
	U32,
	I16,
	U16,
	I8,
	U8,
	CHAR,
	F64,
	F32,
	ISIZE,
	USIZE,
	BOOL,
	VOID,
	STR,
}

impl Basic {
	pub fn get_basic_type(name: &str) -> Option<Self> {
		match name {
			// Concrete names
			"i64" =>	Some(Basic::I64),
			"u64" =>	Some(Basic::U64),
			"i32" =>	Some(Basic::I32),
			"u32" =>	Some(Basic::U32),
			"i16" =>	Some(Basic::I16),
			"u16" =>	Some(Basic::U16),
			"i8" =>		Some(Basic::I8),
			"u8" =>		Some(Basic::U8),
			"char" =>	Some(Basic::CHAR),
			"str" =>	Some(Basic::STR),
			"f64" =>	Some(Basic::F64),
			"f32" =>	Some(Basic::F32),
			"isize" =>	Some(Basic::ISIZE),
			"usize" =>	Some(Basic::USIZE),
			"bool" =>	Some(Basic::BOOL),
			"void" =>	Some(Basic::VOID),
			
			// Friendly names
			"int" =>		Some(Basic::I32),
			"uint" =>		Some(Basic::U32),
			"float" =>		Some(Basic::F32),
			"double" =>		Some(Basic::F64),
			
			_ => None,
		}
	}

	pub fn as_str(&self) -> &'static str {
		match self {
			Basic::I64 => "i64",
			Basic::U64 => "u64",
			Basic::I32 => "i32",
			Basic::U32 => "u32",
			Basic::I16 => "i16",
			Basic::U16 => "u16",
			Basic::I8 => "i8",
			Basic::U8 => "u8",
			Basic::CHAR => "char",
			Basic::STR => "str",
			Basic::F64 => "f64",
			Basic::F32 => "f32",
			Basic::ISIZE => "isize",
			Basic::USIZE => "usize",
			Basic::BOOL => "bool",
			Basic::VOID => "void",
		}
	}
}

impl Display for Basic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}


#[derive(Debug, Clone, PartialEq)]
pub enum Type {
	Basic(Basic),											// Fundamental type
	Alias(String, BoxedType),								// Identifier + referenced type
	Aggregate(Box<AggregateType>),							// Guess.
	Pointer(BoxedType),										// Pointer-to-<BoxedType>
	Function(BoxedType, Vec<(BoxedType, Option<String>)>),	// Return type + parameter types
	Unresolved(Identifier)									// Unresolved type (during parsing phase)
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self {
			Type::Basic(t) => {
				write!(f, "{}", t)?;
			},

			Type::Alias(a, t) => {
				write!(f, "{} ({})", a, t)?;
			},

			Type::Aggregate(agg) => {
				write!(f, "{:?}", agg)?;
			},

			Type::Pointer(t) => {
				write!(f, "{}*", t)?;
			},

			Type::Function(ret, params) => {
				write!(f, "{}(", ret)?;
				for param in params {
					write!(f, "{}, ", param.0)?;
				}
				write!(f, ")")?;
			},

			Type::Unresolved(t) => {
				write!(f, "\"{}\"", t)?;
			},
		}

		Ok(())
    }
}



 
impl Type {

	pub fn ptr_type(&self) -> Self {
		Type::Pointer(Box::new(self.clone()))
	}

	// Name mangling
	pub fn serialize(&self) -> String {
		let mut result = String::new();
		match &self {
			Type::Basic(b) => {
				// TODO: Shorten
				result.push_str(b.as_str());
			},

			// TODO: Consider if aliased types are equivalent at the ABI stage?
			Type::Alias(_, t) => return t.serialize(),
			
			Type::Aggregate(a) => {
				for t in &a.members {
					result.push_str(&t.1.0.serialize());
				}
			},

			Type::Pointer(t) => {
				result.push_str(&t.serialize());
				result.push_str("*");
			},

			Type::Function(ret, args) => {
				result.push_str("?");
				for arg in args {
					result.push_str(&arg.0.serialize());
				}
				result.push_str("!");
				result.push_str(&ret.serialize());
			},

			Type::Unresolved(_) => { panic!("Attempt to serialize an unresolved type!"); }, // Not supposed to happen Lol
		}
		// TODO: Generics

		result
	}


	pub fn castable_to(&self, target: &Type) -> bool {
		if *self == *target {
			true
		} else {

			if self.is_numeric() {
				if target.is_numeric() || target.is_boolean() {
					return true;
				}
			}
			false
		}
	}


	pub fn is_numeric(&self) -> bool {
		self.is_integral() || self.is_floating_point()
	}


	pub fn is_integral(&self) -> bool {
		match self {
			Type::Basic(b) =>
				match b {
					Basic::ISIZE | Basic::USIZE | 
					Basic::I64 | Basic::U64 | 
					Basic::I32 | Basic::U32 | 
					Basic::I16 | Basic::U16 | 
					Basic::I8 | Basic::U8 | 
					Basic::CHAR => 
						true,
					
					_ => 
						false
				}
			
			_ => false
		}
	}


	pub fn is_boolean(&self) -> bool {
		match self {
			Type::Basic(b) => 
				match b {
					Basic::BOOL => true,
					_ => false,
				}
			_ => false,
		}
	}


	pub fn is_floating_point(&self) -> bool {
		match self {
			Type::Basic(b) =>
				match b {
					Basic::F32 | Basic::F64 => 
						true,
					
					_ => 
						false
				}
			
			_ => false
		}
	}


	pub fn get_size_bytes(&self) -> usize {
		let ptr_size = *PTR_SIZE_BYTES.get().unwrap() as usize;

		match &self {
			Type::Basic(b) => match b {
				Basic::I64 | Basic::U64 | Basic::F64 => 8,
				Basic::I32 | Basic::U32 | Basic::F32 | Basic::CHAR => 4, // Chars in a string are variable-width, lone char is 4 bytes
				Basic::I16 | Basic::U16 => 2,
				Basic::I8 | Basic::U8 => 1,

				// TODO: Actually implement based on target ptr size
				Basic::ISIZE | Basic::USIZE => ptr_size,
				Basic::STR => ptr_size + ptr_size, // sizeof(char*) + sizeof(usize)

				Basic::BOOL => 1,
				Basic::VOID => 0,
				
			},
			
			Type::Alias(_, t) => t.get_size_bytes(),

			Type::Aggregate(ts) => {
				let mut result: usize = 0;

				for t in ts.members.iter() {
					result += t.1.0.get_size_bytes();
				}
				result
			},

			Type::Pointer(_) => ptr_size,
			
			_ => 0,
		}
	}
}

/*


impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self.inner {
			InnerType::Basic(t) => {
				write!(f, "{}", t)?;
			},

			InnerType::Alias(a, t) => {
				write!(f, "{} ({})", a, t)?;
			},

			InnerType::Aggregate(agg) => {
				write!(f, "{:?}", agg)?;
			},

			InnerType::Pointer(t) => {
				write!(f, "{}*", t)?;
			},

			InnerType::Function(ret, params) => {
				write!(f, "{}(", ret)?;
				for param in params {
					write!(f, "{}, ", param.0)?;
				}
				write!(f, ")")?;
			},

			InnerType::Unresolved(t) => {
				write!(f, "\"{}\"", t)?;
			},
		}

		if !self.generics.is_empty() {
			write!(f, "<")?;
			for t in &self.generics {
				write!(f, "{}, ", t)?;
			}
			write!(f, ">")?;
		}

		Ok(())
    }
}
*/

#[derive(Clone, Debug, PartialEq)]
pub struct AggregateType {
	pub members: Vec<(String, (Type, Option<ASTElem>, Visibility))>,
	pub methods: HashMap<String, (Type, Option<ASTElem>, Vec<Attribute>)>,
	pub constructors: Vec<Type>,
	pub destructor: Option<Type>,
	pub inherits: Vec<Type>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Visibility {
	Public,
	Private,
	Protected,
}

impl AggregateType {
	pub fn new() -> Self {
		AggregateType { 
			members: vec![],
			methods: HashMap::new(),
			constructors: vec![],
			destructor: None,
			inherits: vec![],
		}
	}
}