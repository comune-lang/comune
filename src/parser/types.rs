use std::{fmt::Display, collections::HashMap};

use crate::lexer::{Token};

use super::{semantic::Scope, ast::TokenData, ASTResult};

type TypeRef = Box<Type>;

pub type FnParamList = Vec<(Type, Option<String>)>;


pub trait Typed {
	fn get_type(&self, scope: &Scope) -> ASTResult<Type>;
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

	pub fn to_string(&self) -> &'static str {
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
        write!(f, "{}", self.to_string())
    }
}


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InnerType {
	Basic(Basic),						// Fundamental type
	Alias(Token, TypeRef),				// Identifier + referenced type
	Aggregate(HashMap<String, TypeRef>),			// Vector of component types
	Pointer(TypeRef),					// Pretty self-explanatory
	Function(TypeRef, Vec<TypeRef>),	// Return type + parameter types
	Unresolved(Token)					// Unresolved type (during parsing phase)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
	pub inner: InnerType,
	pub generics: Vec<Type>,
	pub is_const: bool,
}

impl Type {
	pub fn new(inner: InnerType, generics: Vec<Type>, is_const: bool) -> Self {
		Type { inner, generics, is_const }
	}
	
	pub fn from_basic(basic: Basic) -> Self {
		Type { inner: InnerType::Basic(basic), generics: vec![], is_const: false }
	}

	pub fn coercable_to(&self, target: &Type) -> bool {
		if *self == *target {
			true
		} else {
			// TODO: Implement
			false
		}
	}

	pub fn castable_to(&self, target: &Type) -> bool {
		if *self == *target {
			true
		} else if self.coercable_to(target) {
			true
		} else {
			// TODO: Implement
			false
		}
	}
}


impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.is_const && !matches!(self.inner, InnerType::Function(_, _)) {
			write!(f, "const ")?;
		}

		match &self.inner {
			InnerType::Basic(t) => {
				write!(f, "{}", t)?;
			},

			InnerType::Alias(a, t) => {
				write!(f, "{} ({})", a, t)?;
			},

			InnerType::Aggregate(types) => {
				write!(f, "{{ ")?;
				for t in types {
					write!(f, "{} {}, ", t.1, t.0)?;
				}
				write!(f, "}}")?;
			},

			InnerType::Pointer(t) => {
				write!(f, "{}*", t)?;
			},

			InnerType::Function(ret, params) => {
				write!(f, "{}(", ret)?;
				for param in params {
					write!(f, "{}, ", param)?;
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