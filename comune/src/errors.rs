use std::{ffi::OsString, fmt::Display};

use super::types::Type;
use crate::semantic::expression::Operator;

#[derive(Debug, Clone)]
pub enum CMNMessage {
	Error(CMNError),
	Warning(CMNWarning),
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum CMNError {
	// Not really used in Results but i don't want an error code 0
	OK,

	// Syntactic errors
	UnexpectedEOF,
	UnexpectedToken,
	UnexpectedKeyword,
	ExpectedIdentifier,
	InvalidSuffix,

	// Semantic errors
	UndeclaredIdentifier(String),
	UnresolvedTypename(String),
	ExprTypeMismatch(Type, Type, Operator),
	AssignTypeMismatch(Type, Type),
	InvalidCast { from: Type, to: Type },
	InvalidCoercion { from: Type, to: Type },
	InvalidMemberAccess { t: Type, idx: String },
	ReturnTypeMismatch { expected: Type, got: Type },
	ParamCountMismatch { expected: usize, got: usize },
	NotCallable(String),
	NonPtrDeref,
	InfiniteSizeType,

	// Resolution errors
	ModuleNotFound(OsString),

	// Code generation errors
	LLVMError,

	// Misc
	Unimplemented,
	Other,
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum CMNWarning {
	OK,

	CharPtrNoNull,
}

impl Display for CMNMessage {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CMNMessage::Error(e) => e.fmt(f),
			CMNMessage::Warning(w) => w.fmt(f),
		}
	}
}

impl Display for CMNError {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CMNError::OK => write!(f, "ok (how did you trigger this error???)"),
			CMNError::UnexpectedEOF => write!(f, "unexpected end of file"),
			CMNError::UnexpectedToken => write!(f, "unexpected token"),
			CMNError::UnexpectedKeyword => write!(f, "unexpected keyword"),
			CMNError::ExpectedIdentifier => write!(f, "expected identifier"),
			CMNError::InvalidSuffix => write!(f, "invalid suffix"),

			CMNError::UndeclaredIdentifier(id) => write!(f, "undeclared identifier `{}`", id),
			CMNError::UnresolvedTypename(id) => write!(f, "unresolved typename `{}`", id),
			CMNError::ExprTypeMismatch(a, b, op) => write!(
				f,
				"type mismatch; cannot apply operator {:?} to {} and {}",
				op, a, b
			),
			CMNError::AssignTypeMismatch(e, v) => write!(
				f,
				"cannot assign value of type {} to variable of type {}",
				e, v
			),
			CMNError::InvalidCast { from, to } => write!(f, "cannot cast from {} to {}", from, to),
			CMNError::InvalidCoercion { from, to } => {
				write!(f, "cannot coerce from {} to {}", from, to)
			}
			CMNError::ReturnTypeMismatch { expected, got } => write!(
				f,
				"return type mismatch; expected {}, got {}",
				expected, got
			),
			CMNError::ParamCountMismatch { expected, got } => write!(
				f,
				"parameter count mismatch; expected {}, got {}",
				expected, got
			),
			CMNError::InvalidMemberAccess { t, idx } => {
				write!(f, "variable of type {} has no member '{}'", t, idx)
			}
			CMNError::NotCallable(id) => write!(f, "{} is not callable", id),
			CMNError::NonPtrDeref => write!(f, "attempt to dereference a non-pointer value"),
			CMNError::InfiniteSizeType => write!(f, "cyclical type dependency found"),

			CMNError::ModuleNotFound(m) => write!(f, "module not found: {}", m.to_string_lossy()),

			CMNError::LLVMError => write!(f, "an internal compiler error occurred"),

			CMNError::Unimplemented => write!(f, "not yet implemented"),
			CMNError::Other => write!(f, "an unknown error occurred"),
		}
	}
}

impl Display for CMNWarning {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CMNWarning::OK => write!(f, "nothing wrong here!"),
			CMNWarning::CharPtrNoNull => write!(
				f,
				"string literal being coerced into a `char*` has no terminating null character"
			),
		}
	}
}

impl CMNMessage {
	pub fn get_notes(&self) -> Vec<String> {
		match self {
			CMNMessage::Error(e) => e.get_notes(),
			CMNMessage::Warning(w) => w.get_notes(),
		}
	}
}

impl CMNError {
	pub fn get_notes(&self) -> Vec<String> {
		match self {
			_ => vec![],
		}
	}
}

impl CMNWarning {
	pub fn get_notes(&self) -> Vec<String> {
		match self {
			CMNWarning::OK => vec!["(how did you trigger this warning???)".into()],

			CMNWarning::CharPtrNoNull => vec![
				"strings passed to C/C++ functions should end with '\\0'".into(),
				"if you're the author of this function, consider taking a `str` parameter instead"
					.into(),
			],
			//_ => vec![],
		}
	}
}
