use std::{
	ffi::OsString,
	fmt::Display,
	sync::{
		atomic::{AtomicU32, Ordering},
		Arc,
	},
};

use backtrace::Backtrace;
use lazy_static::lazy_static;

use super::types::Type;
use crate::{parser::Parser, semantic::expression::Operator};

lazy_static! {
	pub(crate) static ref ERROR_COUNT: Arc<AtomicU32> = Arc::new(AtomicU32::new(0));
}

#[derive(Debug, Clone)]
pub struct CMNError {
	pub code: CMNErrorCode,
	origin: Backtrace,
}

impl CMNError {
	pub fn new(code: CMNErrorCode) -> Self {
		ERROR_COUNT.fetch_add(1, Ordering::Relaxed);
		CMNError {
			code,
			origin: Backtrace::new(),
		}
	}

	pub fn new_with_parser(code: CMNErrorCode, _parser: &Parser) -> Self {
		ERROR_COUNT.fetch_add(1, Ordering::Relaxed);
		CMNError {
			code,
			origin: Backtrace::new(),
		}
	}
}

#[derive(Debug, Clone)]
pub enum CMNMessage {
	Error(CMNError),
	Warning(CMNWarning),
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum CMNErrorCode {
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
	AssignTypeMismatch { expr: Type, to: Type },
	InvalidCast { from: Type, to: Type },
	InvalidCoercion { from: Type, to: Type },
	InvalidMemberAccess { t: Type, idx: String },
	InvalidLValue,
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
			CMNMessage::Error(e) => e.code.fmt(f),
			CMNMessage::Warning(w) => w.fmt(f),
		}
	}
}

impl Display for CMNErrorCode {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			CMNErrorCode::OK => write!(f, "ok (how did you trigger this error???)"),
			CMNErrorCode::UnexpectedEOF => write!(f, "unexpected end of file"),
			CMNErrorCode::UnexpectedToken => write!(f, "unexpected token"),
			CMNErrorCode::UnexpectedKeyword => write!(f, "unexpected keyword"),
			CMNErrorCode::ExpectedIdentifier => write!(f, "expected identifier"),
			CMNErrorCode::InvalidSuffix => write!(f, "invalid suffix"),

			CMNErrorCode::UndeclaredIdentifier(id) => write!(f, "undeclared identifier `{}`", id),
			CMNErrorCode::UnresolvedTypename(id) => write!(f, "unresolved typename `{}`", id),
			CMNErrorCode::ExprTypeMismatch(a, b, op) => write!(
				f,
				"type mismatch; cannot apply operator {:?} to {} and {}",
				op, a, b
			),
			CMNErrorCode::AssignTypeMismatch { expr, to } => write!(
				f,
				"cannot assign value of type {} to variable of type {}",
				expr, to
			),
			CMNErrorCode::InvalidCast { from, to } => {
				write!(f, "cannot cast from {} to {}", from, to)
			}
			CMNErrorCode::InvalidCoercion { from, to } => {
				write!(f, "cannot coerce from {} to {}", from, to)
			}
			CMNErrorCode::InvalidLValue => write!(f, "invalid lvalue"),
			CMNErrorCode::ReturnTypeMismatch { expected, got } => write!(
				f,
				"return type mismatch; expected {}, got {}",
				expected, got
			),
			CMNErrorCode::ParamCountMismatch { expected, got } => write!(
				f,
				"parameter count mismatch; expected {}, got {}",
				expected, got
			),
			CMNErrorCode::InvalidMemberAccess { t, idx } => {
				write!(f, "variable of type {} has no member '{}'", t, idx)
			}
			CMNErrorCode::NotCallable(id) => write!(f, "{} is not callable", id),
			CMNErrorCode::NonPtrDeref => write!(f, "attempt to dereference a non-pointer value"),
			CMNErrorCode::InfiniteSizeType => write!(f, "cyclical type dependency found"),

			CMNErrorCode::ModuleNotFound(m) => {
				write!(f, "module not found: {}", m.to_string_lossy())
			}

			CMNErrorCode::LLVMError => write!(f, "an internal compiler error occurred"),

			CMNErrorCode::Unimplemented => write!(f, "not yet implemented"),
			CMNErrorCode::Other => write!(f, "an unknown error occurred"),
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
			CMNMessage::Error(e) => e.code.get_notes(),
			CMNMessage::Warning(w) => w.get_notes(),
		}
	}
}

impl CMNErrorCode {
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
