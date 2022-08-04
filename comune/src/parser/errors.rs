use std::{fmt::Display, ffi::OsString};

use super::types::Type;


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

	// Semantic errors
	UndeclaredIdentifier(String),
	TypeMismatch(Type, Type),
	ReturnTypeMismatch{expected: Type, got: Type},
	ParameterCountMismatch{expected: usize, got: usize},
	NotCallable(String),
	NonPtrDeref,

	// Resolution errors
	ModuleNotFound(OsString),

	// Misc
	Unimplemented,
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
			CMNError::OK => 										write!(f, "ok (how did you trigger this error???)"),
			CMNError::UnexpectedEOF => 								write!(f, "unexpected end of file"),
			CMNError::UnexpectedToken => 							write!(f, "unexpected token"),
			CMNError::UnexpectedKeyword => 							write!(f, "unexpected keyword"),
			CMNError::ExpectedIdentifier => 						write!(f, "expected identifier"),
			
			CMNError::UndeclaredIdentifier(id) =>					write!(f, "undeclared identifier `{}`", id),
			CMNError::TypeMismatch(a, b) => 						write!(f, "type mismatch; expected {}, got {}", a, b),
			CMNError::ReturnTypeMismatch { expected, got } =>		write!(f, "return type mismatch; expected {}, got {}", expected, got),
			CMNError::ParameterCountMismatch{ expected, got } =>	write!(f, "parameter count mismatch; expected {}, got {}", expected, got),
			CMNError::NotCallable(id) => 							write!(f, "{} is not callable", id),
			CMNError::NonPtrDeref =>								write!(f, "attempt to dereference a non-pointer value"),

			CMNError::ModuleNotFound(m) =>							write!(f, "module not found: {}", m.to_string_lossy()),
			
			CMNError::Unimplemented =>								write!(f, "not yet implemented"),
    		
		}
	}
}


impl Display for CMNWarning {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CMNWarning::OK => 					write!(f, "nothing wrong here!"),
            CMNWarning::CharPtrNoNull => 		write!(f, "string literal being coerced into a `char*` has no terminating null character"),
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
				"if you're the author of this function, consider taking a `str` parameter instead".into()
				],
				
			//_ => vec![],
		}
	}
}