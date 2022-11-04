use colored::Colorize;
use std::{
	ffi::OsString,
	fmt::Display,
	sync::{
		atomic::{AtomicU32, Ordering},
		mpsc::{self, Sender},
		Arc,
	},
	thread,
};

use backtrace::Backtrace;
use lazy_static::lazy_static;

use super::types::Type;
use crate::{
	cir::analyze::borrowck::LivenessState,
	parser::Parser,
	semantic::{ast::TokenData, expression::Operator, namespace::Identifier},
};

lazy_static! {
	pub(crate) static ref ERROR_COUNT: Arc<AtomicU32> = Arc::new(AtomicU32::new(0));
}

#[derive(Debug, Clone)]
pub struct CMNError {
	pub code: CMNErrorCode,
	pub origin: Backtrace,
	pub notes: Vec<(Option<TokenData>, String)>,
}

impl CMNError {
	pub fn new(code: CMNErrorCode) -> Self {
		ERROR_COUNT.fetch_add(1, Ordering::Relaxed);
		CMNError {
			code,
			origin: Backtrace::new(),
			notes: vec![],
		}
	}

	pub fn with_note(mut self, note: String, location: Option<TokenData>) -> Self {
		self.notes.push((location, note));
		self
	}

	pub fn new_with_parser(code: CMNErrorCode, _parser: &Parser) -> Self {
		ERROR_COUNT.fetch_add(1, Ordering::Relaxed);
		CMNError {
			code,
			origin: Backtrace::new(),
			notes: vec![],
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
	AssignTypeMismatch {
		expr: Type,
		to: Type,
	},
	InvalidCast {
		from: Type,
		to: Type,
	},
	InvalidCoercion {
		from: Type,
		to: Type,
	},
	InvalidMemberAccess {
		t: Type,
		idx: String,
	},
	InvalidSubscriptLHS {
		t: Type,
	},
	InvalidSubscriptRHS {
		t: Type,
	},
	InvalidLValue,
	ReturnTypeMismatch {
		expected: Type,
		got: Type,
	},
	ParamCountMismatch {
		expected: usize,
		got: usize,
	},
	NotCallable(String),
	InvalidDeref(Type),
	InfiniteSizeType,

	// Resolution errors
	ModuleNotFound(OsString),

	// Code generation errors
	LLVMError,

	// Borrowck errors
	InvalidUse {
		variable: Identifier,
		state: LivenessState,
	},

	// Packaged-up collection of errors as a single Err
	Pack(Vec<CMNError>),

	// Misc
	Custom(String),
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

			CMNErrorCode::UndeclaredIdentifier(id) => write!(f, "undeclared identifier `{id}`"),
			CMNErrorCode::UnresolvedTypename(id) => write!(f, "unresolved typename `{id}`"),
			CMNErrorCode::ExprTypeMismatch(a, b, op) => write!(
				f,
				"type mismatch; cannot apply operator {op:?} to {a} and {b}"
			),
			CMNErrorCode::AssignTypeMismatch { expr, to } => write!(
				f,
				"cannot assign value of type {expr} to variable of type {to}"
			),
			CMNErrorCode::InvalidCast { from, to } => {
				write!(f, "cannot cast from {} to {}", from, to)
			}
			CMNErrorCode::InvalidCoercion { from, to } => {
				write!(f, "cannot coerce from {} to {}", from, to)
			}
			CMNErrorCode::InvalidLValue => write!(f, "invalid lvalue"),
			CMNErrorCode::InvalidSubscriptLHS { t } => write!(f, "can't index into type {t}"),
			CMNErrorCode::InvalidSubscriptRHS { t } => {
				write!(f, "can't index into array with index type {t}")
			}
			CMNErrorCode::ReturnTypeMismatch { expected, got } => {
				write!(f, "return type mismatch; expected {expected}, got {got}")
			}
			CMNErrorCode::ParamCountMismatch { expected, got } => write!(
				f,
				"parameter count mismatch; expected {expected}, got {got}",
			),
			CMNErrorCode::InvalidMemberAccess { t, idx } => {
				write!(f, "variable of type {t} has no member '{idx}'")
			}
			CMNErrorCode::NotCallable(id) => write!(f, "{id} is not callable"),
			CMNErrorCode::InvalidDeref(ty) => write!(f, "can't dereference value of type {ty}"),
			CMNErrorCode::InfiniteSizeType => write!(f, "cyclical type dependency found"),

			CMNErrorCode::ModuleNotFound(m) => {
				write!(f, "module not found: {}", m.to_string_lossy())
			}

			CMNErrorCode::LLVMError => write!(f, "an internal compiler error occurred"),

			CMNErrorCode::InvalidUse { variable, state } => {
				write!(
					f,
					"use of {} variable {variable}",
					match state {
						LivenessState::Uninit => "uninitialized",
						LivenessState::Live => "live (how did you trigger this error??)",
						LivenessState::Moved => "moved",
						LivenessState::PartialMoved => "partially-moved",
						LivenessState::Dropped => "dropped",
					}
				)
			}

			CMNErrorCode::Pack(vec) => write!(f, "encountered {} errors", vec.len()),

			CMNErrorCode::Custom(text) => write!(f, "{text}"),
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
	pub fn get_notes(&self) -> &Vec<(Option<TokenData>, String)> {
		match self {
			CMNMessage::Error(e) => &e.notes,
			CMNMessage::Warning(_) => todo!(), // CMNError and CMNWarning are probably gonna get merged into one enum
		}
	}
}

pub enum CMNMessageLog {
	Annotated {
		msg: CMNMessage,
		filename: String,

		line_text: String,
		line: usize,
		column: usize,
		length: usize,
	},

	Plain {
		msg: CMNMessage,
		filename: String,
	},

	Raw(String),
}

pub fn spawn_logger(backtrace_on_error: bool) -> Sender<CMNMessageLog> {
	let (sender, receiver) = mpsc::channel::<CMNMessageLog>();

	thread::spawn(move || {
		loop {
			match receiver.recv() {
				Ok(CMNMessageLog::Raw(text)) => print!("{}", text),

				Ok(message) => {
					let (msg, filename) = match &message {
						CMNMessageLog::Annotated { msg, filename, .. }
						| CMNMessageLog::Plain { msg, filename, .. } => (msg, filename),
						_ => panic!(),
					};

					// Print message
					match msg {
						CMNMessage::Error(_) => {
							print!("\n{}: {}", "error".bold().red(), msg.to_string().bold());
						}
						CMNMessage::Warning(_) => {
							print!(
								"\n{}: {}",
								"warning".bold().yellow(),
								msg.to_string().bold()
							)
						}
					}

					// Print file:row:column
					match &message {
						CMNMessageLog::Annotated {
							line,
							column,
							line_text,
							length,
							..
						} => {
							println!(
								"{}",
								format!(" in {}:{}:{}\n", filename, line + 1, column)
									.bright_black()
							);

							// Print code snippet
							println!(
								"{} {}",
								format!("{}\t{}", line + 1, "|").bright_black(),
								line_text
							);

							// Print squiggle
							print!("\t{: <1$}", "", column + 1);
							println!("{:~<1$}", "", length);
						}

						CMNMessageLog::Plain { .. } => {
							println!("{}", format!(" in {}", filename,).bright_black())
						}

						_ => panic!(),
					}

					let notes = msg.get_notes();

					for note in notes {
						println!("{} {}\n", "note:".bold().italic(), note.1.italic());
					}

					// Print compiler backtrace
					if let CMNMessage::Error(err) = &msg {
						if backtrace_on_error {
							println!("\ncompiler backtrace:\n\n{:?}", err.origin);
						}
					}
				}

				// All channels closed
				Err(_) => break,
			}
		}
	});

	sender
}