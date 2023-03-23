use colored::Colorize;
use std::io::Write;
use std::ops::RangeInclusive;
use std::{
	ffi::OsString,
	fmt::Display,
	io,
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
use crate::ast::module::Name;
use crate::lexer::SrcSpan;
use crate::{
	ast::{expression::Operator, module::Identifier},
	cir::analyze::lifeline::LivenessState,
};

lazy_static! {
	pub(crate) static ref ERROR_COUNT: Arc<AtomicU32> = Arc::new(AtomicU32::new(0));
}

pub(crate) static mut CAPTURE_BACKTRACE: bool = false;

#[derive(Debug, Clone)]
pub struct ComuneError {
	pub code: ComuneErrCode,
	pub span: SrcSpan,
	pub origin: Option<Backtrace>,
	pub notes: Vec<(Option<SrcSpan>, String)>,
}

impl ComuneError {
	pub fn new(code: ComuneErrCode, span: SrcSpan) -> Self {
		ERROR_COUNT.fetch_add(1, Ordering::Relaxed);
		ComuneError {
			code,
			span,
			notes: vec![],

			// Safety: CAPTURE_BACKTRACE is set before compilation begins.
			origin: if unsafe { CAPTURE_BACKTRACE } {
				Some(Backtrace::new())
			} else {
				None
			},
		}
	}

	pub fn with_note(mut self, note: String, location: Option<SrcSpan>) -> Self {
		self.notes.push((location, note));
		self
	}
}

#[derive(Debug, Clone)]
pub enum ComuneMessage {
	Error(ComuneError),
	Warning(CMNWarning),
}

#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum ComuneErrCode {
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
	AmbiguousCall,
	NotCallable(String),
	InvalidDeref(Type),
	InfiniteSizeType,
	UnstableFeature(&'static str),
	NoCandidateFound {
		name: Identifier,
		args: Vec<Type>,
		type_args: Vec<Type>,
	},
	MissingInitializers {
		ty: Type,
		members: Vec<Name>,
	},
	UnresolvedTrait(Identifier),

	LoopCtrlOutsideLoop(&'static str),
	UnsafeOperation,

	// Resolution errors
	ModuleNotFound(OsString),
	DependencyError,

	// Code generation errors
	LLVMError,

	// Borrowck errors
	InvalidUse {
		variable: Identifier,
		state: LivenessState,
	},

	ImmutVarMutation {
		variable: Identifier,
	},

	// Packaged-up collection of errors as a single Err
	Pack(Vec<ComuneError>),

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

impl Display for ComuneMessage {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			ComuneMessage::Error(e) => e.code.fmt(f),
			ComuneMessage::Warning(w) => w.fmt(f),
		}
	}
}

impl Display for ComuneErrCode {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			ComuneErrCode::OK => write!(f, "ok (how did you trigger this error???)"),
			ComuneErrCode::UnexpectedEOF => write!(f, "unexpected end of file"),
			ComuneErrCode::UnexpectedToken => write!(f, "unexpected token"),
			ComuneErrCode::UnexpectedKeyword => write!(f, "unexpected keyword"),
			ComuneErrCode::ExpectedIdentifier => write!(f, "expected identifier"),
			ComuneErrCode::InvalidSuffix => write!(f, "invalid suffix"),

			ComuneErrCode::UndeclaredIdentifier(id) => {
				write!(f, "`{id}` was not found in this scope")
			}
			ComuneErrCode::UnresolvedTypename(id) => write!(f, "unresolved typename `{id}`"),
			ComuneErrCode::ExprTypeMismatch(a, b, op) => write!(
				f,
				"type mismatch; cannot apply operator {op:?} to {a} and {b}"
			),
			ComuneErrCode::AssignTypeMismatch { expr, to } => write!(
				f,
				"cannot assign value of type {expr} to variable of type {to}"
			),
			ComuneErrCode::InvalidCast { from, to } => {
				write!(f, "cannot cast from {} to {}", from, to)
			}
			ComuneErrCode::InvalidCoercion { from, to } => {
				write!(f, "cannot coerce from {} to {}", from, to)
			}
			ComuneErrCode::InvalidLValue => write!(f, "invalid lvalue"),
			ComuneErrCode::InvalidSubscriptLHS { t } => write!(f, "can't index into type {t}"),
			ComuneErrCode::InvalidSubscriptRHS { t } => {
				write!(f, "can't index into array with index type {t}")
			}
			ComuneErrCode::ReturnTypeMismatch { expected, got } => {
				write!(f, "return type mismatch; expected {expected}, got {got}")
			}
			ComuneErrCode::ParamCountMismatch { expected, got } => write!(
				f,
				"parameter count mismatch; expected {expected}, got {got}",
			),
			ComuneErrCode::InvalidMemberAccess { t, idx } => {
				write!(f, "variable of type {t} has no member '{idx}'")
			}
			ComuneErrCode::NotCallable(id) => write!(f, "{id} is not callable"),
			ComuneErrCode::InvalidDeref(ty) => write!(f, "can't dereference value of type {ty}"),
			ComuneErrCode::InfiniteSizeType => write!(f, "cyclical type dependency found"),
			ComuneErrCode::UnstableFeature(feat) => write!(f, "feature `{feat}` is unstable"),
			ComuneErrCode::NoCandidateFound {
				name,
				args,
				type_args,
			} => {
				write!(f, "no viable overload found for `{name}`")?;

				if !type_args.is_empty() {
					let mut iter = type_args.iter();
					write!(f, "<{}", iter.next().unwrap())?;
					for arg in iter {
						write!(f, ", {arg}")?;
					}
					write!(f, ">")?;
				}

				write!(f, "(")?;

				if !args.is_empty() {
					let mut iter = args.iter();
					write!(f, "{}", iter.next().unwrap())?;
					for arg in iter {
						write!(f, ", {arg}")?;
					}
				}
				write!(f, ")")
			}

			ComuneErrCode::MissingInitializers { ty, members } => {
				let mut iter = members.iter();
				write!(
					f,
					"missing initializers for type {ty}: {}",
					iter.next().unwrap()
				)?;

				for member in iter {
					write!(f, ", {member}")?;
				}

				Ok(())
			}
			
			ComuneErrCode::UnresolvedTrait(tr) => write!(f, "failed to resolve trait `{tr}`"),

			ComuneErrCode::LoopCtrlOutsideLoop(name) => write!(f, "{name} outside of loop"),

			ComuneErrCode::UnsafeOperation => write!(f, "unsafe operation outside `unsafe` block"),

			ComuneErrCode::ModuleNotFound(m) => write!(f, "module not found: {m:#?}"),
			ComuneErrCode::DependencyError => write!(f, "a dependency failed to compile"),
			ComuneErrCode::LLVMError => write!(f, "an internal compiler error occurred"),

			ComuneErrCode::InvalidUse { variable, state } => {
				write!(
					f,
					"use of {} variable {variable}",
					match state {
						LivenessState::Uninit => "uninitialized",
						LivenessState::Live => "live (how did you trigger this error??)",
						LivenessState::Moved => "moved",
						LivenessState::PartialMoved => "partially-moved",
						LivenessState::Dropped => "dropped",
						LivenessState::MaybeUninit => "potentially uninitialized",
					}
				)
			}

			ComuneErrCode::ImmutVarMutation { variable } => {
				write!(
					f,
					"cannot mutate {variable}, as it is not declared as mutable"
				)
			}

			ComuneErrCode::AmbiguousCall => {
				write!(f, "ambiguous call")
			}

			ComuneErrCode::Pack(vec) => write!(f, "encountered {} errors", vec.len()),

			ComuneErrCode::Custom(text) => write!(f, "{text}"),
			ComuneErrCode::Unimplemented => write!(f, "not yet implemented"),
			ComuneErrCode::Other => write!(f, "an unknown error occurred"),
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

impl ComuneMessage {
	pub fn get_notes(&self) -> &Vec<(Option<SrcSpan>, String)> {
		match self {
			ComuneMessage::Error(e) => &e.notes,
			ComuneMessage::Warning(_) => todo!(), // CMNError and CMNWarning are probably gonna get merged into one enum
		}
	}
}

pub enum CMNMessageLog {
	Annotated {
		msg: ComuneMessage,
		filename: String,

		lines_text: Vec<String>,
		lines: RangeInclusive<usize>,
		column: usize,
		length: usize,
	},

	Plain {
		msg: ComuneMessage,
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

					let mut out = io::stdout().lock();

					// Print message
					match msg {
						ComuneMessage::Error(_) => {
							write!(
								out,
								"\n{}: {}",
								"error".bold().red(),
								msg.to_string().bold()
							)
							.unwrap();
						}
						ComuneMessage::Warning(_) => {
							write!(
								out,
								"\n{}: {}",
								"warning".bold().yellow(),
								msg.to_string().bold()
							)
							.unwrap();
						}
					}

					// Print file:row:column
					match &message {
						CMNMessageLog::Annotated {
							lines,
							column,
							lines_text,
							length,
							..
						} => {
							writeln!(
								out,
								"{}",
								format!(" in {}:{}:{}\n", filename, lines.start() + 1, column)
									.bright_black()
							)
							.unwrap();

							let mut length_left = *length;

							// Print code snippet
							for line in lines.clone() {
								let og_line_text = &lines_text[line - lines.start()];

								// First, convert tabs to spaces and store the display offsets for each character
								let (line_text, offsets) = {
									let mut line_result = String::with_capacity(og_line_text.len());
									let mut current_offset = 0;
									let mut offsets = vec![];

									for c in og_line_text.chars() {
										if c == '\t' {
											line_result.push_str("    ");
											current_offset += 3;
											length_left += 3;
										} else {
											line_result.push(c);
										}

										offsets.push(current_offset);
									}
									(line_result, offsets)
								};

								writeln!(
									out,
									"{} {}",
									format!("{}\t{}", line + 1, "|").bright_black(),
									line_text
								)
								.unwrap();
								
								let column = {
									if line == *lines.start() {
										*column + offsets[*column - 1]
									} else {
										if let Some(first) = line_text.chars().position(|c| c != ' ')
										{
											first + 1
										} else {
											0
										}
									}
								};

								let len;

								// welcome to off-by-one hell. don't touch anything or suffer the consequences

								if line_text.is_empty() {
									// Blank line, skip it
									len = 0;
									length_left -= 1;
								} else if line == *lines.start() {
									// First line
									len = usize::min(column + length - 1, line_text.len()) - column + 1;
									length_left -= len;
								} else if line != *lines.end() {
									// Middle line
									len = line_text.len() - column + 1;
									length_left -= line_text.len() + 1;
								} else {
									// Last line
									len = length_left - column;
								}

								// Print gutter
								write!(out, "{}", format!("\t{}", "|").bright_black()).unwrap();

								if column == 0 {
									// No text on this line, just print a newline
									writeln!(out, "").unwrap();
								} else {
									// Print squiggle

									write!(out, "{: <1$}", "", column).unwrap();
									writeln!(
										out,
										"{}",
										format!("{:~<1$}", "", len).red(),
									)
									.unwrap();
								}

								if length_left == 0 {
									break;
								}
							}
						}

						CMNMessageLog::Plain { .. } => {
							writeln!(out, "{}", format!(" in {}", filename).bright_black())
								.unwrap();
						}

						_ => panic!(),
					}

					let notes = msg.get_notes();

					for note in notes {
						writeln!(out, "{} {}\n", "note:".bold().italic(), note.1.italic()).unwrap();
					}

					// Print compiler backtrace
					if let ComuneMessage::Error(err) = &msg {
						if backtrace_on_error {
							writeln!(
								out,
								"\ncompiler backtrace:\n\n{:?}",
								err.origin.as_ref().unwrap()
							)
							.unwrap();
						}
					}
					out.flush().unwrap();
				}

				// All channels closed
				Err(_) => break,
			}
		}
	});

	sender
}
