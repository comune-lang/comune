use colored::Colorize;
use std::io::Write;
use std::ops::RangeInclusive;
use std::{
	fmt::Display,
	io,
	sync::{
		atomic::AtomicU32,
		mpsc::{self, Sender},
		Arc,
	},
	thread,
};

use backtrace::Backtrace;
use lazy_static::lazy_static;

use crate::ast::module::Name;
use crate::ast::types::Type;
use crate::ast::types::{FnPrototype, GenericArgs};
use crate::ast::write_arg_list;
use crate::lexer::SrcSpan;
use crate::{
	ast::{expression::Operator, module::Identifier},
	cir::analyze::lifeline::LivenessState,
};

lazy_static! {
	pub static ref ERROR_COUNT: Arc<AtomicU32> = Arc::new(AtomicU32::new(0));
}

pub static mut CAPTURE_BACKTRACE: bool = false;

#[derive(Debug, Clone)]
pub struct ComuneError {
	pub code: ComuneErrCode,
	pub span: SrcSpan,
	pub origin: Option<Backtrace>,
	pub notes: Vec<(SrcSpan, String)>,
}

impl ComuneError {
	pub fn new(code: ComuneErrCode, span: SrcSpan) -> Self {
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

	pub fn with_note(mut self, note: String, location: SrcSpan) -> Self {
		self.notes.push((location, note));
		self
	}
}

#[derive(Debug, Clone)]
pub enum ComuneMessage {
	Error(ComuneError),
	Warning(ComuneWarning),
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

	RightShiftInGenericArgs(Option<Type>, Option<GenericArgs>),

	// Semantic errors
	UndeclaredIdentifier(String),
	UnresolvedTypename(String),
	UnsupportedInference,
	ExprTypeMismatch(Type, Type, Operator),
	AssignTypeMismatch {
		expr: Type,
		to: Type,
	},
	MatchTypeMismatch {
		scrutinee: Type,
		branch: Type,
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
		generic_args: GenericArgs,
	},
	MissingInitializers {
		ty: Type,
		members: Vec<Name>,
	},
	UnresolvedTrait(Identifier),
	UninitReference,
	UninitNewReference,
	UninitMutReference,
	LocalNewReference,
	LoopCtrlOutsideLoop(&'static str),
	UnsafeOperation,
	UnsafeCall(Arc<FnPrototype>),
	DSTWithoutIndirection,
	TraitFunctionMismatch,
	MissingTraitFuncImpl(String),
	CtorSelfParam(Identifier),
	DtorSelfParam(Identifier),
	DtorDefOverlap,
	AlreadyDefined(Identifier),
	UnsupportedConstExpr,
	InvalidLifetimeName,

	// Resolution errors
	ModuleNotFound(Identifier),
	DependencyError,

	// Code generation errors
	BackendError,

	// Borrowck errors
	InvalidUse {
		variable: Identifier,
		state: LivenessState,
	},

	InvalidNewReference {
		variable: Identifier,
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
pub enum ComuneWarning {
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
		use ComuneErrCode::*;

		match self {
			OK => write!(f, "ok (how did you trigger this error???)"),

			AlreadyDefined(name) => write!(f, "conflicting definitions of `{name}`"),
			AmbiguousCall => write!(f, "ambiguous call"),

			AssignTypeMismatch { expr, to } => {
				write!(
					f,
					"cannot assign value of type `{expr}` to variable of type `{to}`"
				)
			}

			BackendError => write!(f, "an internal compiler error occurred"),

			CtorSelfParam(id) => write!(f, "constructor of `{id}` must take a `new& self` parameter"),
			DependencyError => write!(f, "a dependency failed to compile"),
			DSTWithoutIndirection => write!(f, "dynamically-sized type without indirection"),
			DtorDefOverlap => write!(f, "overlapping definitions of `drop`"),
			DtorSelfParam(id) => write!(f, "destructor of `{id}` must take a `mut& self` parameter"),
			ExpectedIdentifier => write!(f, "expected identifier"),
			InvalidSuffix => write!(f, "invalid suffix"),

			RightShiftInGenericArgs(..) => {
				write!(
					f,
					"`>>` in generic argument list interpreted as right shift operator"
				)
			}

			ExprTypeMismatch(a, b, op) => write!(
				f,
				"type mismatch; cannot apply operator {op:?} to `{a}` and `{b}`"
			),

			ImmutVarMutation { variable } => {
				write!(
					f,
					"cannot mutate `{variable}`, as it is not declared as mutable"
				)
			}

			InfiniteSizeType => write!(f, "cyclical type dependency found"),
			InvalidCast { from, to } => write!(f, "cannot cast from `{from}` to `{to}`"),
			InvalidCoercion { from, to } => write!(f, "cannot coerce from `{from}` to `{to}`"),
			InvalidDeref(ty) => write!(f, "can't dereference value of type `{ty}`"),
			InvalidLifetimeName => write!(f, "invalid lifetime name"),
			InvalidLValue => write!(f, "invalid lvalue"),
			InvalidMemberAccess { t, idx } => write!(f, "no such member `{idx}` on type `{t}`"),
			InvalidSubscriptLHS { t } => write!(f, "can't index into type `{t}`"),
			InvalidSubscriptRHS { t } => write!(f, "can't index with value of type `{t}`"),

			InvalidUse { variable, state } => {
				write!(
					f,
					"use of {} variable `{variable}`",
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

			InvalidNewReference { variable } => {
				write!(
					f,
					"variable `{variable}` must be uninitialized to pass as new&"
				)
			}

			LocalNewReference => write!(f, "new& is only allowed in function parameters"),
			LoopCtrlOutsideLoop(name) => write!(f, "{name} outside of loop"),
			
			MatchTypeMismatch { scrutinee, branch } => {
				write!(
					f,
					"branch type `{branch}` is not a subtype of matched type `{scrutinee}`"
				)
			}

			MissingInitializers { ty, members } => {
				let mut iter = members.iter();
				write!(
					f,
					"missing initializers for type `{ty}`: {}",
					iter.next().unwrap()
				)?;

				for member in iter {
					write!(f, ", {member}")?;
				}

				Ok(())
			}

			MissingTraitFuncImpl(name) => write!(f, "missing implementation for function `{name}`"),

			ModuleNotFound(m) => write!(f, "module not found: {m:#?}"),
			NotCallable(id) => write!(f, "`{id}` is not callable"),
			NoCandidateFound {
				name,
				args,
				generic_args,
			} => {
				write!(f, "no viable overload found for `{name}`")?;

				if !generic_args.is_empty() {
					write_arg_list!(f, generic_args, "<", ">");
				}

				write_arg_list!(f, args, "(", ")");
				Ok(())
			}

			ParamCountMismatch { expected, got } => write!(
				f,
				"parameter count mismatch; expected `{expected}`, got `{got}`",
			),
			
			ReturnTypeMismatch { expected, got } => {
				write!(
					f,
					"return type mismatch; expected `{expected}`, got `{got}`"
				)
			}

			TraitFunctionMismatch => write!(f, "function signature does not match trait definition"),

			UndeclaredIdentifier(id) => write!(f, "`{id}` was not found in this scope"),
			UnexpectedEOF => write!(f, "unexpected end of file"),
			UnexpectedToken => write!(f, "unexpected token"),
			UnexpectedKeyword => write!(f, "unexpected keyword"),
			UninitReference => write!(f, "reference binding must be immediately initialized"),
			
			UninitNewReference => {
				write!(
					f,
					"new& binding must be initialized in all control flow paths"
				)
			}
			
			UninitMutReference => {
				write!(
					f,
					"moved-from mut& binding must be re-initialized in all control flow paths"
				)
			}

			UnresolvedTypename(id) => write!(f, "unresolved typename `{id}`"),
			UnstableFeature(feat) => write!(f, "feature `{feat}` is unstable"),
			UnresolvedTrait(tr) => write!(f, "failed to resolve trait `{tr}`"),
			UnsafeOperation => write!(f, "unsafe operation outside `unsafe` context"),
			UnsafeCall(call) => write!(f, "unsafe call to `{call}` outside `unsafe` context"),
			UnsupportedInference => write!(f, "`auto` in this position is not supported"),
			UnsupportedConstExpr => write!(f, "unsupported constant expression"),

			Pack(vec) => write!(f, "encountered {} errors", vec.len()),
			Custom(text) => write!(f, "{text}"),
			Unimplemented => write!(f, "not yet implemented"),
			Other => write!(f, "an unknown error occurred"),
		}
	}
}

impl Display for ComuneWarning {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			ComuneWarning::OK => write!(f, "nothing wrong here!"),
			ComuneWarning::CharPtrNoNull => write!(
				f,
				"string literal being coerced into a `char*` has no terminating null character"
			),
		}
	}
}

impl ComuneMessage {
	pub fn get_notes(&self) -> &Vec<(SrcSpan, String)> {
		match self {
			ComuneMessage::Error(e) => &e.notes,
			ComuneMessage::Warning(_) => todo!(),
		}
	}
}

pub enum MessageLog {
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

pub fn spawn_logger(backtrace_on_error: bool) -> Sender<MessageLog> {
	let (sender, receiver) = mpsc::channel::<MessageLog>();

	thread::spawn(move || {
		loop {
			match receiver.recv() {
				Ok(MessageLog::Raw(text)) => print!("{}", text),

				Ok(message) => {
					let (msg, filename) = match &message {
						MessageLog::Annotated { msg, filename, .. }
						| MessageLog::Plain { msg, filename, .. } => (msg, filename),
						_ => panic!(),
					};

					let mut out = io::stderr().lock();

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
						MessageLog::Annotated {
							lines,
							column,
							lines_text,
							length,
							..
						} => {
							writeln!(
								out,
								"{}",
								format!(" - in {}:{}:{}\n", filename, lines.start() + 1, column)
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
										if let Some(first) =
											line_text.chars().position(|c| c != ' ')
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
									len = usize::min(column + length - 1, line_text.len()) - column
										+ 1;
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
									writeln!(out, "{}", format!("{:~<1$}", "", len).red(),)
										.unwrap();
								}

								if length_left == 0 {
									break;
								}
							}
						}

						MessageLog::Plain { .. } => {
							writeln!(out, "{}", format!(" - in {}\n", filename).bright_black())
								.unwrap();
						}

						_ => panic!(),
					}

					let notes = msg.get_notes();

					for note in notes {
						writeln!(out, "{} {}\n", "note:".bold(), note.1).unwrap();
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
