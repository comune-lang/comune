use colored::{Colorize, ColoredString};
use std::io::Write;
use std::ops::RangeInclusive;
use std::{
	fmt::Display,
	io,
	sync::Arc,
};

use backtrace::Backtrace;

use crate::ast::module::Name;
use crate::ast::traits::TraitRef;
use crate::ast::types::Type;
use crate::ast::types::{FnPrototype, GenericArgs};
use crate::ast::write_arg_list;
use crate::lexer::{SrcSpan, Lexer};
use crate::{
	ast::{expression::Operator, module::Identifier},
	cir::analyze::lifeline::LivenessState,
};

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
	CastTypeMismatch {
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
	UnsatisfiedTraitBounds(Type, Vec<TraitRef>),
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
	DestructureNotExhaustive(Vec<Name>),

	// Resolution errors
	ModuleNotFound(Identifier),
	DependencyError,

	// Code generation errors
	LLVMError,

	// Borrowck errors
	InvalidUse {
		variable: Identifier,
		state: LivenessState,
	},

	InvalidNewRef {
		variable: Identifier,
	},

	InvalidMutRef {
		variable: Identifier,
	},

	ImmutVarMutation {
		variable: Identifier,
	},

	// Packaged-up collection of errors as a single Err
	Pack(Vec<ComuneError>),

	LexerError(String),

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
		match self {
			ComuneErrCode::OK => write!(f, "ok (how did you trigger this error???)"),
			ComuneErrCode::UnexpectedEOF => write!(f, "unexpected end of file"),
			ComuneErrCode::UnexpectedToken => write!(f, "unexpected token"),
			ComuneErrCode::UnexpectedKeyword => write!(f, "unexpected keyword"),
			ComuneErrCode::ExpectedIdentifier => write!(f, "expected identifier"),
			ComuneErrCode::InvalidSuffix => write!(f, "invalid suffix"),
			
			ComuneErrCode::RightShiftInGenericArgs(..) => {
				write!(f, "`>>` in generic argument list interpreted as right shift operator")
			}

			ComuneErrCode::UndeclaredIdentifier(id) => {
				write!(f, "`{id}` was not found in this scope")
			}
			ComuneErrCode::UnresolvedTypename(id) => write!(f, "unresolved typename `{id}`"),
			ComuneErrCode::UnsupportedInference => write!(f, "`auto` in this position is not supported"),
			ComuneErrCode::ExprTypeMismatch(a, b, op) => write!(
				f,
				"type mismatch; cannot apply operator {op:?} to `{a}` and `{b}`"
			),
			ComuneErrCode::AssignTypeMismatch { expr, to } => {
				write!(
					f,
					"cannot assign value of type `{expr}` to variable of type `{to}`"
				)
			}
			ComuneErrCode::MatchTypeMismatch { scrutinee, branch } => {
				write!(
					f,
					"pattern type `{branch}` is not a subtype of matched type `{scrutinee}`"
				)
			}
			ComuneErrCode::CastTypeMismatch { from, to } => {
				write!(f, "cannot cast from `{from}` to `{to}`")
			}
			ComuneErrCode::InvalidCoercion { from, to } => {
				write!(f, "cannot coerce from `{from}` to `{to}`")
			}
			ComuneErrCode::InvalidLValue => write!(f, "invalid lvalue"),
			ComuneErrCode::InvalidSubscriptLHS { t } => write!(f, "can't index into type `{t}`"),
			ComuneErrCode::InvalidSubscriptRHS { t } => {
				write!(f, "can't index into array with index type `{t}`")
			}
			ComuneErrCode::ReturnTypeMismatch { expected, got } => {
				write!(
					f,
					"return type mismatch; expected `{expected}`, got `{got}`"
				)
			}
			ComuneErrCode::ParamCountMismatch { expected, got } => write!(
				f,
				"parameter count mismatch; expected `{expected}`, got `{got}`",
			),
			ComuneErrCode::InvalidMemberAccess { t, idx } => {
				write!(f, "variable of type `{t}` has no member `{idx}`")
			}
			ComuneErrCode::NotCallable(id) => write!(f, "`{id}` is not callable"),
			ComuneErrCode::InvalidDeref(ty) => write!(f, "can't dereference value of type `{ty}`"),
			ComuneErrCode::InfiniteSizeType => write!(f, "cyclical type dependency found"),
			ComuneErrCode::UnstableFeature(feat) => write!(f, "feature `{feat}` is unstable"),
			ComuneErrCode::NoCandidateFound {
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

			ComuneErrCode::MissingInitializers { ty, members } => {
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

			ComuneErrCode::CtorSelfParam(id) => {
				write!(f, "constructor of `{id}` must take a `new& self` parameter")
			}
			ComuneErrCode::DtorSelfParam(id) => {
				write!(f, "destructor of `{id}` must take a `mut& self` parameter")
			}
			ComuneErrCode::DtorDefOverlap => {
				write!(f, "overlapping definitions of `drop`")
			}
			ComuneErrCode::UnresolvedTrait(tr) => write!(f, "failed to resolve trait `{tr}`"),

			ComuneErrCode::UnsatisfiedTraitBounds(ty, traits) => {
				write!(f, "trait bounds not satisfied: `{ty}` does not implement ")?;

				for (i, tr) in traits.iter().enumerate() {
					write!(f, "`{}`", tr.name)?;

					if i != traits.len() - 1 {
						write!(f, "`, `")?;
					}
				}
				
				Ok(())
			}

			ComuneErrCode::UninitReference => {
				write!(f, "a reference binding must be immediately initialized")
			}
			ComuneErrCode::UninitNewReference => {
				write!(
					f,
					"new& binding must be initialized in all control flow paths"
				)
			}
			ComuneErrCode::UninitMutReference => {
				write!(
					f,
					"moved-from mut& binding must be re-initialized in all control flow paths"
				)
			}
			ComuneErrCode::LocalNewReference => {
				write!(f, "new& is only allowed in function parameters")
			}

			ComuneErrCode::LoopCtrlOutsideLoop(name) => write!(f, "{name} outside of loop"),
			ComuneErrCode::UnsafeOperation => {
				write!(f, "unsafe operation outside `unsafe` context")
			}
			ComuneErrCode::UnsafeCall(call) => {
				write!(f, "unsafe call to `{call}` outside `unsafe` context")
			}
			ComuneErrCode::DSTWithoutIndirection => {
				write!(f, "dynamically-sized type without indirection")
			}
			ComuneErrCode::TraitFunctionMismatch => {
				write!(f, "function signature does not match trait definition")
			}
			ComuneErrCode::MissingTraitFuncImpl(name) => {
				write!(f, "missing implementation for function `{name}`")
			}
			ComuneErrCode::AlreadyDefined(name) => write!(f, "conflicting definitions of `{name}`"),
			ComuneErrCode::ModuleNotFound(m) => write!(f, "module not found: {m:#?}"),
			ComuneErrCode::DependencyError => write!(f, "a dependency failed to compile"),
			ComuneErrCode::LLVMError => write!(f, "an internal compiler error occurred"),

			ComuneErrCode::InvalidUse { variable, state } => {
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

			ComuneErrCode::InvalidNewRef { variable } => {
				write!(
					f,
					"variable `{variable}` must be uninitialized to pass as new&"
				)
			}

			ComuneErrCode::ImmutVarMutation { variable } => {
				write!(
					f,
					"cannot mutate `{variable}`, as it is not declared as mutable"
				)
			}

			ComuneErrCode::InvalidMutRef { variable } => {
				write!(
					f,
					"cannot pass `{variable}` as mut&, as it is not declared as mutable"
				)
			}

			ComuneErrCode::AmbiguousCall => {
				write!(f, "ambiguous call")
			}

			ComuneErrCode::DestructureNotExhaustive(fields) => {
				write!(f, "missing fields ")?;

				for (i, field) in fields.iter().enumerate() {
					if i == fields.len() - 1 {
						write!(f, "`{field}`")?;
					} else {
						write!(f, "`{field}`, ")?;
					}
				}
				
				write!(f, " in destructure pattern")
			}

			ComuneErrCode::Pack(vec) => write!(f, "encountered {} errors", vec.len()),

			ComuneErrCode::LexerError(err) => write!(f, "internal lexer bug ({err})"),

			ComuneErrCode::Custom(text) => write!(f, "{text}"),
			ComuneErrCode::Unimplemented => write!(f, "not yet implemented"),
			ComuneErrCode::Other => write!(f, "an unknown error occurred"),
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


pub fn log_msg(msg: ComuneMessage, lexer: Option<&Lexer>) {
	let mut out = io::stderr().lock();

	match msg {
		ComuneMessage::Error(ref e) => {
			write!(
				out,
				"\n{}: {}",
				"error".bold().red(),
				msg.to_string().bold()
			)
			.unwrap();

			if let Some(lexer) = lexer {
				let file_name = lexer.file_name.to_string_lossy();

				if e.span == SrcSpan::new() {
					writeln!(
						out,
						"{}",
						format!(" - in {}\n", file_name)
						.bright_black()
					)
					.unwrap();
				} else {
					let line = lexer.get_line_number(e.span.start);
					let column = lexer.get_column(e.span.start);

					writeln!(
						out,
						"{}",
						format!(" - in {}:{}:{}\n", file_name, line + 1, column)
						.bright_black()
					)
					.unwrap();
					}
				write_code_snippet(&mut out, e.span, lexer, "~".red());
			}

			for note in &e.notes {
				write!(
					out,
					"\n{}: {}\n\n",
					"note".bold(),
					note.1
				).unwrap();

				if let Some(lexer) = lexer {
					write_code_snippet(&mut out, note.0, lexer, "-".bright_black());
				}
			}

			if let Some(backtrace) = &e.origin {
				writeln!(
					out,
					"\ncompiler backtrace:\n\n{:?}",
					backtrace
				)
				.unwrap();
			}
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
}


fn write_code_snippet(mut out: impl Write, span: SrcSpan, lexer: &Lexer, underline: ColoredString) {
	if span.start == 0 {
		return
	}

	let first_line = lexer.get_line_number(span.start);
	let last_line = lexer.get_line_number(span.start + span.len);
	let column = lexer.get_column(span.start);
	let lines = first_line..=last_line;

	let mut length_left = span.len;

	for line in first_line..=last_line {
		let og_line_text = lexer.get_line(line);

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
				column + offsets[column - 1]
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
			len = usize::min(column + span.len - 1, line_text.len()) - column
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

			let underline = underline.to_string().repeat(len);
			
			writeln!(out, "{underline}").unwrap();
		}

		if length_left == 0 {
			break;
		}
	}
}