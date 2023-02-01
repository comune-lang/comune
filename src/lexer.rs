use std::ffi::{CString, OsString};
use std::fmt::{Debug, Display};
use std::fs::File;
use std::io::{self, Error, Read};
use std::path::Path;
use std::sync::mpsc::Sender;

use crate::errors::{ComuneMessage, CMNMessageLog};

use crate::ast::namespace::Name;

static KEYWORDS: [&str; 32] = [
	"if",
	"else",
	"use",
	"auto",
	"class",
	"struct",
	"public",
	"private",
	"protected",
	"module",
	"static",
	"const",
	"mut",
	"ref",
	"for",
	"while",
	"using",
	"import",
	"return",
	"break",
	"continue",
	"true",
	"false",
	"unsafe",
	"safe",
	"import",
	"export",
	"compile",
	"trait",
	"impl",
	"enum",
	"match",
];

static OPERATORS: [&str; 42] = [
	"+", "-", "/", "*", "%", "^", "|", "||", "&", "&&", "=", "==", "/=", "*=", "+=", "-=", "%=",
	"&=", "|=", "^=", "++", "--", "->", "(", ")", "[", "]", ".", "::", "<", ">", "<=", ">=", "!=",
	"<<", ">>", ">>=", "<<=", "..", "...", "=>",
	"as", // yeah `as` is technically an operator lol
];

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
	Eof,
	Name(Name),
	StringLiteral(String),
	CStringLiteral(CString),
	BoolLiteral(bool),
	Keyword(&'static str),
	NumLiteral(String, String), // Optional suffix
	Operator(&'static str),
	Other(char),
}

impl Token {
	pub fn len(&self) -> usize {
		match self {
			Token::Name(x) => x.len(),

			Token::NumLiteral(x, suf) => x.len() + suf.len(),

			Token::BoolLiteral(val) => {
				if *val {
					4
				} else {
					5
				}
			}

			Token::StringLiteral(x) => x.len() + 2,

			Token::CStringLiteral(x) => x.as_bytes().len() + 3,

			Token::Keyword(x) | Token::Operator(x) => x.len(),

			Token::Eof => 0,

			_ => 1,
		}
	}
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct SrcSpan {
	pub start: usize,
	pub len: usize,
}

impl SrcSpan {
	pub fn new() -> Self {
		SrcSpan { start: 0, len: 0 }
	}
}

impl Display for Token {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Token::Name(x) => write!(f, "{x}"),

			Token::StringLiteral(x) | Token::NumLiteral(x, _) => write!(f, "{x}"),

			Token::CStringLiteral(x) => write!(f, "{x:?}"),

			Token::Keyword(x) | Token::Operator(x) => write!(f, "{x}"),

			Token::BoolLiteral(b) => {
				if *b {
					write!(f, "true")
				} else {
					write!(f, "false")
				}
			}

			Token::Other(c) => write!(f, "{c}"),

			Token::Eof => write!(f, "eof"),
		}
	}
}

pub struct Lexer {
	file_buffer: String,
	file_index: usize, // must be on a valid utf-8 character boundary
	char_buffer: Option<char>,
	token_buffer: Vec<(SrcSpan, Token)>,
	token_index: usize,
	error_logger: Sender<CMNMessageLog>,
	pub file_name: OsString,
}

impl Lexer {
	pub fn new<P: AsRef<Path>>(
		path: P,
		error_logger: Sender<CMNMessageLog>,
	) -> std::io::Result<Lexer> {
		let mut result = Lexer {
			file_buffer: String::new(),
			file_index: 0usize,
			char_buffer: None,
			token_buffer: vec![],
			token_index: 0usize,
			error_logger,
			file_name: path.as_ref().file_name().unwrap().to_os_string(),
		};

		File::open(path)?.read_to_string(&mut result.file_buffer)?; // lol

		// Tabs fuck up the visual error reporting and making it Really Work is a nightmare because Unicode
		// So here's this hack lol
		result.file_buffer = result.file_buffer.replace('\t', "    ");
		result.tokenize_file()?;

		Ok(result)
	}

	pub fn tokenize_file(&mut self) -> io::Result<()> {
		self.file_index = 0usize;
		self.char_buffer = None;
		self.token_buffer = vec![];
		self.token_index = 0;

		self.advance_char()?;
		loop {
			match self.parse_next() {
				Ok((span, Token::Eof)) => {
					self.token_buffer.push((span, Token::Eof));
					break;
				}
				Ok(tk) => self.token_buffer.push(tk),
				Err(_) => panic!(), // Shouldn't happen?
			}
		}
		self.file_index = 0usize;

		Ok(())
	}

	pub fn seek_token_idx(&mut self, idx: usize) {
		self.token_index = idx;
	}

	pub fn get_line_number(&self, char_idx: usize) -> usize {
		if char_idx >= self.file_buffer.len() {
			self.file_buffer.lines().count()
		} else {
			self.file_buffer[..char_idx]
				.chars()
				.filter(|x| *x == '\n')
				.count()
		}
	}

	pub fn get_column(&self, char_idx: usize) -> usize {
		if char_idx >= self.file_buffer.len() {
			char_idx - self.file_buffer.len()
		} else {
			let line_num = self.get_line_number(char_idx);

			if line_num == 0 {
				char_idx - 1
			} else {
				let line_index = self
					.file_buffer
					.match_indices('\n')
					.nth(line_num - 1)
					.unwrap()
					.0;
				char_idx - line_index - 1
			}
		}
	}

	pub fn get_line(&self, line: usize) -> &str {
		self.file_buffer.lines().nth(line).unwrap()
	}

	pub fn current(&self) -> Option<&(SrcSpan, Token)> {
		self.token_buffer.get(self.token_index)
	}

	pub fn previous(&self) -> Option<&(SrcSpan, Token)> {
		if self.token_index == 0 {
			None
		} else {
			self.token_buffer.get(self.token_index - 1)
		}
	}

	pub fn current_token_index(&self) -> usize {
		self.token_index
	}

	fn skip_whitespace(&mut self) -> io::Result<()> {
		if let Some(mut token) = self.char_buffer {
			while token.is_whitespace() && !self.eof_reached() {
				token = self.get_next_char()?;
			}
			Ok(())
		} else {
			Err(Error::new(
				io::ErrorKind::UnexpectedEof,
				"file buffer exhausted",
			))
		}
	}

	fn skip_single_line_comment(&mut self) -> io::Result<()> {
		if let Some(mut token) = self.char_buffer {
			while token == '/' && self.peek_next_char()? == '/' {
				while token != '\n' && !self.eof_reached() {
					token = self.get_next_char()?;
				}
				token = self.get_next_char()?;
			}
			Ok(())
		} else {
			Err(Error::new(
				io::ErrorKind::UnexpectedEof,
				"file buffer exhausted",
			))
		}
	}

	fn skip_multi_line_comment(&mut self) -> io::Result<()> {
		if let Some(mut token) = self.char_buffer {
			let mut depth = 1;

			while token == '/' && self.peek_next_char()? == '*' {
				while !self.eof_reached() {
					token = self.get_next_char()?;

					if token == '*' && self.peek_next_char()? == '/' {
						depth -= 1;

						if depth == 0 {
							break;
						}
					}

					if token == '/' && self.peek_next_char()? == '*' {
						depth += 1;
					}
				}
				self.get_next_char()?;
				token = self.get_next_char()?;
			}
			Ok(())
		} else {
			Err(Error::new(
				io::ErrorKind::UnexpectedEof,
				"file buffer exhausted",
			))
		}
	}

	pub fn next(&mut self) -> Option<&(SrcSpan, Token)> {
		self.token_index += 1;
		if let Some((span, _)) = self.current() {
			self.file_index = span.start;
		}
		self.current()
	}

	pub fn parse_next(&mut self) -> io::Result<(SrcSpan, Token)> {
		let mut result_token = Ok(Token::Eof);
		let mut start = self.file_index;

		if let Some(mut token) = self.char_buffer {
			// skip whitespace and comments
			while !self.eof_reached()
				&& (token.is_whitespace()
					|| (token == '/' && self.peek_next_char()? == '/')
					|| (token == '/' && self.peek_next_char()? == '*'))
			{
				self.skip_whitespace()?;
				self.skip_single_line_comment()?;
				self.skip_multi_line_comment()?;
				token = self.char_buffer.unwrap();
			}

			start = self.file_index;

			if token == 'c' && self.peek_next_char()? == '"' {
				self.get_next_char()?;
				// Parse C string literal
				token = self.get_next_char()?;

				let mut result = String::new();
				let mut escaped = false;

				while token != '"' {
					if escaped {
						result.push(get_escaped_char(token).unwrap());
						escaped = false;
					} else if token == '\\' {
						escaped = true;
					} else {
						result.push(token);
					}

					token = self.get_next_char()?;
				}

				let result = result.into_bytes();

				// Consume ending quote
				self.get_next_char()?;

				result_token = Ok(Token::CStringLiteral(CString::new(result).unwrap()));
			} else if token.is_alphabetic() || token == '_' {
				// Identifier

				let mut result = String::from(token);
				let mut next = self.get_next_char()?;

				while next.is_alphanumeric() || next == '_' {
					result.push(next);
					next = self.get_next_char()?;
				}

				if KEYWORDS.contains(&result.as_str()) {
					result_token = match result.as_str() {
						"true" => Ok(Token::BoolLiteral(true)),

						"false" => Ok(Token::BoolLiteral(false)),

						_ => Ok(Token::Keyword(
							KEYWORDS
								.iter()
								.find(|x_static| **x_static == result.as_str())
								.unwrap(),
						)),
					}
				} else if OPERATORS.contains(&result.as_str()) {
					result_token = Ok(Token::Operator(
						OPERATORS
							.iter()
							.find(|x_static| **x_static == result.as_str())
							.unwrap(),
					));
				} else {
					result_token = Ok(Token::Name(result.into()))
				}
			} else if token.is_numeric() {
				// Numeric literal

				let mut result = String::from(token);
				let mut suffix = String::new();
				let mut next = self.get_next_char()?;

				while next.is_numeric() {
					result.push(next);
					next = self.get_next_char()?;
				}

				// Parse decimal stuff
				if next == '.' {
					result.push(next);
					next = self.get_next_char()?;
					while next.is_numeric() {
						result.push(next);
						next = self.get_next_char()?;
					}
				}
				// Parse suffix
				while next.is_alphanumeric() {
					suffix.push(next);
					next = self.get_next_char()?;
				}

				result_token = Ok(Token::NumLiteral(result, suffix));
			} else if let Some(op) = OPERATORS
				.iter()
				.find(|x| x.chars().next().unwrap() == token)
			{
				// Operator

				let result = String::from(token);

				let next = self.peek_next_char()?;
				let mut result_double = result.clone();
				result_double.push(next);

				// Check for two-char operator
				if OPERATORS.contains(&result_double.as_str()) {
					// Little hack for three-char operators
					let mut result_triple = result_double.clone();
					result_triple.push(self.get_next_char()?);

					if OPERATORS.contains(&result_triple.as_str()) {
						self.get_next_char()?;

						result_token = Ok(Token::Operator(
							OPERATORS
								.iter()
								.find(|x_static| **x_static == result_triple.as_str())
								.unwrap(),
						));
					} else {
						result_token = Ok(Token::Operator(
							OPERATORS
								.iter()
								.find(|x_static| **x_static == result_double.as_str())
								.unwrap(),
						));
					}
				} else if OPERATORS.contains(&result.as_str()) {
					result_token = Ok(Token::Operator(op));
				} else {
					result_token = Ok(Token::Other(token));
				}

				self.get_next_char()?;
			} else if token == '"' {
				// Parse string literal
				token = self.get_next_char()?;

				let mut result = String::new();
				let mut escaped = false;

				while token != '"' {
					if escaped {
						result.push(get_escaped_char(token).unwrap());
						escaped = false;
					} else if token == '\\' {
						escaped = true;
					} else {
						result.push(token);
					}

					token = self.get_next_char()?;
				}

				// Consume ending quote
				self.get_next_char()?;

				result_token = Ok(Token::StringLiteral(result));
			} else if self.eof_reached() && token.is_whitespace() {
				return Ok((SrcSpan { start, len: 0 }, Token::Eof));
			} else {
				result_token = Ok(Token::Other(token));
				self.get_next_char()?;
			}
		}

		match result_token {
			Ok(tk) => Ok((
				SrcSpan {
					start,
					len: tk.len(),
				},
				tk,
			)),
			Err(e) => Err(e),
		}
	}

	fn get_next_char(&mut self) -> io::Result<char> {
		match self.advance_char() {
			Ok(()) => {
				// Char buffer filled
				Ok(self.char_buffer.unwrap())
			}
			Err(e) => {
				if self.char_buffer.is_some() {
					self.file_index += self.char_buffer.unwrap().len_utf8();
					Ok(self.char_buffer.take().unwrap())
				} else {
					Err(e)
				}
			}
		}
	}

	fn eof_reached(&self) -> bool {
		self.file_index >= self.file_buffer.len()
	}

	fn advance_char(&mut self) -> io::Result<()> {
		if self.eof_reached() {
			Err(Error::new(
				io::ErrorKind::UnexpectedEof,
				"file buffer exhausted",
			))
		} else {
			let mut chars_buf = self.file_buffer[self.file_index..].chars();

			self.char_buffer = chars_buf.next();
			self.file_index += self.char_buffer.unwrap().len_utf8();

			Ok(())
		}
	}

	fn peek_next_char(&self) -> io::Result<char> {
		// Good language
		self.file_buffer[self.file_index..]
			.chars()
			.next()
			.ok_or_else(|| Error::new(io::ErrorKind::UnexpectedEof, "Unexpected EOF"))
	}

	pub fn log_msg_at(&self, span: SrcSpan, e: ComuneMessage) {
		if span.start > 0 {
			let first_line = self.get_line_number(span.start);
			let last_line = self.get_line_number(span.start + span.len);
			let column = self.get_column(span.start);
			let mut lines_text = vec![];

			for line in first_line..=last_line {
				lines_text.push(self.get_line(line).to_string());
			}

			self.error_logger
				.send(CMNMessageLog::Annotated {
					msg: e,
					lines_text,
					filename: self.file_name.to_string_lossy().into_owned(),
					lines: first_line..=last_line,
					column,
					length: span.len,
				})
				.unwrap();
		} else {
			self.error_logger
				.send(CMNMessageLog::Plain {
					msg: e,
					filename: self.file_name.to_string_lossy().into_owned(),
				})
				.unwrap();
		}
	}

	pub fn log_msg(&self, e: ComuneMessage) {
		if let Some((span, _)) = self.current() {
			self.log_msg_at(*span, e)
		} else {
			self.log_msg_at(SrcSpan { start: 0, len: 0 }, e)
		}
	}
}

pub fn get_escaped_char(c: char) -> Option<char> {
	match c {
		'n' => Some('\n'),
		't' => Some('\t'),
		'\\' => Some('\\'),
		'0' => Some('\0'),
		'"' => Some('"'),

		_ => None,
	}
}

pub fn get_unescaped_char(c: char) -> Option<&'static str> {
	match c {
		'\n' => Some("\\n"),
		'\t' => Some("\\t"),
		'\\' => Some("\\\\"),
		'\0' => Some("\\0"),
		'"' => Some("\\\""),

		_ => None,
	}
}

pub fn get_escaped(string: &str) -> String {
	let mut result = String::new();
	let mut escaped = false;

	result.reserve(string.len());

	for c in string.chars() {
		if escaped {
			result.push(get_escaped_char(c).unwrap());
			escaped = false;
		} else if c == '\\' {
			escaped = true;
		} else {
			result.push(c);
		}
	}

	result.shrink_to_fit();

	result
}

pub fn get_unescaped(string: &str) -> String {
	let mut result = String::new();
	result.reserve(string.len());

	for c in string.chars() {
		if let Some(unesc) = get_unescaped_char(c) {
			result.push_str(unesc);
		} else {
			result.push(c);
		}
	}

	result
}
