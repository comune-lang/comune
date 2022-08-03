use std::cell::RefCell;
use std::ffi::OsString;
use std::fmt::Display;
use std::fs::File;
use std::io::{self, Read, Error};
use std::path::Path;

use colored::Colorize;

use crate::parser::errors::CMNMessage;

thread_local! {
	pub(crate) static CURRENT_LEXER: RefCell<Lexer> = RefCell::new(Lexer::dummy());
}

// For logging warnings from arbitrary locations in the parse code
pub(crate) fn log_msg_at(char_idx: usize, token_len: usize, e: CMNMessage) {
	CURRENT_LEXER.with(|lexer| { 
		lexer.borrow().log_msg_at(char_idx, token_len, e);
	});
}

const KEYWORDS: &[&'static str] = &[
	"mod",	
	"if",
	"use",
	"else",  
	"auto", 
	"class",
	"struct",
	"public",
	"private",
	"protected",
	"namespace",
	"static",
	"const",
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
];

const OPERATORS: &[&str] = &[
	"+",
	"-",
	"/",
	"*",
	"%",
	"^",
	"|",
	"||",
	"&",
	"&&",
	"=",
	"==",
	"/=",
	"*=",
	"+=",
	"-=",
	"++",
	"--",
	"->",
	"(",
	")",
	"[",
	"]",
	".",
	"::",
	"<",
	">",
	"<=",
	">=",
	"!=",
	"<<",
	">>",
];




#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
	EOF,
	Identifier(String),
	StringLiteral(String),
	BoolLiteral(bool),
	Keyword(&'static str),
	NumLiteral(String),
	Operator(String),
	Other(char),
}

impl Token {
	pub fn len(&self) -> usize {
		match self {
			
			Token::Identifier(x) | Token::StringLiteral(x) | Token::NumLiteral(x) | Token::Operator(x)
				=> x.len(),

			Token::Keyword(x) => x.len(),

			Token::EOF => 0,
			
			_ => 1
		}
	}
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", 
		
		match self {
		
			Token::Identifier(x) | Token::StringLiteral(x) | Token::NumLiteral(x) | Token::Operator(x) => 
				x.clone(),

			Token::Keyword(x) => x.to_string(),
			
			Token::BoolLiteral(b) => if *b { "true".to_string() } else { "false".to_string() },
			
			Token::Other(c) => c.to_string(),

			Token::EOF => "[eof]".to_string()

		})
    }
}


pub struct Lexer {
	file_buffer: String,
	// hate hate hate hate hate hate
	file_index: usize, // must be on a valid utf-8 character boundary
	char_buffer: Option<char>,
	token_buffer: Option<Token>,
	pub file_name: OsString,
}

impl Lexer {
	pub fn dummy() -> Lexer {
		Lexer {
			file_buffer: String::new(),
			file_index: 0usize,
			char_buffer: None,
			token_buffer: None,
			file_name: OsString::new(),
		}
	}

	pub fn new<P: AsRef<Path>>(path: P) -> std::io::Result<Lexer> {
		let mut result = Lexer { 
			file_buffer: String::new(), 
			file_index: 0usize,
			char_buffer: None,
			token_buffer: None,
			file_name: path.as_ref().file_name().unwrap().to_os_string()
		};
	

		File::open(path)?.read_to_string(&mut result.file_buffer)?; // lol
		

		// Tabs fuck up the visual error reporting and making it Really Work is a nightmare because Unicode
		// So here's this hack lol
		result.file_buffer = result.file_buffer.replace("\t", "    ");

		result.advance_char()?; // Populate char buffer
		result.next()?; 		// Populate token buffer

		Ok(result)
	}

	pub fn reset(&mut self) -> io::Result<()> {
		self.file_index = 0usize;
		self.char_buffer = None;
		self.token_buffer = None;
		
		self.advance_char()?;
		self.next()?;

		Ok(())
	}

	pub fn get_line_number(&self, char_idx: usize) -> usize {
		if char_idx >= self.file_buffer.len() {
			self.file_buffer.lines().count()
		} else {
			self.file_buffer[..char_idx].chars().filter(|x| *x == '\n').count()
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
				let line_index = self.file_buffer.match_indices('\n').nth(line_num - 1).unwrap().0;
				char_idx - line_index - 1
			}
		}
	}

	pub fn get_line(&self, line: usize) -> &str {
		self.file_buffer.lines().nth(line).unwrap()
	}

	pub fn get_index(&self) -> usize {
		self.file_index
	}
	
	pub fn current(&self) -> &Option<Token> {
		&self.token_buffer
	}

	pub fn get_current_start_index(&self) -> usize {
		self.file_index - self.token_buffer.as_ref().unwrap().len()
	}

	fn skip_whitespace(&mut self) -> io::Result<()> {
		if let Some(mut token) = self.char_buffer {
			while token.is_whitespace() && !self.eof_reached() {
				token = self.get_next_char()?;
			}
			Ok(())
		} else {
			Err(Error::new(io::ErrorKind::UnexpectedEof, "file buffer exhausted"))
		}
	}

	fn skip_comment(&mut self) -> io::Result<()> {
		if let Some(mut token) = self.char_buffer {
			while token == '/' && self.peek_next_char()? == '/' {
				while token != '\n' && !self.eof_reached() {
					token = self.get_next_char()?;
				}
				token = self.get_next_char()?;
			}
			Ok(())
		} else {
			Err(Error::new(io::ErrorKind::UnexpectedEof, "file buffer exhausted"))
		}
	}

	
	pub fn next(&mut self) -> io::Result<Token> {
		let mut result_token = Ok(Token::EOF);

		if let Some(mut token) = self.char_buffer {

			// skip whitespace and comments
			while !self.eof_reached() && (token.is_whitespace() || (token == '/' && self.peek_next_char()? == '/')) {
				self.skip_whitespace()?;
				self.skip_comment()?;
				token = self.char_buffer.unwrap();
			}

			
			if token.is_alphabetic() || token == '_' {	
				// Identifier
				
				let mut result = String::from(token);
				let mut next = self.get_next_char()?;

				while next.is_alphanumeric() || next == '_' {
					result.push(next);
					next = self.get_next_char()?;
				}

				if KEYWORDS.contains(&result.as_str()) {
					result_token = match result.as_str() {
					
						"true" =>
							Ok(Token::BoolLiteral(true)),
						
						"false" =>
							Ok(Token::BoolLiteral(false)),

						_ => 
							Ok(Token::Keyword(*KEYWORDS.iter().find(|x_static| **x_static == result.as_str()).unwrap()))

					}
				} else {				
					result_token = Ok(Token::Identifier(result));
				}

			} else if token.is_numeric() { 
				// Numeric literal
				
				let mut result = String::from(token);
				let mut next = self.get_next_char()?;

				while next.is_numeric() {
					result.push(next);
					next = self.get_next_char()?;
				}

				result_token = Ok(Token::NumLiteral(result));

			} else if OPERATORS.iter().find(|x| { x.chars().next().unwrap() == token }).is_some() {
				// Operator

				let result = String::from(token);
				
				let next = self.peek_next_char()?;
				let mut result_double = result.clone(); result_double.push(next);

				// Check for two-char operator
				if OPERATORS.contains(&result_double.as_str()) {
					self.get_next_char()?;
					result_token = Ok(Token::Operator(result_double));
				} else {
					result_token = Ok(Token::Operator(result));
				}

				self.get_next_char()?;


			} else if token == '"' {
				// Parse string literal
				token = self.get_next_char()?;
				
				let mut result = String::new();
				let mut escaped = false;

				while token != '"' {
					if escaped {
						match token {
							'n' => result.push('\n'),
							't' => result.push('\t'),
							'\\' => result.push('\\'),
							'0' => result.push('\0'),

							_ => panic!() // TODO: proper error handling
						}
						escaped = false;

					} else {

						if token == '\\' {
							escaped = true;
						} else {
							result.push(token);
						}
					}
					
					token = self.get_next_char()?;
				}

				// Consume ending quote 
				self.get_next_char()?;
				result_token = Ok(Token::StringLiteral(result));

			} else if !self.eof_reached() { 
				result_token = Ok(Token::Other(token));
				self.get_next_char()?;
			}
		}

		if result_token.is_ok() {
		//	println!("{:?}", result_token.as_ref().unwrap());
			self.token_buffer = Some(result_token.as_ref().unwrap().clone());
		} else {
			self.token_buffer = None;
		}

		result_token
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
			},
		}
	}


	fn eof_reached(&self) -> bool {
		self.file_index >= self.file_buffer.len()
	}


	fn advance_char(&mut self) -> io::Result<()> {
		if self.eof_reached() {
			Err(Error::new(io::ErrorKind::UnexpectedEof, "file buffer exhausted"))
		} else {
			let mut chars_buf = self.file_buffer[self.file_index..].chars();

			self.char_buffer = chars_buf.next();
			self.file_index += self.char_buffer.unwrap().len_utf8();

			Ok(())
		}
	}


	fn peek_next_char(&self) -> io::Result<char> {
		// Good language
		self.file_buffer[self.file_index..].chars().next().ok_or(
			Error::new(io::ErrorKind::UnexpectedEof, "Unexpected EOF")
		)
	}
	

	pub fn log_msg_at(&self, char_idx: usize, token_len: usize, e: CMNMessage) {
		if char_idx > 0 {

			let line = self.get_line_number(char_idx);
			let column = self.get_column(char_idx);

			match e {
				CMNMessage::Error(_) =>		print!("{}: {}", "error".bold().red(), e.to_string().bold()),
				CMNMessage::Warning(_) =>	print!("{}: {}", "warning".bold().yellow(), e.to_string().bold()),
			}

			println!("{}", 
				format!(" in {}:{}:{}\n", self.file_name.to_string_lossy(), line + 1, column).bright_black()
			);

			println!("{} {}", 
				format!("{}\t{}", line + 1, "|").bright_black(), 
				self.get_line(line));

			print!("\t{: <1$}", "", column - 1 + 2);
			println!("{:~<1$}\n", "", token_len);	
			
			let notes = e.get_notes();
			for note in notes {
				println!("{} {}\n", "note:".bold().italic(), note.italic());
			}

		} else {
			println!("\n[error]\t{} \n[note]\tno error metadata found, can't display error location", e);
		}
	}

	pub fn log_msg(&self, e: CMNMessage) {
		let len = self.current().as_ref().unwrap().len();
		self.log_msg_at(self.file_index - len, len, e)
	}
}