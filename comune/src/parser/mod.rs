use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::cell::{RefCell, Ref};

use self::lexer::Token;
use self::ast::{ASTNode, ASTElem, TokenData};
use self::controlflow::ControlFlow;
use self::errors::CMNError;
use self::expression::{Expr, Operator, Atom};
use self::types::{Type, InnerType, Basic, FnParamList};

pub mod lexer;
pub mod errors;
pub mod ast;
pub mod types;
pub mod expression;
pub mod semantic;
pub mod controlflow;

// Utility functions to make the code a bit cleaner

fn get_current() -> ParseResult<Token> {
	lexer::CURRENT_LEXER.with(|lexer| lexer.borrow().current().clone().ok_or(CMNError::UnexpectedEOF))
}

fn get_next() -> ParseResult<Token> {
	lexer::CURRENT_LEXER.with(|lexer| lexer.borrow_mut().next().or(Err(CMNError::UnexpectedEOF)))
}

fn get_current_start_index() -> usize {
	lexer::CURRENT_LEXER.with(|lexer| lexer.borrow().get_current_start_index())
}

// Convenience function that matches a &str against various token kinds
fn token_compare(token: &Token, text: &str) -> bool {
	match token {
	    Token::Operator(op) => text == op.as_str(),
   		Token::Other(c) => text.chars().next().unwrap() == *c,
		Token::Keyword(keyword) => text == *keyword,
		_ => false,
	}
}


// NamespaceInfo describes a root namespace's type and symbol information, gathered on the first parsing pass.
// This is used during the generative pass to disambiguate expressions, as well as validating types and symbols.
pub struct NamespaceInfo {
	pub types: HashMap<String, Type>,
	pub symbols: HashMap<String, (Type, Option<ASTElem>)>,
	pub parsed_children: HashMap<String, NamespaceInfo>,
	pub parent: Option<Box<NamespaceInfo>>,

	pub referenced_modules: HashSet<String>,
	pub imported: Box<Option<NamespaceInfo>>,
}

impl NamespaceInfo {
	fn new() -> Self {
		NamespaceInfo { 
			types: HashMap::new(), 
			symbols: HashMap::new(),
			parsed_children: HashMap::new(),

			referenced_modules: HashSet::new(),
			imported: Box::new(None),
			parent: None,
		}
	}

	// Children take temporary ownership of their parent to avoid lifetime hell
	fn from_parent(parent: Box<NamespaceInfo>) -> Self {
		NamespaceInfo { 
			types: HashMap::new(), 
			symbols: HashMap::new(),
			parsed_children: HashMap::new(),

			referenced_modules: HashSet::new(),
			imported: Box::new(None),
			parent: Some(parent),
		}
	}

	fn get_type(&self, name: &str) -> Option<Type> {
		if let Some(basic) = Basic::get_basic_type(name) {
			Some(Type::from_basic(basic))
		} else if self.types.contains_key(name) {
			self.types.get(name).cloned()
		} else {
			let scope_op_idx = name.find("::");
			
			if let Some(idx) = scope_op_idx {
				if self.parsed_children.contains_key(&name[..idx]) {
					return self.parsed_children.get(&name[..idx]).unwrap().get_type(&name[idx+2..]);
				}
			}

			None
		}
	}


	fn get_symbol(&self, name: &str) -> Option<&(Type, Option<ASTElem>)> {
		if self.symbols.contains_key(name) {
			self.symbols.get(name)
		} else {
			let scope_op_idx = name.find("::");
			
			if let Some(idx) = scope_op_idx {
				if self.parsed_children.contains_key(&name[..idx]) {
					return self.parsed_children.get(&name[..idx]).unwrap().get_symbol(&name[idx+2..]);
				}
			}

			None
		}
	}
}


impl Display for NamespaceInfo {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "types:\n")?;
		
		for t in &self.types {
			write!(f, "\t{}: {}\n", t.0, t.1)?;
		}
		
		write!(f, "\nsymbols:\n")?;
		
		for t in &self.symbols {
			write!(f, "\t{}: {}\n", t.0, t.1.0)?;
		}

		Ok(())
	}
}




pub type ParseResult<T> = Result<T, CMNError>;
pub type ASTResult<T> = Result<T, (CMNError, TokenData)>;

pub struct Parser {
	active_namespace: Option<RefCell<NamespaceInfo>>,
	generate_ast: bool,
	verbose: bool,
}



impl Parser {
	pub fn new(verbose: bool) -> Parser {
		let result = Parser { 
			active_namespace: None,
			generate_ast: false,
			verbose
		};

		result
	}

	fn current_namespace(& self) -> &RefCell<NamespaceInfo> {
		self.active_namespace.as_ref().unwrap()
	}

	pub fn parse_module(&mut self, generate_ast: bool) -> ParseResult<&RefCell<NamespaceInfo>> {
		self.generate_ast = generate_ast;

		lexer::CURRENT_LEXER.with(|lexer| {
			lexer.borrow_mut().reset().unwrap();
		});

		self.active_namespace = Some(RefCell::new(NamespaceInfo::new()));

		match self.parse_namespace("") {
			Ok(()) => {
				
				if !generate_ast && self.verbose {
					println!("\ngenerated namespace info:\n\n{}", self.current_namespace().borrow());
				}

				Ok(&self.current_namespace())
			}
			Err(e) => {
				Err(e)
			}
		}
	
	}



	pub fn parse_namespace(&self, path: &str) -> ParseResult<()> {
		let mut current = get_current()?;

		while current != Token::EOF && current != Token::Other('}') {
			match current {
				Token::EOF => {
					return Err(CMNError::UnexpectedEOF);
				},

				Token::Keyword(ref keyword) => {

					match *keyword {

						"class" | "struct" => {
							// Register aggregate type
							let aggregate = Type::new(InnerType::Aggregate(HashMap::new()), vec![], false);
							let name_token = get_next()?;
							
							if let Token::Identifier(name) = name_token {
								let mut next = get_next()?;

								if token_compare(&next, ":") {
									// TODO: Parse base classes
								} else if !token_compare(&next, "{") {
									return Err(CMNError::UnexpectedToken);
								}

								next = get_next()?; // Consume brace

								while !token_compare(&next, "}") {
									let member_t = self.parse_type()?;

									
								}

								self.current_namespace().borrow_mut().types.insert(name, aggregate);
							}
						}

						"namespace" => {
							let name_token = get_next()?;

							if let Token::Identifier(namespace_name) = name_token {
								// We do some serious bullshit here to avoid lifetime hell
								// Children namespaces take temporary ownership of their parents,
								// and instead of having an explicit namespace stack, the parent values just live... here.
								// In the call stack. We use the stack to make a stack.
								// God I hate Rust so fucking much sometimes
								
								get_next()?; // Consume name
								get_next()?; // Consume brace

								let namespace_path = format!("{}::{}", path, namespace_name);
								let new_namespace = NamespaceInfo::new();
								let old_namespace = self.current_namespace().replace(new_namespace);

								self.current_namespace().borrow_mut().parent = Some(Box::new(old_namespace));

								self.parse_namespace(
									if path.is_empty() {
										namespace_name.as_str()
									} else {
										namespace_path.as_str()
									}
								)?;

								let dummy = NamespaceInfo::new();
								let mut parsed_namespace = self.current_namespace().replace(dummy);

								let mut old_namespace = parsed_namespace.parent.take().unwrap();
								old_namespace.parsed_children.insert(namespace_name, parsed_namespace);
								self.current_namespace().replace(*old_namespace);

							} else {
								return Err(CMNError::ExpectedIdentifier);
							}
						}


						"using" => {
							// Register type alias/import statement
							let name_token = get_next()?;

							if let Token::Identifier(name) = name_token {
								self.current_namespace().borrow_mut().referenced_modules.insert(name);
						
								let scoped_name = self.parse_scoped_name()?;

								
							} else {
								return Err(CMNError::ExpectedIdentifier);
							}

						}

						_ => {
							return Err(CMNError::UnexpectedToken);
						}
					}
				},

				Token::Identifier(_) => {
					// Parse declaration/definition
					let mut t = self.parse_type()?;
					let mut next = get_current()?;
					
					if let Token::Identifier(id) = next {
						
						next = get_next()?;

						let mut ast_elem = None;

						if let Token::Operator(op) = next {
							match op.as_str() {
								
								// Function declaration
								"(" => {	
									t = Type::new(
										InnerType::Function(
											Box::new(t), 
											self.parse_parameter_list()?
										), 
										vec![], // TODO: Generics in function declarations 
										true
									);
									
									// Past the parameter list, check if we're at a function body or not
									current = get_current()?;
									
									if current == Token::Other('{') {
										// Are we generating the AST? If not, skip the function body
										if self.generate_ast {
											ast_elem = Some(self.parse_block()?);
										} else {
											self.skip_block()?;
										}
									} else if current == Token::Other(';') {
										// No function body, just a semicolon
										get_next()?;
									} else {
										// Expected a function body or semicolon!
										return Err(CMNError::UnexpectedToken);
									}
								}

								"=" => {
									// Variable declaration
								}
								
								_ => {
									return Err(CMNError::UnexpectedToken);
								}
							}
						}

						// Register declaration to symbol table
						self.current_namespace().borrow_mut().symbols.insert(id, (t, ast_elem));
					}
				}
				
				Token::Other(tk) => {
					match tk {
						';' => {
							get_next()?;
						}

						'}' => return Ok(()),

						_ => {
							return Err(CMNError::UnexpectedToken);
						}
					}
				},

				_ => { // Other types of tokens (literals etc) not valid at this point
					return Err(CMNError::UnexpectedToken);
				}
			}

			current = get_current()?;
		}

		if current == Token::EOF {
			if path == "" {
				Ok(())
			} else {
				Err(CMNError::UnexpectedEOF)
			}
		} else if current == Token::Other('}') {
			if path != "" {
				get_next()?;
				Ok(())
			} else {
				Err(CMNError::UnexpectedToken)
			}
		}
		else {
			get_next()?;
			Ok(())
		}
	}



	// Not super robust - add checks for namespace-level keywords and abort early if found
	fn skip_block(&self) -> ParseResult<Token> {	
		let mut current = get_current()?;
	
		if current != Token::Other('{') {
			return Err(CMNError::UnexpectedToken);
		}
		let mut bracket_depth = 1;

		while bracket_depth > 0 {
			current = get_next()?;

			match current {
				Token::Other('{') => bracket_depth += 1,
				Token::Other('}') => bracket_depth -= 1,
				Token::EOF => break,
				_ => {}
			}
		}

		Ok(get_next()?)
	}



	fn parse_block(&self) -> ParseResult<ASTElem> {
		let begin = get_current_start_index();
		let mut current = get_current()?;

		if current != Token::Other('{') {
			return Err(CMNError::UnexpectedToken);
		}
	
		let mut result = Vec::<ASTElem>::new();

		get_next()?;
		
		while get_current()? != Token::Other('}') {			
			let stmt = self.parse_statement()?;
			
			if self.verbose {
				stmt.print();
			}

			result.push(stmt);

			current = get_current()?;

			while current == Token::Other(';') {
				current = get_next()?;
			}

		}

		get_next()?; // consume closing bracket
		
		let end = get_current_start_index();

		Ok(ASTElem { node: ASTNode::Block(result), token_data: (begin, end - begin), type_info: RefCell::new(None)})
	}



	fn parse_statement(&self) -> ParseResult<ASTElem> {
		let mut current = get_current()?;
		let begin = get_current_start_index();
		let mut result = None;

		match &current {
		
			Token::Identifier(id) => {
				// Might be a declaration, check if identifier is a type
				let decl_type = self.current_namespace().borrow().get_type(&id);

				if decl_type.is_some() {
					// Parse variable declaration
					
					let t = self.parse_type()?;
					let name = get_current()?;
					let mut expr = None;
					
					if token_compare(&get_next()?, "=") {
						get_next()?;
						expr = Some(Box::new(self.parse_expression()?));
					}
					self.check_semicolon()?;
					result = Some(ASTNode::Declaration(t, name, expr));
					
				}
			},

			Token::Keyword(keyword) => {
				match *keyword {
					

					// Parse return statement
					"return" => {
						let next = get_next()?;
						
						if next == Token::Other(';') {
							result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Return{expr: None})));
						} else {
							result = Some(ASTNode::ControlFlow(Box::new(ControlFlow::Return{expr: Some(self.parse_expression()?)})));
						}
						self.check_semicolon()?;
					}


					// Parse if statement
					"if" => {
						current = get_next()?;

						// Check opening brace
						if token_compare(&current, "(") {
							get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let cond = self.parse_expression()?;

						current = get_current()?;
						
						// Check closing brace
						if token_compare(&current, ")") {
							get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						// Parse body
						let body;
						let mut else_body = None;

						if token_compare(&get_current()?, "{") {
							body = self.parse_block()?;
						} else {
							body = self.parse_statement()?.wrap_in_block();
						}

						if token_compare(&get_current()?, "else") {
							get_next()?;
							
							if token_compare(&get_current()?, "{") {
								else_body = Some(self.parse_block()?);
							} else {
								else_body = Some(self.parse_statement()?.wrap_in_block());
							}
						}

						result = Some(ASTNode::ControlFlow(
							Box::new(ControlFlow::If {
								cond,
								body,
								
								// TODO: Add proper metadata to this
								else_body: match else_body { 
									None => None, 
									Some(e) => Some(e)},
							})));
					}

					// Parse while loop
					"while" => {
						current = get_next()?;

						// Check opening brace
						if token_compare(&current, "(") {
							current = get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let cond;
						
						if token_compare(&current, ")") {
							// No condtion in while statement!
							return Err(CMNError::UnexpectedToken);
						} else {
							cond = self.parse_expression()?;
							current = get_current()?;
						}

						// Check closing brace
						if token_compare(&current, ")") {
							current = get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						// Parse body
						let body;
						if token_compare(&current, "{") {
							body = self.parse_block()?;
						} else {
							body = self.parse_statement()?.wrap_in_block();
						}

						result = Some(ASTNode::ControlFlow(
							Box::new(ControlFlow::While { 
								cond, body
							})
						));
					}

					// Parse for loop
					"for" => {
						current = get_next()?;

						// Check opening brace
						if token_compare(&current, "(") {
							current = get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						let mut init = None;
						let mut cond = None;
						let mut iter = None;

						if token_compare(&current, ";") {
							// No init statement, skip
							current = get_next()?;
						} else {
							init = Some(self.parse_statement()?); // TODO: Restrict to declaration?
							current = get_current()?;
						}

						if token_compare(&current, ";") {
							// No iter expression, skip
							current = get_next()?;
						} else {
							cond = Some(self.parse_expression()?);
							self.check_semicolon()?;
							current = get_current()?;
						}

						if token_compare(&current, ";") {
							// No cond expression, skip
							current = get_next()?;
						} else if !token_compare(&current, ")") {
							iter = Some(self.parse_expression()?);
							current = get_current()?;
						}

						// Check closing brace
						if token_compare(&current, ")") {
							current = get_next()?;
						} else {
							return Err(CMNError::UnexpectedToken);
						}

						// Parse body
						let body;
						if token_compare(&current, "{") {
							body = self.parse_block()?;
						} else {
							body = self.parse_statement()?.wrap_in_block();
						}

						result = Some(ASTNode::ControlFlow(
							Box::new(ControlFlow::For { 
								init, cond, iter, body
							})
						));
					}


					// Invalid keyword at start of statement 
					_ => {
						return Err(CMNError::UnexpectedKeyword)
					}
				}
			}
	
			_ => {}
		}
		if result.is_some() {
			let end = get_current_start_index();
			let len = end - begin;
			return Ok(ASTElem {node: result.unwrap(), token_data: (begin, len), type_info: RefCell::new(None)});
		}

		// Not any of the above, try parsing an expression
		let expr = self.parse_expression()?;
		self.check_semicolon()?;
		return Ok(expr);
	}


	fn check_semicolon(&self) -> ParseResult<()> {
		if token_compare(&get_current()?, ";") {
			get_next()?;
			Ok(())
		} else {
			Err(CMNError::UnexpectedToken)
		}
	}



	fn parse_expression(&self) -> ParseResult<ASTElem> {
		let begin = get_current_start_index();
		let expr = ASTNode::Expression(RefCell::new(self.parse_expression_bp(0)?));
		let len = get_current_start_index() - begin;
		Ok(ASTElem { node: expr, token_data: (begin, len), type_info: RefCell::new(None)})
	}



	// Basic pratt parser, nothing too fancy
	fn parse_expression_bp(&self, min_bp: u8) -> ParseResult<Expr> {
		let mut current = get_current()?;
		let meta = (get_current_start_index(), current.len());

		// Get initial part of expression, could be an Atom or the operator of a unary Cons
		let lhs = match current {

			Token::Identifier(_) | Token::StringLiteral(_) | Token::NumLiteral(_) | Token::BoolLiteral(_) => 
				Expr::Atom(self.parse_atom()?, meta),
			
			Token::Operator(tk) => {
				// Handle unary prefix operators
				match Operator::get_operator(&tk, false) {
					Some(op) => {
						get_next()?;
						
						if let Operator::Call = op {
							// Special case; parse sub-expression
							let sub = self.parse_expression_bp(0)?;
							current = get_current()?;
							if let Token::Operator(op) = current {
								if op.as_str() != ")" {
									return Err(CMNError::UnexpectedToken);
								}
								get_next()?;
								return Ok(sub);
							} else {
								return Err(CMNError::UnexpectedToken);
							}
							
						} else {
							let begin_index = get_current_start_index();

							let rhs = self.parse_expression_bp(op.get_binding_power())?;

							let end_index = get_current_start_index() - 1;
							return Ok(Expr::Cons(op, vec![rhs], (end_index, end_index - begin_index)));
						}
					},
					None => return Err(CMNError::UnexpectedToken)
				};
				
				
			}
			
			_ => { return Err(CMNError::UnexpectedToken); }

		};


		loop {
			let tk = get_current()?;

			let op = match tk {

				Token::Operator(op) => match Operator::get_operator(&op, true) {
					Some(result) => result,
					None => break,
				},
			
				_ => break
			
			};
			
			let binding_power = op.get_binding_power();
			let (lbp, rbp);

			if op.is_associative_rtl() {
				lbp = binding_power;
				rbp = binding_power + 1;
			} else {
				lbp = binding_power + 1;
				rbp = binding_power;
			}

			if lbp < min_bp { 
				break;
			}
			
			get_next()?;

			let begin_index = get_current_start_index();

			let rhs = self.parse_expression_bp(rbp)?;

			let end_index = get_current_start_index();
			return Ok(Expr::Cons(op, vec![lhs, rhs], (end_index, end_index - begin_index)));
		}

		Ok(lhs)
	}



	fn parse_atom(&self) -> ParseResult<Atom> {
		let mut current = get_current()?;
		let mut scoped = None;
		let next;

		if let Token::Identifier(_) = current {
			scoped = Some(self.parse_scoped_name()?);
			next = get_current()?;	
		} else {
			next = get_next()?;
		}

		match current {
			// TODO: Variables and function calls
			Token::Identifier(id) => {
				let name = if scoped.is_some() { scoped.unwrap() } else { id };

				if let Token::Operator(ref op) = next {
					match op.as_str() {

						"(" => {
							// Function call
							let mut args = vec![];
							current = get_next()?;
							
							if current != Token::Operator(")".to_string()) {
								loop {									
									args.push(self.parse_expression()?);
									
									current = get_current()?;

									if let Token::Other(',') = current {
										get_next()?;
									} else if current == Token::Operator(")".to_string()) {
										break;
									} else {
										return Err(CMNError::UnexpectedToken);
									}
								}
							}
							get_next()?;

							Ok(Atom::FnCall{name, args})
						}

						"<" => {
							// TODO: Disambiguate between type parameter list or LT operator 
							Ok(Atom::Variable(name))
						}

						_ => {
							// Just a variable
							Ok(Atom::Variable(name))
						}
					} 
				} else {
					Ok(Atom::Variable(name))
				}	
			},

			Token::StringLiteral(s) => Ok(Atom::StringLit(s)),
			
			// TODO: Separate NumLiteral into float and int?
			Token::NumLiteral(i) => Ok(Atom::IntegerLit(i.parse::<isize>().unwrap())),

			Token::BoolLiteral(b) => Ok(Atom::BoolLit(b)),

			_ => Err(CMNError::UnexpectedToken)
		}
	}

	

	fn parse_parameter_list(&self) -> ParseResult<FnParamList> {
		let next = get_next()?;
		let mut result = vec![];

		while let Token::Identifier(_) = next {
			let mut param = (Box::new(self.parse_type()?), None);
			
			
			// Check for param name
			let mut current = get_current()?;
			if let Token::Identifier(id) = current {
				param.1 = Some(id);
				get_next()?;
			}
			
			result.push(param);

			// Check if we've arrived at a comma, skip it, and loop back around
			current = get_current()?;
			match current {
				Token::Other(',') => {
					get_next()?;
					continue;
				}
				Token::Operator(s) => {
					if s.as_str() == ")" {
						break;
					} else {
						return Err(CMNError::UnexpectedToken);
					}
				}
				_ => {
					return Err(CMNError::UnexpectedToken);
				}
			}
		}

		let current = get_current()?;

		if let Token::Operator(s) = current {
			if s.as_str() == ")" {
				get_next()?;
				Ok(result)
			} else {
				Err(CMNError::UnexpectedToken)
			}
		} else {
			Err(CMNError::UnexpectedToken)
		}
	}



	fn parse_scoped_name(&self) -> ParseResult<String> {
		let mut result = String::new();
		
		if let Token::Identifier(id) = get_current()? {
			result.push_str(&id);
		} else {
			return Err(CMNError::ExpectedIdentifier);
		}

		while token_compare(&get_next()?, "::") {
			if let Token::Identifier(id) = get_next()? {
				result.push_str("::");
				result.push_str(&id);
			} else {
				return Err(CMNError::ExpectedIdentifier);
			}
		}

		Ok(result)
	}



	fn parse_type(&self) -> ParseResult<Type> {
		let mut result : Type;
		let current = get_current()?;

		if let Token::Identifier(ref id) = current {
			// Typename
			let typename = id.clone();

			let found_type;
			{
				let ctx = self.current_namespace().borrow_mut();
				found_type = ctx.get_type(&typename);

				result = match found_type { 
					Some(t) => t.clone(),
					None => Type::new(InnerType::Unresolved(current.clone()), vec![], false)
				}
			}

			let mut next = get_next()?;
		
			match next { 
				Token::Operator(ref op) => {
					match op.as_str() {
						"*" => {
							while token_compare(&next, "*") {
								result = Type::new(InnerType::Pointer(Box::new(result)), vec![], false);
								next = get_next()?;
							}
						}
						
						"<" => {
							get_next()?;
							
							let generic = self.parse_type()?;
							result.generics.push(generic);
							
							while get_current()? == Token::Other(',') {
								get_next()?;
								
								let generic = self.parse_type()?;
								result.generics.push(generic);
							}

							// assert token == '>'
							if get_current()? != Token::Operator(">".to_string()) {
								return Err(CMNError::UnexpectedToken)
							}
							// consume >
							get_next()?;
						}
						_ => {
							// 
							return Ok(result);
						}
					}
				}
				_ => {
					return Ok(result);
				}
			}
			Ok(result)
		} else {
			Err(CMNError::ExpectedIdentifier)
		}
	}
		


	
}