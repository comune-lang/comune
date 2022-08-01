mod lexer;
mod parser;
mod backend;

use std::cell::RefCell;
use inkwell::context::Context;
use parser::Parser;
use crate::{parser::semantic, lexer::Lexer, backend::{llvm::LLVMBackend}};

fn main() {
	println!("comune reference compiler");

	let lexer = RefCell::new(Lexer::new("test/test.crs").unwrap());
	let mut parser = Parser::new(&lexer);

	println!("\ncollecting symbols...");
	
	// Declarative pass
	match parser.parse_module(false) {
		Ok(_) => { println!("\nbuilding AST..."); },
		Err(e) => { lexer.borrow().log_error(e); return; },
	};

	// Generative pass
	let namespace = match parser.parse_module(true) {
		Ok(ctx) => { println!("\nresolving types..."); ctx },
		Err(e) => { lexer.borrow().log_error(e); return; },
	};

	// Resolve types
	match semantic::parse_namespace(namespace) {
		Ok(()) => {},
		Err(e) => { lexer.borrow().log_error_at(e.1.0, e.1.1, e.0); return; },
	}


	// LLVM Backend
	
	let context = Context::create();
	let module = context.create_module("test");
	let builder = context.create_builder();
	
	let mut backend = LLVMBackend {
		context: &context,
		module,
		builder,
		fn_value_opt: None
	};

	for (sym_name, (sym_type, sym_elem)) in &namespace.borrow().symbols {
		backend.generate_fn(sym_name.clone(), sym_type, sym_elem).unwrap();
	}

}
