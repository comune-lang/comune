mod lexer;
mod parser;
mod backend;

use std::{cell::RefCell, fs::File, path::Path, io::{self, Write}, borrow::Borrow, collections::HashMap};
use inkwell::{context::Context, targets::{Target, InitializationConfig, TargetTriple, FileType}, passes::{PassManager, PassManagerBuilder, PassRegistry}, OptimizationLevel, module::Module};
use parser::Parser;
use crate::{parser::semantic, lexer::Lexer, backend::{llvm::LLVMBackend}};
use std::process::Command;

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
		Ok(()) => {	println!("generating code..."); },
		Err(e) => { lexer.borrow().log_error_at(e.1.0, e.1.1, e.0); return; },
	}


	// LLVM Backend
	
	// Set up target machine
	Target::initialize_x86(&InitializationConfig::default());
	let target = Target::from_name("x86-64").unwrap();

	let target_machine = target.create_target_machine(
		&TargetTriple::create("x86_64-pc-linux-gnu"), 
		"x86-64", 
		"+avx2", 
		inkwell::OptimizationLevel::Aggressive, 
		inkwell::targets::RelocMode::Default, 
		inkwell::targets::CodeModel::Default
	).unwrap();

	// Create LLVM generator
	let context = Context::create();
	let module = context.create_module("test");
	let builder = context.create_builder();


	let mut backend = LLVMBackend {
		context: &context,
		module,
		builder,
		fpm: None,
		fn_value_opt: None,
	};


	// Generate LLVM IR

	// Register function prototypes
	for (sym_name, (sym_type, _)) in &namespace.borrow().symbols {
		backend.register_fn(sym_name.clone(), sym_type).unwrap();
	}

	// Generate function bodies
	for (sym_name, (sym_type, sym_elem)) in &namespace.borrow().symbols {
		backend.generate_fn(sym_name.clone(), sym_type, sym_elem).unwrap();
	}

	backend.generate_libc_bindings();
	backend.module.print_to_file("a.ir").unwrap();

	match backend.module.verify() {
    	Ok(_) => {},
    	Err(e) => {println!("an internal compiler error occurred:\n{}", e); return; },
	};	


	let mpm = PassManager::<Module>::create(());
	mpm.add_instruction_combining_pass();
	mpm.add_reassociate_pass();
	mpm.add_gvn_pass();
	mpm.add_cfg_simplification_pass();
	mpm.add_basic_alias_analysis_pass();
	mpm.add_promote_memory_to_register_pass();
	mpm.add_instruction_combining_pass();
	mpm.add_reassociate_pass();

	mpm.run_on(&backend.module);

	backend.module.print_to_file("a.ir.optimized").unwrap();

	// Write to file

	target_machine.write_to_file(&backend.module, FileType::Object, &Path::new("test.o")).unwrap();

	// Link into executable
	// We use gcc here because fuck dude i don't know how to use ld manually
	let output = Command::new("gcc")
				.arg("-ooutput")
				.arg("-nodefaultlibs")
				.arg("-lc")
				.arg("-fno-rtti")
				.arg("-fno-exceptions")
				.arg("test.o")
				.output()
				.expect("fatal: failed to link executable");
	
	io::stdout().write(&output.stdout).unwrap();
	io::stderr().write(&output.stderr).unwrap();
}
