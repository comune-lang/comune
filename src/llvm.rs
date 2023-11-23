use std::{
	collections::HashMap,
	io::{self, Write},
	path::{Path, PathBuf},
	process::Command,
	rc::Rc,
	sync::Arc,
};

use color_eyre::owo_colors::OwoColorize;
use inkwell::{
	attributes::{Attribute, AttributeLoc},
	basic_block::BasicBlock,
	builder::{Builder, BuilderError},
	context::Context,
	debug_info::{DebugInfoBuilder, DIType, DIFlagsConstants, DICompileUnit, AsDIScope, DWARFSourceLanguage, DILexicalBlock},
	module::{Linkage, Module},
	passes::PassManager,
	targets::{FileType, InitializationConfig, Target, TargetMachine, TargetTriple},
	types::{
		AnyType, AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType,
		StructType,
	},
	values::{
		AnyValue, AnyValueEnum, BasicMetadataValueEnum, BasicValue, BasicValueEnum, CallableValue,
		FunctionValue, InstructionValue, PointerValue,
	},
	AddressSpace, FloatPredicate, GlobalVisibility, IntPredicate,
};
use itertools::Itertools;

use crate::{
	ast::{
		expression::Operator,
		types::{
			Basic, BindingProps, DataLayout, FloatSize, FnPrototype, IntSize, TupleKind, Type,
			TypeDef, GenericParam, PtrKind,
		}, get_attribute, module::Identifier,
	},
	backend::Backend,
	cir::{CIRCallId, CIRFunction, CIRModule, CIRStmt, LValue, Operand, PlaceElem, RValue},
	constexpr::{ConstExpr, ConstValue},
	driver::Compiler,
	errors::{ComuneErrCode, ComuneError},
	lexer::{self, SrcSpan, Token},
	parser::ComuneResult,
};

pub mod dwarf_ate {
	pub const VOID: u32           = 0x00;
	pub const ADDRESS: u32        = 0x01;
	pub const BOOLEAN: u32        = 0x02;
	pub const COMPLEX: u32        = 0x03;
	pub const FLOAT: u32          = 0x04;
	pub const SIGNED: u32         = 0x05;
	pub const SIGNED_CHAR: u32    = 0x06;
	pub const UNSIGNED: u32       = 0x07;
	pub const UNSIGNED_CHAR: u32  = 0x08;
	// DWARF 3
	pub const IMAGINARY: u32      = 0x09;
	pub const PACKED_DECIMAL: u32 = 0x0A;
	pub const NUMERIC_STRING: u32 = 0x0B;
	pub const EDITED: u32         = 0x0C;
	pub const SIGNED_FIXED: u32   = 0x0D;
	pub const UNSIGNED_FIXED: u32 = 0x0E;
	pub const DECIMAL_FLOAT: u32  = 0x0F;
	// DWARF 4
	pub const UTF: u32            = 0x10;
	// DWARF 5
	pub const UCS: u32            = 0x11;
	pub const ASCII: u32          = 0x12;
	pub const LO_USER: u32        = 0x13;
	pub const HI_USER: u32        = 0x14;
}

pub const ADDRESS_SPACE_CONST: u16 = 4;

type LLVMResult<T> = Result<T, BuilderError>;

pub struct LLVMBackend {
	context: Context,
}

pub struct LLVMBuilder<'ctx> {
	pub context: &'ctx Context,
	pub module: Module<'ctx>,
	pub target_machine: TargetMachine,
	builder: Builder<'ctx>,
	fn_value_opt: Option<FunctionValue<'ctx>>,
	type_map: HashMap<String, AnyTypeEnum<'ctx>>,
	scopes: Vec<DILexicalBlock<'ctx>>,
	fn_map: HashMap<Arc<FnPrototype>, String>,
	blocks: Vec<BasicBlock<'ctx>>,
	variables: Vec<(PointerValue<'ctx>, BindingProps, Type)>,

	// DWARF Debug Info stuff	
	di_builder: Option<DebugInfoBuilder<'ctx>>,
	di_type_map: HashMap<Type, DIType<'ctx>>,
	di_compile_unit: Option<DICompileUnit<'ctx>>,
}

impl Backend for LLVMBackend {
	type Output<'out> = LLVMBuilder<'out>;

	const SUPPORTED_EMIT_TYPES: &'static [&'static str] = &["obj", "ll", "llraw"];
	const SUPPORTED_LINK_TYPES: &'static [&'static str] = &["bin", "lib", "dylib"];
	const DEFAULT_LINK_TYPES: &'static [&'static str] = &["bin"];

	fn create_instance(_: &Compiler<Self>) -> Self {
		Self {
			context: Context::create(),
		}
	}

	fn generate_code<'out>(
		&'out self,
		module: &CIRModule,
		compiler: &Compiler<Self>,
		module_name: &str,
		source_file: &str,
	) -> ComuneResult<Self::Output<'out>> {
		let mut builder = LLVMBuilder::new(
			&self.context,
			module_name,
			source_file,
			compiler.opt_level,
			compiler.debug_info
		);

		builder.compile_module(&module).unwrap();
		builder.generate_libc_bindings();

		if let Err(e) = builder.module.verify() {
			eprintln!(
				"{}\n{}\n",
				"an internal compiler error occurred:".red().bold(),
				lexer::get_escaped(e.to_str().unwrap())
			);

			let mut boguspath = PathBuf::from(&compiler.output_dir);
			boguspath.push(module_name);
			boguspath.set_extension("llbogus");

			// Output bogus LLVM here, for debugging purposes
			builder.module.print_to_file(boguspath.as_os_str()).unwrap();

			eprintln!(
				"{} ill-formed LLVM IR printed to {}",
				"note:".bold(),
				boguspath.to_string_lossy().bold()
			);

			return Err(ComuneError::new(ComuneErrCode::LLVMError, SrcSpan::new()));
		};

		Ok(builder)
	}

	fn emit(
		&self,
		compiler: &Compiler<Self>,
		builder: &Self::Output<'_>,
		emit_types: &[&str],
		out_path: &Path,
	) {
		if emit_types.contains(&"llraw") {
			builder
				.module
				.print_to_file(out_path.with_extension("llraw").as_os_str())
				.unwrap()
		}

		if compiler.opt_level == 1 {
			// Optimization passes
			let mpm = PassManager::create(());

			mpm.add_instruction_combining_pass();
			mpm.add_reassociate_pass();
			mpm.add_gvn_pass();
			mpm.add_cfg_simplification_pass();
			mpm.add_basic_alias_analysis_pass();
			mpm.add_promote_memory_to_register_pass();
			mpm.add_instruction_combining_pass();
			mpm.add_reassociate_pass();

			mpm.run_on(&builder.module);
		}

		for emit_type in emit_types {
			match *emit_type {
				"ll" => builder
					.module
					.print_to_file(out_path.with_extension("ll").as_os_str())
					.unwrap(),

				"llraw" => {}

				"obj" => builder
					.target_machine
					.write_to_file(&builder.module, FileType::Object, &out_path)
					.unwrap(),

				_ => panic!(),
			}
		}
	}

	fn link(compiler: &Compiler<Self>, link_type: &str) -> ComuneResult<()> {
		let mut output = Command::new("clang");

		for module in &*compiler.output_modules.lock().unwrap() {
			output.arg(module);
		}

		output
			.arg("-lstdc++")
			.arg("-fdiagnostics-color=always")
			.arg("-no-pie");

		let mut output_file = PathBuf::from(&compiler.output_dir);
		output_file.push(&compiler.output_file);

		output.arg("-o").arg(output_file);

		match link_type {
			"bin" => {}

			"lib" => {
				output.arg("--static");
			}

			"dylib" => {
				output.arg("--shared");
			}

			_ => panic!(),
		}

		let output_result = output.output().expect("fatal: failed to invoke linker");

		if !compiler.emit_types.contains(&"obj") {
			for module in &*compiler.output_modules.lock().unwrap() {
				let _ = std::fs::remove_file(module);
			}
		}

		if !output_result.status.success() {
			println!("");
			io::stdout().write_all(&output_result.stdout).unwrap();
			io::stderr().write_all(&output_result.stderr).unwrap();
			println!("");
			Err(ComuneError::new(ComuneErrCode::Other, SrcSpan::new()))
		} else {
			Ok(())
		}
	}


	fn get_required_emit_types(_: &str) -> &'static [&'static str] {
		&["obj"]
	}

}

impl<'ctx> LLVMBuilder<'ctx> {
	fn new(
		context: &'ctx Context,
		module_name: &str,
		source_file: &str,
		opt_level: u32,
		debug: bool,
	) -> Self {
		let module = context.create_module(module_name);
		let builder = context.create_builder();
		
		let (di_builder, di_compile_unit) = if debug {
			// jesus christ

			let (di_builder, compile_unit) = module.create_debug_info_builder(
				/* allow_unresolved */ true,
				/* language */ inkwell::debug_info::DWARFSourceLanguage::CPlusPlus,
				/* filename */ source_file,
				/* directory */ ".",
				/* producer */ "comune-rs",
				/* is_optimized */ opt_level != 0,
				/* flags */ "",
				/* runtime_ver */ 0,
				/* split_name */ "",
				/* kind */ inkwell::debug_info::DWARFEmissionKind::Full,
				/* dwo_id */ 0,
				/* split_debug_inlining */ false,
				/* debug_info_for_profiling */ false,
				/* sysroot */ "",
				/* sdk */ "",
			);

			(Some(di_builder), Some(compile_unit))
		} else {
			(None, None)
		};

		Target::initialize_x86(&InitializationConfig::default());
		let target = Target::from_name("x86-64").unwrap();
		let target_machine = target
			.create_target_machine(
				&TargetTriple::create("x86_64-pc-linux-gnu"),
				"x86-64",
				"+avx2",
				inkwell::OptimizationLevel::Default,
				inkwell::targets::RelocMode::Default,
				inkwell::targets::CodeModel::Default,
			)
			.unwrap();

		Self {
			context,
			module,
			target_machine,
			builder,
			fn_value_opt: None,
			type_map: HashMap::new(),
			scopes: vec![],
			fn_map: HashMap::new(),
			blocks: vec![],
			variables: vec![],
			
			di_builder,
			di_compile_unit,
			di_type_map: HashMap::new(),
		}
	}

	fn compile_module(&mut self, module: &CIRModule) -> LLVMResult<()> {
		// Add opaque types
		for (name, ty) in &module.types {
			self.register_type(name.clone(), &ty.read().unwrap())
		}

		// Define type bodies
		for (name, ty) in &module.types {
			let ty = ty.read().unwrap();

			self.generate_type_body(name, &ty);
		}

		// Register globals
		// TODO: Actually initialize
		for (name, (ty, _)) in &module.globals {
			let ty_ll = Self::to_basic_type(self.get_llvm_type(ty));

			self.module.add_global(
				ty_ll, 
				None, 
				&name.to_string()
			).set_initializer(&ty_ll.const_zero());
		}

		// Register functions
		for (proto, func) in &module.functions {
			let mangled = self.get_mangled_name(&proto, func);

			self.register_fn(&mangled, func)?;
			self.fn_map.insert(proto.clone(), mangled);
		}
		
		// And generate their bodies
		for (proto, func) in &module.functions {
			if !func.is_extern {
				let mangled = self.get_mangled_name(&proto, func);

				self.generate_fn(&mangled, func)?;
			}
		}

		if let Some(di_builder) = &self.di_builder {
			di_builder.finalize();
		}

		Ok(())
	}

	fn register_type(&mut self, name: String, ty: &TypeDef) {
		if self.type_map.contains_key(&name) {
			return;
		}

		let opaque = self.context.opaque_struct_type(&name).as_any_type_enum();

		self.type_map.insert(name, opaque);

		for (_, variant) in &ty.variants {
			let variant_name = variant.read().unwrap().name.to_string();

			self.register_type(variant_name, &variant.read().unwrap());
		}
	}

	fn generate_type_body(&self, name: &str, ty: &TypeDef) {
		if !self.type_map[name].into_struct_type().is_opaque() {
			return;
		}

		let mut members_ir = vec![];

		for disc in ty.get_parent_discriminants() {
			// add parent discriminants
			// TODO: there's room for space optimization here
			members_ir.push(Self::to_basic_type(self.get_llvm_type(&Type::Basic(disc))));
		}

		self.generate_type_own_members(ty, &mut members_ir);
		
		let type_ir = self.type_map[name].into_struct_type();
		type_ir.set_body(&members_ir, ty.layout == DataLayout::Packed);
	}

	fn type_own_data_size(&self, ty: &TypeDef) -> u64 {
		let mut members_ir = vec![];
		let target_data = self.target_machine.get_target_data();
		
		self.generate_type_own_members(ty, &mut members_ir);

		let strct = self.context.struct_type(&members_ir, ty.layout == DataLayout::Packed);
		target_data.get_store_size(&strct)
	}

	fn generate_type_own_members(&self, ty: &TypeDef, members_ir: &mut Vec<BasicTypeEnum<'ctx>>) {
		if !ty.variants.is_empty() {
			members_ir.push(self.context.i32_type().into());
						
			// enum data store
			let mut max_size = 0;

			for (_, variant) in &ty.variants {
				let variant_name = variant.read().unwrap().name.to_string();

				self.generate_type_body(&variant_name, &variant.read().unwrap());
				let variant_size = self.type_own_data_size(&variant.read().unwrap());

				max_size = max_size.max(variant_size);
			}

			if max_size > 0 {
				members_ir.push(
					self.context
						.i8_type()
						.vec_type(max_size as u32)
						.as_basic_type_enum(),
				);
			}
		}

		for (_, mem, _) in &ty.members {
			members_ir.push(Self::to_basic_type(self.get_llvm_type(mem)));
		}
	}

	fn generate_libc_bindings(&self) {
		let exit_t = self.context.void_type().fn_type(
			&[BasicMetadataTypeEnum::IntType(self.context.i32_type())],
			false,
		);

		self.module
			.add_function("_exit", exit_t, Some(Linkage::External));
	}

	fn register_fn(&mut self, name: &str, t: &CIRFunction) -> LLVMResult<FunctionValue> {
		if self.module.get_function(name).is_some() {
			panic!("function name collision in LLVM! `{name}`")
		}

		let fn_t = self.generate_prototype(t)?;
		let fn_v = self.module.add_function(name, fn_t, None);

		if t.ret.1.is_never() {
			fn_v.add_attribute(
				AttributeLoc::Function,
				self.get_attribute("noreturn")
			)
		}

		if self.di_builder.is_some() && !t.is_extern {
			let ret = if t.ret.1.is_never() {
				None
			} else {
				Some(self.get_di_type(&t.ret.1))
			};

			let params = t
				.variables[0..t.arg_count]
				.iter()
				.map(|(arg, props, _)| if props.is_ref { self.get_di_type(&arg.ptr_type(PtrKind::Raw)) } else { self.get_di_type(arg) })
				.collect_vec();

			let di_compile_unit = self.di_compile_unit.as_ref().unwrap();
			let di_builder = self.di_builder.as_ref().unwrap();

			let di_type = di_builder.create_subroutine_type(
				di_compile_unit.get_file(),
				ret,
				&params,
				DIFlagsConstants::PUBLIC
			);
			
			let subprogram = di_builder.create_function(
				di_compile_unit.as_debug_info_scope(),
				name,
				None,
				di_compile_unit.get_file(),
				t.line as u32,
				di_type,
				false,
				true,
				t.line as u32,
				DIFlagsConstants::PUBLIC,
				false
			);

			fn_v.set_subprogram(subprogram);
		}

		Ok(fn_v)
	}

	fn get_mangled_name(&self, id: &FnPrototype, func: &CIRFunction) -> String {
		// Check if the function has a `no_mangle` or `export_as` attribute, or if it's `main`. If not, mangle the name
		if get_attribute(&func.attributes, "no_mangle").is_some() {
			id.path.name().to_string()
		} else if let Some(export_name) = get_attribute(&func.attributes, "export_as") {
			// Export with custom symbol name
			let Some(first_arg) = export_name.args.get(0) else {
				panic!()
			}; 

			let Some(Token::StringLiteral(name)) = first_arg.get(0) else {
				panic!()
			};

			name.clone()				
		} else {
			// Mangle name
			mangle_name(&id.path, func)
		}
	}

	fn generate_fn(&mut self, name: &str, t: &CIRFunction) -> LLVMResult<FunctionValue> {
		let fn_v = self.module.get_function(name).unwrap();

		self.fn_value_opt = Some(fn_v);

		if self.di_builder.is_some() {
			self.scopes.clear();
			
			for _ in 0..t.scopes.len() {
				let di_builder = self.di_builder.as_ref().unwrap();
				let compile_unit = self.di_compile_unit.as_ref().unwrap();
				let block = di_builder.create_lexical_block(
					fn_v.get_subprogram().unwrap().as_debug_info_scope(),
					compile_unit.get_file(),
					0,
					0
				);

				self.scopes.push(block);
			}

			self.builder.set_current_debug_location(
				self.di_builder.as_ref().unwrap().create_debug_location(
					self.context, 
					t.line as u32,
					t.column as u32,
					fn_v.get_subprogram().unwrap().as_debug_info_scope(), 
					None
				)
			);
		}

		for i in 0..t.blocks.len() {
			self.blocks.push(
				self.context.append_basic_block(fn_v, &format!("bb{i}")),
			);
		}

		for (i, (ty, props, _)) in t.variables.iter().enumerate() {
			let mut ty_ll = Self::to_basic_type(self.get_llvm_type(ty));

			if self.pass_by_ptr(&ty, props) {
				ty_ll = Self::to_basic_type(self.get_llvm_type(&ty.ptr_type(PtrKind::Raw)));
			}

			self.variables.push((
				self.create_entry_block_alloca(&format!("_{i}"), ty_ll)?,
				*props,
				ty.clone(),
			));
		}

		// Build parameter stores
		{
			self.builder.position_at_end(self.blocks[0]);

			for (idx, param) in self
				.fn_value_opt
				.as_ref()
				.unwrap()
				.get_param_iter()
				.enumerate()
			{
				let param_props = t.variables[idx].1;

				// If parameter is a `new&` binding, don't add noundef attribute
				if !param_props.is_new {
					fn_v.add_attribute(
						AttributeLoc::Param(idx as u32),
						self.get_attribute("noundef"),
					);
				}

				self.builder.build_store(self.variables[idx].0, param)?;
			}
		}

		for i in 0..t.blocks.len() {
			let block = &t.blocks[i];

			self.builder.position_at_end(self.blocks[i]);

			for stmt in block.items.iter() {
				match stmt {
					CIRStmt::Assignment(lval, expr) => {
						let store = self.generate_lvalue_use(
							lval, 
							BindingProps::mut_reference()
						)?;

						self.generate_expr(
							self.indirection_as_pointer(store),
							expr,
						)?;
					}

					CIRStmt::RefInit(var, lval) => {
						let reference = self.variables[*var].0;
						let props = self.variables[*var].1;

						assert!(props.is_ref);
						
						self.builder.build_store(reference, self.generate_lvalue_use(lval, props)?)?;
					}

					CIRStmt::GlobalAccess { local, symbol } => {
						let reference = self.variables[*local].0;
						let props = self.variables[*local].1;

						assert!(props.is_ref);

						self.builder.build_store(
							reference, 
							self.module.get_global(&symbol.to_string()).unwrap().as_basic_value_enum()
						)?;
					}

					CIRStmt::Jump(block) => {
						self.builder.build_unconditional_branch(self.blocks[*block])?;
					}

					CIRStmt::Switch(cond, branches, else_block) => {
						let cond_ir = self
							.generate_operand(&Type::i32_type(true), cond)?
							.as_basic_value_enum()
							.into_int_value();

						let cases = branches
							.iter()
							.map(|(ty, val, branch)| {
								Ok((
									self.generate_operand(ty, val)?.into_int_value(),
									self.blocks[*branch],
								))
							})
							.collect::<LLVMResult<Vec<_>>>()?;

						self.builder
							.build_switch(cond_ir, self.blocks[*else_block], &cases)?;
					}

					CIRStmt::Return => {
						if let Some(lval) = t.get_return_lvalue() {
							let ret = self.generate_lvalue_use(&lval, t.ret.0)?;

							self.builder.build_return(Some(&ret))?;
						} else {
							self.builder.build_return(None)?;
						}
					}

					CIRStmt::Call {
						id,
						args,
						generic_args,
						result,
					} => {
						assert!(
							generic_args.is_empty(),
							"encountered un-monoized type argument in LLVM codegen!"
						);

						let fn_v = match id {
							CIRCallId::Direct(id, _) => {
								let Some(mangled) = &self.fn_map.get(id) else {
									panic!("could not fetch function {id} from function map!");
								};

								let fn_v = self.module.get_function(mangled).unwrap();

								fn_v.into()
							}

							CIRCallId::Indirect { local, .. } => {
								let ptr = self
									.generate_lvalue_use(local, BindingProps::value())?
									.into_pointer_value();

								CallableValue::try_from(ptr).unwrap()
							}
						};

						let args_mapped: Vec<_> = args
							.iter()
							.map(|(lval, _, props)| {
								Ok(Self::to_basic_metadata_value(
									self.generate_lvalue_use(lval, *props)?.into(),
								))
							})
							.collect::<LLVMResult<Vec<_>>>()?;

						let callsite = self.builder.build_call(fn_v, &args_mapped, "").unwrap();

						if let Some(result) = result {
							if result.props.is_ref {
								// Function return value is a reference - perform reference initialization
								assert!(result.projection.is_empty());

								self.builder.build_store(
									self.variables[result.local].0,
									callsite.try_as_basic_value().unwrap_left(),
								)?;
							} else {
								// Function return value is a plain value - use normal assignment
								self.builder.build_store(
									self.generate_lvalue_use(result, BindingProps::mut_reference())?
										.into_pointer_value(),
									callsite.try_as_basic_value().unwrap_left(),
								)?;
							}
						}
					}

					CIRStmt::Invoke {
						id,
						args,
						generic_args,
						result,
						next,
						except,
					} => {
						assert!(
							generic_args.is_empty(),
							"encountered un-monoized type argument in LLVM codegen!"
						);

						let fn_v = match id {
							CIRCallId::Direct(id, _) => {
								let mangled = &self.fn_map[id];
								let fn_v = self.module.get_function(mangled).unwrap();

								fn_v.into()
							}

							CIRCallId::Indirect { local, .. } => {
								let ptr = self
									.generate_lvalue_use(local, BindingProps::value())?
									.into_pointer_value();

								CallableValue::try_from(ptr).unwrap()
							}
						};

						let mut args_mapped = Vec::with_capacity(args.len());

						for (lval, _, props) in args {
							args_mapped.push(self.generate_lvalue_use(lval, *props)?);
						}

						let callsite = self.builder.build_invoke(
							fn_v,
							&args_mapped,
							self.blocks[*next],
							self.blocks[*except],
							"",
						).unwrap();

						if let Some(result) = result {
							self.builder.position_at_end(self.blocks[*next]);

							if result.props.is_ref {
								// Function return value is a reference - perform reference initialization
								assert!(result.projection.is_empty());

								self.builder.build_store(
									self.variables[result.local].0,
									callsite.try_as_basic_value().unwrap_left(),
								)?;
							} else {
								// Function return value is a plain value - use normal assignment
								self.builder.build_store(
									self.generate_lvalue_use(result, BindingProps::mut_reference())?
										.into_pointer_value(),
									callsite.try_as_basic_value().unwrap_left(),
								)?;
							}
						}
					}

					CIRStmt::StorageLive(_local) | CIRStmt::StorageDead(_local) => {
						// yeah this doesn't work. no idea why

						/*
						let intrinsic = if let CIRStmt::StorageLive(_) = stmt {
							Intrinsic::find("llvm.lifetime.start").unwrap()
						} else {
							Intrinsic::find("llvm.lifetime.end").unwrap()
						};

						let i64_ty = self.context.i64_type();
						let i8ptr_ty = self.context.i8_type().ptr_type(AddressSpace::default());

						let lifetime_func = intrinsic.get_declaration(&self.module, &[
							i64_ty.as_basic_type_enum(), 
							i8ptr_ty.as_basic_type_enum()
						]).unwrap();

						let local = self.variables[*local].0;
						let underlying_type = local.get_type().get_element_type();
						let store_size = self.target_machine.get_target_data().get_store_size(&underlying_type);
						
						self.builder.build_call(lifetime_func, &[
							self.context.i64_type().const_int(store_size, false).into(),
							self.builder.build_bitcast(local, i8ptr_ty, "").into()
						], ""); */
					}

					CIRStmt::DropShim { .. } => panic!("encountered DropShim in LLVM codegen!"),

					CIRStmt::Unreachable => {
						self.builder.build_unreachable()?;
					}

					CIRStmt::SourceLoc(line, column) => {
						if let Some(di_builder) = &self.di_builder {
							self.builder.set_current_debug_location(
								di_builder.create_debug_location(
									self.context, 
									*line as u32, 
									*column as u32, 
									self.scopes[t.blocks[i].scope].as_debug_info_scope(), 
									None,
								)
							);
						}
					}
				}
			}
		}

		if !t.generics.is_empty() {
			self.fn_value_opt.unwrap().set_linkage(Linkage::LinkOnceODR);
		}

		self.blocks.clear();
		self.variables.clear();

		Ok(self.fn_value_opt.unwrap())
	}

	fn generate_expr(&self, store: PointerValue<'ctx>, expr: &RValue) -> LLVMResult<InstructionValue<'ctx>> {
		match expr {
			RValue::Atom(ty, op_opt, atom, _) => {
				match op_opt {
					Some(Operator::Deref) => {
						let atom_ir = self.indirection_as_pointer(self.generate_operand(ty, atom)?);

						self.builder.build_store(
							store,
							self.builder
								.build_load(atom_ir, "")?
								.as_basic_value_enum(),
						)
					}

					Some(Operator::Ref | Operator::RefMut) => {
						if let Operand::LValueUse(lval, props) = atom {
							// Terrible hack
							let mut props = *props;
							props.is_ref = true;
							props.is_mut = matches!(op_opt, Some(Operator::RefMut));

							self.builder
								.build_store(store, self.generate_lvalue_use(lval, props)?)
						} else {
							panic!()
						}
					}

					Some(Operator::UnaryMinus) => {
						if ty.is_integral() {
							let atom_ir = self.generate_operand(ty, atom)?.into_int_value();

							assert!(ty.is_signed());
							
							self.builder.build_store(
								store,
								self.builder.build_int_neg(atom_ir, "")?
							)
						} else if ty.is_floating_point() {
							let atom_ir = self.generate_operand(ty, atom)?.into_float_value();
							
							self.builder.build_store(
								store,
								self.builder.build_float_neg(atom_ir, "")?
							)
						} else {
							panic!()
						}
					}

					// honestly why do we even have this
					Some(Operator::UnaryPlus) => {
						self.builder.build_store(store, self.generate_operand(ty, atom)?)
					}

					Some(Operator::LogicNot) => {
						let atom_ir = self.generate_operand(ty, atom)?.into_int_value();
						
						assert!(ty.is_boolean());

						self.builder.build_store(
							store,
							self.builder.build_not(atom_ir, "")?
						)
					}

					None => self
						.builder
						.build_store(store, self.generate_operand(ty, atom)?),

					_ => panic!(),
				}
			}

			RValue::Cons(expr_ty, [(lhs_ty, lhs), (rhs_ty, rhs)], op, _) => {
				let lhs_v =
					Self::to_basic_value(self.generate_operand(lhs_ty, lhs)?.as_any_value_enum())
						.as_basic_value_enum();
				let rhs_v =
					Self::to_basic_value(self.generate_operand(rhs_ty, rhs)?.as_any_value_enum())
						.as_basic_value_enum();
				let result;

				if expr_ty.is_integral() {
					let lhs_i = lhs_v.into_int_value();
					let rhs_i = rhs_v.into_int_value();

					assert!(lhs_ty.is_signed() == rhs_ty.is_signed());

					result = match op {
						Operator::Add => self.builder.build_int_add(lhs_i, rhs_i, ""),
						Operator::Sub => self.builder.build_int_sub(lhs_i, rhs_i, ""),
						Operator::Mul => self.builder.build_int_mul(lhs_i, rhs_i, ""),
						Operator::Div => {
							if lhs_ty.is_signed() {
								self.builder.build_int_signed_div(lhs_i, rhs_i, "")
							} else {
								self.builder.build_int_unsigned_div(lhs_i, rhs_i, "")
							}
						}
						
						// NOTE: This translates to LLVM's srem and urem instructions,
						// which are subtly different from a proper modulo operator,
						// particularly in the sign of the result type.
						// Is this fine? Should we do something about this? i dunno
						Operator::Mod => {
							if lhs_ty.is_signed() {
								self.builder.build_int_signed_rem(lhs_i, rhs_i, "")
							} else {
								self.builder.build_int_unsigned_rem(lhs_i, rhs_i, "")
							}
						}
						
						Operator::BitAND => self.builder.build_and(lhs_i, rhs_i, ""),
						Operator::BitOR => self.builder.build_or(lhs_i, rhs_i, ""),
						Operator::BitXOR => self.builder.build_xor(lhs_i, rhs_i, ""),
						Operator::BitShiftL => self.builder.build_left_shift(lhs_i, rhs_i, ""),
						Operator::BitShiftR => self.builder.build_right_shift(lhs_i, rhs_i, false, ""),
						
						_ => unimplemented!()
					}?
					.as_basic_value_enum();
				} else if expr_ty.is_floating_point() {
					let lhs_f = lhs_v.into_float_value();
					let rhs_f = rhs_v.into_float_value();

					result = match op {
						Operator::Add => self.builder.build_float_add(lhs_f, rhs_f, ""),
						Operator::Sub => self.builder.build_float_sub(lhs_f, rhs_f, ""),
						Operator::Mul => self.builder.build_float_mul(lhs_f, rhs_f, ""),
						Operator::Div => self.builder.build_float_div(lhs_f, rhs_f, ""),

						_ => panic!(),
					}?
					.as_basic_value_enum()
				} else if expr_ty.is_boolean() {
					if lhs_ty.is_integral() {
						let lhs_i = lhs_v.into_int_value();
						let rhs_i = rhs_v.into_int_value();

						result = self
							.builder
							.build_int_compare(
								Self::to_int_predicate(op, lhs_ty.is_signed()),
								lhs_i,
								rhs_i,
								"",
							)?
							.as_basic_value_enum();
					} else if lhs_ty.is_floating_point() {
						let lhs_f = lhs_v.into_float_value();
						let rhs_f = rhs_v.into_float_value();

						result = self
							.builder
							.build_float_compare(Self::to_float_predicate(op), lhs_f, rhs_f, "")?
							.as_basic_value_enum();
					} else {
						panic!()
					}
				} else if matches!(expr_ty, Type::Pointer { .. }) {
					let lhs = lhs_v.into_pointer_value();
					let rhs = rhs_v.into_int_value();

					result = unsafe {
						self.builder
							.build_gep(lhs, &[rhs], "")?
							.as_basic_value_enum()
					};
				} else {
					panic!("unknown binary expression: {lhs_ty} {op} {rhs_ty} => {expr_ty}!");
				}

				self.builder.build_store(store, result)
			}

			RValue::Cast {
				from,
				to,
				val,
				span: _,
			} => {
				match to {
					Type::Tuple(TupleKind::Sum, _) => {
						let val = self.generate_operand(from, val)?;

						let ptr = self.builder.build_pointer_cast(
							store,
							val.get_type().ptr_type(AddressSpace::default()),
							"",
						)?;

						self.builder.build_store(ptr, val)
					}

					Type::TypeRef { .. } if matches!(from, Type::Tuple(TupleKind::Sum, _)) => {
						// cast from (T::VariantA | T::VariantB) to T

						let val = self.generate_operand(from, val)?.into_struct_value();
						let from_data = from.get_sum_data_field().unwrap() as u32;
						let data = self.builder.build_extract_value(val, from_data, "").unwrap();

						self.builder.build_store(
							self.builder.build_bitcast(
								store, 
								data.get_type().ptr_type(AddressSpace::default()), 
								""
							)?.into_pointer_value(),
							data
						)
					}

					Type::TypeRef { .. } if to.get_variant_index(from).is_some() => {
						let val = self.generate_operand(from, val)?;
						let ptr = self.builder.build_pointer_cast(
							store,
							val.get_type().ptr_type(AddressSpace::default()),
							"",
						)?;

						self.builder.build_store(ptr, val)
					}

					_ => match from {
						Type::Pointer { .. } => {
							let val = self.generate_operand(from, val)?;
							let to_ir = self.get_llvm_type(to);

							if to.is_boolean() {
								self.builder.build_store(
									store,
									self.builder.build_is_not_null(self.indirection_as_pointer(val), "")?,
								)
							} else {
								self.builder.build_store(
									store,
									self.builder
										.build_pointer_cast(
											self.indirection_as_pointer(val),
											to_ir.into_pointer_type(),
											"",
										)?
										.as_basic_value_enum(),
								)
							}
						}

						Type::Tuple(TupleKind::Newtype, _) => {
							let val = self.generate_operand(from, val)?;
							
							self.builder.build_store(store, val)
						}

						Type::Tuple(TupleKind::Sum, _) => {
							// Tuple downcast, aka just indexing into the data field
							let Operand::LValueUse(lvalue, props) = val else {
								panic!()
							};

							let val = self.generate_lvalue_use(lvalue, *props)?;
							
							self.builder.build_store(store, val)
						}

						Type::TypeRef { .. } if from.get_variant_index(to).is_some() => {
							// Enum downcast (i.e. `Option` -> `Option::Some`)
							let Operand::LValueUse(lvalue, props) = val else {
								panic!()
							};

							let val = self.generate_lvalue_use(lvalue, *props)?;
							
							self.builder.build_store(store, val)
						}

						Type::Basic(b) => {
							if from.is_integral() || from.is_floating_point() {
								let val = self.generate_operand(from, val)?;

								match val {
									BasicValueEnum::IntValue(i) => match &to {
										Type::Basic(Basic::Bool) => self.builder.build_store(
											store,
											self.builder
												.build_select(
													val.into_int_value(),
													i.get_type().const_int(1, false),
													i.get_type().const_zero(),
													"",
												)?
												.as_basic_value_enum(),
										),

										_ => match self.get_llvm_type(to) {
											AnyTypeEnum::IntType(t) => self.builder.build_store(
												store,
												self.builder
													.build_int_cast(i, t, "")?
													.as_basic_value_enum(),
											),

											AnyTypeEnum::FloatType(t) => {
												if from.is_signed() {
													self.builder.build_store(
														store,
														self.builder
															.build_signed_int_to_float(i, t, "")?
															.as_basic_value_enum(),
													)
												} else {
													self.builder.build_store(
														store,
														self.builder
															.build_unsigned_int_to_float(i, t, "")?
															.as_basic_value_enum(),
													)
												}
											}

											_ => panic!(),
										},
									},

									BasicValueEnum::FloatValue(f) => match self.get_llvm_type(to) {
										AnyTypeEnum::FloatType(t) => self.builder.build_store(
											store,
											self.builder
												.build_float_cast(f, t, "")?
												.as_basic_value_enum(),
										),

										AnyTypeEnum::IntType(t) => {
											if to.is_signed() {
												self.builder.build_store(
													store,
													self.builder
														.build_float_to_signed_int(f, t, "")?
														.as_basic_value_enum(),
												)
											} else {
												self.builder.build_store(
													store,
													self.builder
														.build_float_to_unsigned_int(f, t, "")?
														.as_basic_value_enum(),
												)
											}
										}

										_ => panic!(),
									},

									_ => panic!(),
								}
							} else {
								// Not numeric, match other Basics

								match b {
									Basic::Bool => {
										let Type::Basic(Basic::Integral { signed, .. }) = to else {
											panic!()
										};

										let val = self
											.generate_operand(from, val)?
											.as_basic_value_enum()
											.into_int_value();

										self.builder.build_store(
											store,
											self.builder
												.build_int_cast_sign_flag(
													val,
													self.get_llvm_type(to).into_int_type(),
													*signed,
													"",
												)?
												.as_basic_value_enum(),
										)
									}

									_ => unimplemented!(),
								}
							}
						}

						_ => unimplemented!("cast from {from} to {to}"),
					},
				}
			}
		}
	}

	fn generate_operand(&self, ty: &Type, expr: &Operand) -> LLVMResult<BasicValueEnum<'ctx>> {
		let const_addr_space = AddressSpace::from(ADDRESS_SPACE_CONST);

		match expr {
			Operand::StringLit(s, _) => {
				let len = s.as_bytes().len().try_into().unwrap();
				let string_t = self.context.i8_type().array_type(len);
				let val = self
					.module
					.add_global(string_t, Some(const_addr_space), ".str");

				let literal = self.context.const_string(s.as_bytes(), false);

				val.set_visibility(GlobalVisibility::Hidden);
				val.set_linkage(Linkage::Private);
				val.set_unnamed_addr(true);
				val.set_initializer(&literal);

				Ok(self.slice_type(&self.context.i8_type())
					.const_named_struct(&[
						val.as_pointer_value().as_basic_value_enum(),
						self.context
							.i64_type()
							.const_int(len.into(), false)
							.as_basic_value_enum(),
					])
					.as_basic_value_enum())
			}

			Operand::CStringLit(s, _) => {
				let val = self.module.add_global(
					self.context
						.i8_type()
						.array_type(s.as_bytes_with_nul().len() as u32),
					Some(const_addr_space),
					".cstr",
				);

				val.set_visibility(GlobalVisibility::Hidden);
				val.set_linkage(Linkage::Private);
				val.set_unnamed_addr(true);

				let literal = self.context.const_string(s.as_bytes(), true);

				val.set_visibility(GlobalVisibility::Hidden);
				val.set_linkage(Linkage::Private);
				val.set_unnamed_addr(true);
				val.set_initializer(&literal);

				Ok(self.builder
					.build_address_space_cast(
						self.builder
							.build_bitcast(
								val.as_pointer_value(),
								self.context.i8_type().ptr_type(const_addr_space),
								"",
							)?
							.into_pointer_value(),
						self.context.i8_type().ptr_type(AddressSpace::default()),
						"",
					)?
					.as_basic_value_enum())
			}

			Operand::IntegerLit(i, _) => Ok(Self::to_basic_type(self.get_llvm_type(ty))
				.into_int_type()
				.const_int(*i as u64, true)
				.as_basic_value_enum()),

			Operand::FloatLit(f, _) => Ok(Self::to_basic_type(self.get_llvm_type(ty))
				.into_float_type()
				.const_float(*f)
				.as_basic_value_enum()),

			Operand::BoolLit(b, _) => Ok(self
				.context
				.bool_type()
				.const_int(u64::from(*b), false)
				.as_basic_value_enum()),

			Operand::LValueUse(lval, props) => self.generate_lvalue_use(lval, *props),

			Operand::Undef => Ok(self.get_undef(&Self::to_basic_type(self.get_llvm_type(ty)))),
		}
	}

	fn generate_lvalue_use(&self, expr: &LValue, props: BindingProps) -> LLVMResult<BasicValueEnum<'ctx>> {
		// Get the variable pointer from the function
		let (local, lprops, ty) = &self.variables[expr.local];
		
		let mut local = local.as_basic_value_enum();

		// If the lvalue is a reference, perform a load
		// so we're left with a single indirection
		if self.pass_by_ptr(ty, lprops) {
			local = self
					.builder
					.build_load(self.indirection_as_pointer(local), "")?
					.as_basic_value_enum();
		}
		
		let mut ty = ty.clone();
		// Perform geps and whatnot to get a pointer to the sublocation

		for proj in expr.projection.iter() {
			local = match proj {
				PlaceElem::Deref => {
					let Type::Pointer(pointee, _) = ty else {
						panic!()
					};
					
					ty = *pointee.clone();
					
					self
						.builder
						.build_load(self.indirection_as_pointer(local), "")?
						.as_basic_value_enum()
				}

				PlaceElem::Index { index_ty, index, op } => {
					let (Type::Array(sub, _) | Type::Pointer(sub, _)) = ty else {
						panic!()
					};

					ty = *sub.clone();

					let mut idx = self
						.generate_operand(index_ty, index)?
						.as_basic_value_enum()
						.into_int_value();

					if *op == Operator::Sub {
						idx = self.builder.build_int_neg(idx, "")?;
					}

					local = self.builder.build_load(self.indirection_as_pointer(local), "")?;

					unsafe { 
						self
							.builder
							.build_gep(
								self.indirection_as_pointer(local),
								&[idx], 
								""
							)?
							.as_basic_value_enum()
						}
				}

				PlaceElem::Field(i) => {
					let idx = i + ty.get_fields_offset();

					ty = ty.get_field_type(*i);

					self
						.builder
						.build_struct_gep(self.indirection_as_pointer(local), idx as u32, "")
						.expect(&format!("failed to generate Field projection for `{expr}` into {:?}`", local.get_type()))
						.as_basic_value_enum()
				}
						
				PlaceElem::SumDisc => {
					let result = self
						.builder
						.build_struct_gep(
							self.indirection_as_pointer(local),
							ty.get_sum_disc_field().unwrap() as u32,
							""
						)
						.expect(&format!("failed to generate SumDisc projection for `{expr} into {:?}`", local.get_type()))
						.as_basic_value_enum();
					
					ty = Type::Basic(ty.get_discriminant_type().unwrap());

					result
				},

				PlaceElem::SumData(variant_ty) => {
					let mut ptr = self.indirection_as_pointer(local);

					if matches!(ty, Type::Tuple(TupleKind::Sum, _)) {
						ptr = self.builder.build_struct_gep(ptr, 1, "").unwrap();
					}

					ty = variant_ty.clone();

					// SumData index requires a cast to variant type
					self.builder.build_bitcast(
						ptr,
						Self::to_basic_type(self.get_llvm_type(variant_ty)).ptr_type(AddressSpace::default()),
						""
					)?
				}
			}
		}

		if props.is_ref {
			Ok(local.as_basic_value_enum())
		} else {
			self.builder.build_load(self.indirection_as_pointer(local), "")
		}
	}

	// get the pointer element of an indirection.
	//
	// pointers and references may have differing representations,
	// based on what they point to -- a pointer to a T[] will
	// actually be represented as (T*, usize) internally.
	// this function extracts the pointer element, allowing these
	// differing representations to be handled uniformly in codegen.
	// prefer this over into_pointer_value() when dealing with lvalues.

	fn indirection_as_pointer(&self, value: BasicValueEnum<'ctx>) -> PointerValue<'ctx> {
		match value {
			// for common types
			BasicValueEnum::PointerValue(ptr) => ptr,
	
			// for slice types
			BasicValueEnum::StructValue(strct) => {
				self.builder.build_extract_value(strct, 0, "").unwrap().into_pointer_value()
			}

			other => panic!("unexpected pointer value: {other}")
		}
	}

	fn generate_prototype(&mut self, t: &CIRFunction) -> LLVMResult<FunctionType<'ctx>> {
		let types_mapped: Vec<_> = t.variables[0..t.arg_count]
			.iter()
			.map(|(ty, props, _)| {
				if self.pass_by_ptr(ty, props) {
					Self::to_basic_metadata_type(self.get_llvm_type(&ty.ptr_type(PtrKind::Raw)))
				} else {
					Self::to_basic_metadata_type(self.get_llvm_type(ty))
				}
			})
			.collect();

		let ret = if self.pass_by_ptr(&t.ret.1, &t.ret.0) {
			self.get_llvm_type(&t.ret.1.ptr_type(PtrKind::Raw))
		} else {
			self.get_llvm_type(&t.ret.1)
		};

		Ok(match ret {
			AnyTypeEnum::ArrayType(a) => a.fn_type(&types_mapped, t.is_variadic),
			AnyTypeEnum::FloatType(f) => f.fn_type(&types_mapped, t.is_variadic),
			AnyTypeEnum::IntType(i) => i.fn_type(&types_mapped, t.is_variadic),
			AnyTypeEnum::PointerType(p) => p.fn_type(&types_mapped, t.is_variadic),
			AnyTypeEnum::StructType(s) => s.fn_type(&types_mapped, t.is_variadic),
			AnyTypeEnum::VectorType(v) => v.fn_type(&types_mapped, t.is_variadic),
			AnyTypeEnum::VoidType(v) => v.fn_type(&types_mapped, t.is_variadic),

			_ => panic!(),
		})
	}

	fn create_entry_block_alloca<T: BasicType<'ctx>>(
		&self,
		name: &str,
		ty: T,
	) -> LLVMResult<PointerValue<'ctx>> {
		let builder = self.context.create_builder();
		let entry = self.fn_value_opt.unwrap().get_first_basic_block().unwrap();

		match entry.get_first_instruction() {
			Some(first_instr) => builder.position_before(&first_instr),
			None => builder.position_at_end(entry),
		};

		builder.build_alloca(ty, name)
	}

	fn to_basic_value(t: AnyValueEnum<'ctx>) -> Rc<dyn BasicValue<'ctx> + 'ctx> {
		match t {
			AnyValueEnum::ArrayValue(a) => Rc::new(a),
			AnyValueEnum::FloatValue(f) => Rc::new(f),
			AnyValueEnum::IntValue(i) => Rc::new(i),
			AnyValueEnum::PointerValue(p) => Rc::new(p),
			AnyValueEnum::StructValue(s) => Rc::new(s),
			AnyValueEnum::VectorValue(v) => Rc::new(v),
			_ => panic!(),
		}
	}

	fn to_basic_type(t: AnyTypeEnum<'ctx>) -> BasicTypeEnum<'ctx> {
		match t {
			AnyTypeEnum::ArrayType(a) => a.as_basic_type_enum(),
			AnyTypeEnum::FloatType(f) => f.as_basic_type_enum(),
			AnyTypeEnum::IntType(i) => i.as_basic_type_enum(),
			AnyTypeEnum::PointerType(p) => p.as_basic_type_enum(),
			AnyTypeEnum::StructType(s) => s.as_basic_type_enum(),
			AnyTypeEnum::VectorType(v) => v.as_basic_type_enum(),
			AnyTypeEnum::VoidType(_) => panic!("attempted to convert VoidType to BasicTypeEnum!"),
			AnyTypeEnum::FunctionType(_) => {
				panic!("attempted to convert FunctionType to BasicTypeEnum!")
			}
		}
	}

	fn to_basic_metadata_type(t: AnyTypeEnum<'ctx>) -> BasicMetadataTypeEnum<'ctx> {
		match t {
			AnyTypeEnum::ArrayType(a) => BasicMetadataTypeEnum::ArrayType(a),
			AnyTypeEnum::FloatType(f) => BasicMetadataTypeEnum::FloatType(f),
			AnyTypeEnum::IntType(i) => BasicMetadataTypeEnum::IntType(i),
			AnyTypeEnum::PointerType(p) => BasicMetadataTypeEnum::PointerType(p),
			AnyTypeEnum::StructType(s) => BasicMetadataTypeEnum::StructType(s),
			AnyTypeEnum::VectorType(v) => BasicMetadataTypeEnum::VectorType(v),
			_ => panic!(),
		}
	}

	fn to_basic_metadata_value(t: AnyValueEnum<'ctx>) -> BasicMetadataValueEnum<'ctx> {
		match t {
			AnyValueEnum::ArrayValue(a) => BasicMetadataValueEnum::ArrayValue(a),
			AnyValueEnum::FloatValue(f) => BasicMetadataValueEnum::FloatValue(f),
			AnyValueEnum::IntValue(i) => BasicMetadataValueEnum::IntValue(i),
			AnyValueEnum::PointerValue(p) => BasicMetadataValueEnum::PointerValue(p),
			AnyValueEnum::StructValue(s) => BasicMetadataValueEnum::StructValue(s),
			AnyValueEnum::VectorValue(v) => BasicMetadataValueEnum::VectorValue(v),
			_ => panic!(),
		}
	}

	fn get_llvm_type(&self, ty: &Type) -> AnyTypeEnum<'ctx> {
		match ty {
			Type::Basic(basic) => match basic {
				Basic::Integral { size, .. } => match size {
					IntSize::IAddr => self
						.context
						.ptr_sized_int_type(&self.target_machine.get_target_data(), None),

					IntSize::I64 => self.context.i64_type(),
					IntSize::I32 => self.context.i32_type(),
					IntSize::I16 => self.context.i16_type(),
					IntSize::I8 => self.context.i8_type(),
				}
				.as_any_type_enum(),

				Basic::Float {
					size: FloatSize::F64,
				} => self.context.f64_type().as_any_type_enum(),
				Basic::Float {
					size: FloatSize::F32,
				} => self.context.f32_type().as_any_type_enum(),

				Basic::Bool => self.context.bool_type().as_any_type_enum(),
				Basic::Void => self.context.void_type().as_any_type_enum(),
			},

			Type::Never => self.context.void_type().as_any_type_enum(),

			Type::Array(arr_ty, size) => Self::to_basic_type(self.get_llvm_type(arr_ty))
				.array_type(
					if let ConstExpr::Result(ConstValue::Integral(e, _)) = &*size.read().unwrap() {
						*e as u32
					} else {
						panic!()
					},
				)
				.as_any_type_enum(),

			// Hack to make some ABI/optimization code work. Don't actually use this in codegen
			Type::Slice(slicee) => Self::to_basic_type(self.get_llvm_type(slicee))
				.ptr_type(AddressSpace::default())
				.as_any_type_enum(),

			Type::Pointer(pointee, _) => {
				match &**pointee {
					Type::Slice(slicee) => self
						.slice_type(&Self::to_basic_type(self.get_llvm_type(slicee)))
						.as_any_type_enum(),

					// void* isn't valid in LLVM, so we generate an i8* type instead
					Type::Basic(Basic::Void) => self
						.context
						.i8_type()
						.ptr_type(AddressSpace::default())
						.as_any_type_enum(),

					_ => Self::to_basic_type(self.get_llvm_type(pointee))
						.ptr_type(AddressSpace::default())
						.as_any_type_enum(),
				}
			}

			Type::TypeRef { def, .. } => {
				let ir_typename = ty.get_ir_typename();
				let ty = &self.type_map[&ir_typename];
				
				if ty.into_struct_type().is_opaque() {
					self.generate_type_body(&ir_typename, &def.upgrade().unwrap().read().unwrap());
				}

				self.type_map[&ir_typename]
			}

			Type::Tuple(kind, types) => {
				let types_mapped: Vec<_> = types
					.iter()
					.map(|ty| Self::to_basic_type(self.get_llvm_type(ty)))
					.collect();

				match kind {
					TupleKind::Product => self
						.context
						.struct_type(&types_mapped, false)
						.as_any_type_enum(),

					// For the purposes of codegen, a newtype is
					// identical to the type it wraps around
					TupleKind::Newtype => {
						assert!(types.len() == 1);
						self.get_llvm_type(&types[0])
					}

					// The unit type has exactly one value, but
					// we might as well use an i8 in codegen
					TupleKind::Empty => self.context.i8_type().as_any_type_enum(),

					TupleKind::Sum => {
						let discriminant = self.context.i32_type(); // TODO: Adapt to variant count
						let target_data = self.target_machine.get_target_data();

						let biggest_variant = types_mapped
							.iter()
							.map(|ty| target_data.get_store_size(ty))
							.max()
							.unwrap();

						self.context
							.struct_type(
								&[
									discriminant.as_basic_type_enum(),
									self.context
										.i8_type()
										.vec_type(biggest_variant as u32)
										.as_basic_type_enum(),
								],
								false,
							)
							.as_any_type_enum()
					}
				}
			}

			Type::Function(ret, args) => {
				// TODO: vararg support
				let args_mapped = args
					.iter()
					.map(|(_, ty)| Self::to_basic_metadata_type(self.get_llvm_type(ty)))
					.collect::<Vec<_>>();

				match self.get_llvm_type(ret) {
					AnyTypeEnum::VoidType(ty) => ty.fn_type(&args_mapped, false),
					ty => Self::to_basic_type(ty).fn_type(&args_mapped, false),
				}
				.ptr_type(AddressSpace::default())
				.as_any_type_enum()
			}

			Type::TypeParam(_) => panic!("unexpected TypeParam in codegen!"),

			Type::Unresolved { .. } | Type::Infer(_) => panic!(),
		}
	}

	fn slice_type(&self, ty: &dyn BasicType<'ctx>) -> StructType<'ctx> {
		self.context.struct_type(
			&[
				BasicTypeEnum::PointerType(ty.ptr_type(AddressSpace::default())),
				BasicTypeEnum::IntType(self.context.i64_type()),
			],
			true,
		)
	}

	fn get_undef(&self, ty: &BasicTypeEnum<'ctx>) -> BasicValueEnum<'ctx> {
		match ty {
			BasicTypeEnum::ArrayType(a) => a.get_undef().as_basic_value_enum(),
			BasicTypeEnum::FloatType(f) => f.get_undef().as_basic_value_enum(),
			BasicTypeEnum::IntType(i) => i.get_undef().as_basic_value_enum(),
			BasicTypeEnum::PointerType(p) => p.get_undef().as_basic_value_enum(),
			BasicTypeEnum::StructType(s) => s.get_undef().as_basic_value_enum(),
			BasicTypeEnum::VectorType(v) => v.get_undef().as_basic_value_enum(),
		}
	}

	fn to_int_predicate(op: &Operator, signed: bool) -> IntPredicate {
		if signed {
			match op {
				Operator::Eq => IntPredicate::EQ,
				Operator::NotEq => IntPredicate::NE,
				Operator::Greater => IntPredicate::SGT,
				Operator::GreaterEq => IntPredicate::SGE,
				Operator::Less => IntPredicate::SLT,
				Operator::LessEq => IntPredicate::SLE,

				_ => panic!(),
			}
		} else {
			match op {
				Operator::Eq => IntPredicate::EQ,
				Operator::NotEq => IntPredicate::NE,
				Operator::Greater => IntPredicate::UGT,
				Operator::GreaterEq => IntPredicate::UGE,
				Operator::Less => IntPredicate::ULT,
				Operator::LessEq => IntPredicate::ULE,

				_ => panic!(),
			}
		}
	}

	fn to_float_predicate(op: &Operator) -> FloatPredicate {
		match op {
			Operator::Eq => FloatPredicate::OEQ,
			Operator::NotEq => FloatPredicate::ONE,
			Operator::Greater => FloatPredicate::OGT,
			Operator::GreaterEq => FloatPredicate::OGE,
			Operator::Less => FloatPredicate::OLT,
			Operator::LessEq => FloatPredicate::OLE,

			_ => panic!(),
		}
	}

	fn get_attribute(&self, name: &str) -> Attribute {
		self.context
			.create_enum_attribute(Attribute::get_named_enum_kind_id(name), 0)
	}

	fn pass_by_ptr(&self, _ty: &Type, props: &BindingProps) -> bool {
		/*
		// don't pass by pointer if binding is not a reference, or if it's unsafe
		if !props.is_ref || props.is_unsafe {
			return false;
		}

		// mutable references and DSTs are passed by pointer
		if props.is_mut || ty.is_dyn_sized() {
			return true;
		}

		let target_data = get_target_machine().get_target_data();
		let store_size = target_data.get_store_size(&self.get_llvm_type(ty));

		// determine how shared reference should be passed
		// if the data is bigger than the equivalent pointer,
		// we pass-by-pointer. else, we pass-by-value.
		store_size > target_data.get_store_size(&self.get_llvm_type(&ty.ptr_type(false)))
		*/

		// The above code is disabled for now,
		// while I work on generalized reference support
		props.is_ref
	}
	
	fn get_di_type(&mut self, ty: &Type) -> DIType<'ctx> {
		if let Some(ty) = self.di_type_map.get(ty) {
			return *ty
		}

		let ptr_size = self.target_machine.get_target_data().get_pointer_byte_size(None);

		let result = match ty {
			Type::Basic(basic) => {
				let di_builder = self.di_builder.as_ref().unwrap();

				match basic {
					Basic::Bool => di_builder.create_basic_type(
						basic.as_str(),
						8,
						dwarf_ate::BOOLEAN,
						DIFlagsConstants::PUBLIC,
					),

					Basic::Integral { signed, size } => di_builder.create_basic_type(
						basic.as_str(),
						(size.as_bytes(ptr_size as usize) * 8) as u64,
						if *signed { dwarf_ate::SIGNED } else { dwarf_ate::UNSIGNED },
						DIFlagsConstants::PUBLIC,
					),

					Basic::Float { size } => di_builder.create_basic_type(
						basic.as_str(),
						(size.as_bytes() * 8) as u64,
						dwarf_ate::FLOAT,
						DIFlagsConstants::PUBLIC,
					),

					Basic::Void => di_builder.create_basic_type(
						basic.as_str(),
						0,
						dwarf_ate::VOID,
						DIFlagsConstants::PUBLIC,
					)
				}.unwrap().as_type()
			},

			Type::TypeRef { def, .. } => {
				let def = def.upgrade().unwrap();
				let def = def.read().unwrap();

				let members = def.members
					.iter()
					.map(|(_, member, _)| self.get_di_type(member))
					.collect_vec();

				let di_builder = self.di_builder.as_ref().unwrap();
				let di_compile_unit = self.di_compile_unit.as_ref().unwrap();
				let name = def.name.to_string();
				
				// TODO: Variants

				di_builder.create_struct_type(
					di_compile_unit.get_file().as_debug_info_scope(),
					&name,
					di_compile_unit.get_file(),
					0,
					0,
					0,
					DIFlagsConstants::PUBLIC,
					None,
					&members,
					DWARFSourceLanguage::CPlusPlus as u32,
					None,
					&name
				).as_type()
			}

			Type::Pointer(pointee, _) => {
				if let Type::Slice(slicee) = &**pointee {
					let pointee = self.get_di_type(slicee);
					let size_ty = self.get_di_type(&Type::isize_type(false));
					let di_builder = self.di_builder.as_ref().unwrap();
					let di_compile_unit = self.di_compile_unit.as_ref().unwrap();
					let name = format!("[{}]*", slicee.to_string());
					
					di_builder.create_struct_type(
						di_compile_unit.get_file().as_debug_info_scope(),
						&name,
						di_compile_unit.get_file(),
						0,
						(ptr_size * 2 * 8) as u64,
						ptr_size,
						DIFlagsConstants::PUBLIC,
						None,
						&[
							pointee,
							size_ty,
						],
						DWARFSourceLanguage::CPlusPlus as u32, // idfk
						None,
						&name
					).as_type()
				} else {
					let pointee = self.get_di_type(&pointee);
					let di_builder = self.di_builder.as_ref().unwrap();

					di_builder.create_pointer_type(
						&ty.to_string(),
						pointee,
						(ptr_size * 8) as u64,
						ptr_size * 8, // FIXME: actually get alignment
						AddressSpace::default(),
					).as_type()
				}
			}

			Type::Slice(slicee) => self.get_di_type(&slicee),

			Type::Function(ret, args) => {
				let _ret = self.get_di_type(ret);
				let _args = args
					.iter()
					.map(|(_, arg)| self.get_di_type(arg))
					.collect_vec();

				self.get_di_type(&Type::void_type().ptr_type(PtrKind::Raw))
			}

			Type::Array(sub, size) => {
				let ConstExpr::Result(ConstValue::Integral(size, _)) = &*size.read().unwrap() else {
					panic!()
				};

				let sub = self.get_di_type(sub);

				self.di_builder.as_ref().unwrap().create_array_type(
					sub,
					sub.get_size_in_bits() * *size as u64,
					64,
					&[]
				).as_type()
			}

			Type::Tuple(TupleKind::Sum, types) => {
				let types = types
					.iter()
					.map(|ty| self.get_di_type(ty))
					.collect_vec();

				let disc = self.get_di_type(&Type::i32_type(true));

				let name = ty.to_string();
				let data_name = name.clone() + "-data";
				let di_compile_unit = self.di_compile_unit.as_ref().unwrap();
				let di_builder = self.di_builder.as_ref().unwrap();

				let data = di_builder.create_union_type(
					di_compile_unit.get_file().as_debug_info_scope(),
					&data_name,
					di_compile_unit.get_file(),
					0,
					0, // FIXME: ACTUALLY FIGURE OUT SIZE AND ALIGNMENT FOR THESE
					0,
					DIFlagsConstants::PUBLIC,
					&types,
					DWARFSourceLanguage::CPlusPlus as u32,
					&data_name
				).as_type();

				di_builder.create_struct_type(
					di_compile_unit.get_file().as_debug_info_scope(),
					&name,
					di_compile_unit.get_file(),
					0,
					0,
					0,
					DIFlagsConstants::PUBLIC,
					None,
					&[
						disc,
						data
					],
					DWARFSourceLanguage::CPlusPlus as u32,
					None,
					&name
				).as_type()
			}

			Type::Tuple(TupleKind::Product, types) => {
				let types = types
					.iter()
					.map(|ty| self.get_di_type(ty))
					.collect_vec();

				let name = ty.to_string();
				let di_builder = self.di_builder.as_ref().unwrap();
				let di_compile_unit = self.di_compile_unit.as_ref().unwrap();

				di_builder.create_struct_type(
					di_compile_unit.get_file().as_debug_info_scope(),
					&name,
					di_compile_unit.get_file(),
					0,
					0,
					0,
					DIFlagsConstants::PUBLIC,
					None,
					&types,
					DWARFSourceLanguage::CPlusPlus as u32,
					None,
					&name
				).as_type()
			}

			Type::Tuple(TupleKind::Empty, _) => {
				let compile_unit = self.di_compile_unit.as_ref().unwrap();

				self.di_builder.as_ref().unwrap().create_struct_type(
					compile_unit.get_file().as_debug_info_scope(),
					"()",
					compile_unit.get_file(),
					0,
					0,
					0,
					DIFlagsConstants::PUBLIC,
					None,
					&[],
					DWARFSourceLanguage::CPlusPlus as u32,
					None,
					"()"
				).as_type()
			}

			Type::Tuple(TupleKind::Newtype, ty) => self.get_di_type(&ty[0]),

			Type::Never | Type::TypeParam(_) | Type::Infer(_) | Type::Unresolved { .. } => panic!(),
		};
		
		self.di_type_map.insert(ty.clone(), result);
		result
	}
}

// Basic implementation of the Itanium C++ ABI, which is used by GCC and Clang.
// This is not complete or robust at all, but it should do for now.

fn mangle_name(name: &Identifier, func: &CIRFunction) -> String {
	let mut result = String::from("_Z");

	assert!(name.absolute);

	if !name.is_qualified() {
		result.push_str(&name.name().as_str().len().to_string());
		result.push_str(name.name().as_str());
	} else {
		result.push('N');

		if let Some(ty_qualifier) = &name.qualifier.0 {
			if let Type::TypeRef { def, .. } = &**ty_qualifier {
				let def = def.upgrade().unwrap();
				let typename = &def.read().unwrap().name;
	
				for scope in &typename.path {
					result.push_str(&scope.as_str().len().to_string());
					result.push_str(scope.as_str());
				}	
			} else {
				mangle_type(&ty_qualifier, &mut result).unwrap();
			}
		}

		for scope in &name.path {
			result.push_str(&scope.as_str().len().to_string());
			result.push_str(scope.as_str());
		}

		result.push('E');
	}

	if func.arg_count == 0 {
		result.push('v');
	} else {
		for i in 0..func.arg_count {
			let (ty, props, _) = &func.variables[i];

			if props.is_ref {
				mangle_type(&ty.ptr_type(PtrKind::Raw), &mut result).unwrap();
			} else {
				mangle_type(&ty, &mut result).unwrap();
			}
		}
	}

	if !func.generics.is_empty() {
		result.push('I');

		for (.., param) in &func.generics.params {
			let GenericParam::Type { arg: Some(ty), .. } = param else {
				panic!() // Can't have un-monomorphized generics at this point 
			};

			mangle_type(&ty, &mut result).unwrap();
		}

		result.push('E');
	}

	result
}

fn mangle_type(ty: &Type, f: &mut impl std::fmt::Write) -> std::fmt::Result {
	match ty {
		Type::Basic(b) => write!(f, "{}", mangle_basic(b)),

		Type::Pointer(pointee, kind) => {
			write!(f, "P")?;
				
			// compliant-ish? this is all so hacky lol
			match kind {
				PtrKind::Shared => write!(f, "K")?,
				PtrKind::Unique => write!(f, "r")?,
				PtrKind::Raw => {},
			}
			
			if let Type::Slice(slicee) = &**pointee {
				mangle_type(slicee, f)?;
				write!(f, "y")?;
			} else {
				mangle_type(pointee, f)?;
			}
			
			Ok(())
		}

		Type::TypeRef { def, .. } => {
			let name = def.upgrade().unwrap().read().unwrap().name.to_string();
			write!(f, "{}{name}", name.len())
		}

		Type::Function(ret, args) => {
			write!(f, "PF")?;

			mangle_type(ret, f)?;

			for (_, arg) in args {
				mangle_type(arg, f)?;
			}
			Ok(())
		}

		Type::Slice(slicee) => {
			// note: this is pretty nonsensical in C++ terms. probably not interop-viable
			//panic!("encountered Type::Slice without indirection!"),
			write!(f, "A_")?;
			mangle_type(slicee, f)
		}

		_ => todo!(),
	}
}

// See https://itanium-cxx-abi.github.io/cxx-abi/abi.html#mangle.builtin-type
fn mangle_basic(b: &Basic) -> &str {
	match b {
		Basic::Bool => "b",

		Basic::Integral { signed, size } => {
			if *signed {
				match size {
					// FIXME: figure this out properly
					IntSize::IAddr => "x",

					IntSize::I64 => "x",
					IntSize::I32 => "i",
					IntSize::I16 => "s",
					IntSize::I8 => "c",
				}
			} else {
				match size {
					// FIXME: ditto
					IntSize::IAddr => "y",

					IntSize::I64 => "y",
					IntSize::I32 => "j",
					IntSize::I16 => "t",
					IntSize::I8 => "h",
				}
			}
		}

		Basic::Float { size } => match size {
			FloatSize::F64 => "d",
			FloatSize::F32 => "f",
		},

		Basic::Void => "v",
	}
}