use std::rc::Rc;

use inkwell::{targets::{TargetMachine, InitializationConfig, Target, TargetTriple}, context::Context, module::{Module, Linkage}, values::{FunctionValue, AnyValue, BasicValue, AnyValueEnum, PointerValue, BasicValueEnum, IntValue, StructValue, BasicMetadataValueEnum}, builder::Builder, types::{AnyType, BasicMetadataTypeEnum, FunctionType, AnyTypeEnum, BasicTypeEnum, BasicType, StructType, IntType}, basic_block::BasicBlock, AddressSpace, GlobalVisibility, FloatPredicate, IntPredicate};

use crate::{cir::{CIRType, CIRFunction, CIRModule, CIRStmt, RValue, LValue, PlaceElem, Operand}, semantic::{types::Basic, expression::Operator, namespace::Identifier}};

pub fn get_target_machine() -> TargetMachine {
	Target::initialize_x86(&InitializationConfig::default());
	let target = Target::from_name("x86-64").unwrap();

	target
		.create_target_machine(
			&TargetTriple::create("x86_64-pc-linux-gnu"),
			"x86-64",
			"+avx2",
			inkwell::OptimizationLevel::Aggressive,
			inkwell::targets::RelocMode::Default,
			inkwell::targets::CodeModel::Default,
		)
		.unwrap()
}

type LLVMResult<T> = Result<T, String>;

pub struct LLVMBackend<'ctx> {
	pub context: &'ctx Context,
	pub module: Module<'ctx>,
	builder: Builder<'ctx>,
	fn_value_opt: Option<FunctionValue<'ctx>>,
	type_map: Vec<Rc<dyn AnyType<'ctx> + 'ctx>>,
	blocks: Vec<BasicBlock<'ctx>>,
	variables: Vec<PointerValue<'ctx>>,
}

impl<'ctx> LLVMBackend<'ctx> {
	pub fn new(context: &'ctx Context, module_name: &str) -> Self {
		Self {
			context,
			module: context.create_module(module_name),
			builder: context.create_builder(),
			fn_value_opt: None,
			type_map: vec![],
			blocks: vec![],
			variables: vec![],
		}
	} 

	pub fn compile_module(&mut self, module: &CIRModule) -> LLVMResult<()> {
		for func in &module.functions {
			self.register_fn(func.0, func.1)?;
		}

		for func in &module.functions {
			self.generate_fn(func.0, func.1)?;
		}

		Ok(())
	}

	pub fn generate_libc_bindings(&self) {
		let exit_t = self.context.void_type().fn_type(
			&[BasicMetadataTypeEnum::IntType(self.context.i32_type())],
			false,
		);

		self.module.add_function("_exit", exit_t, Some(Linkage::External));
	}

	fn register_fn(&mut self, name: &Identifier, t: &CIRFunction) -> LLVMResult<FunctionValue> {
		let fn_t = self.generate_prototype(t)?;
		let fn_v = self.module.add_function(name.resolved.as_ref().unwrap(), fn_t, None);

		Ok(fn_v)
	}

	fn generate_fn(&mut self, name: &Identifier, t: &CIRFunction) -> LLVMResult<FunctionValue> {
		let fn_v = self.module.get_function(name.resolved.as_ref().unwrap()).unwrap();

		self.fn_value_opt = Some(fn_v);

		for i in 0..t.variables.len() {
			let ty = Self::to_basic_type(self.get_llvm_type(&t.variables[i].0));
			self.variables.push(self.create_entry_block_alloca(&format!("_{i}"), ty.as_basic_type_enum()));
		}

		for i in 0..t.blocks.len() {
			self.blocks.push(self.context.append_basic_block(self.fn_value_opt.unwrap(), &format!("bb{i}")));
		}

		for i in 0..t.blocks.len() {
			let block = &t.blocks[i];

			self.builder.position_at_end(self.blocks[i]);

			for stmt in block {
				match stmt {
        			CIRStmt::Expression(expr) => {
						self.generate_rvalue(expr);
					},

        			CIRStmt::Assignment(lval, expr) => {
						self.builder.build_store(self.generate_lvalue(lval), self.generate_rvalue(expr).as_basic_value_enum());
					},

        			CIRStmt::Jump(block) => { 
						self.builder.build_unconditional_branch(self.blocks[*block]); 
					},

        			CIRStmt::Branch(cond, a, b) => {
						let cond_ir = self.generate_rvalue(cond).as_basic_value_enum().into_int_value();
						self.builder.build_conditional_branch(cond_ir, self.blocks[*a], self.blocks[*b]);
					},

        			CIRStmt::Return(expr) => {
						if let Some(expr) = expr {
							self.builder.build_return(Some(&*self.generate_rvalue(&expr)));
						} else {
							self.builder.build_return(None);
						}
					},
    			}
			}
		}

		self.blocks.clear();
		self.variables.clear();

		Ok(self.fn_value_opt.unwrap())
	}

	fn generate_rvalue(&self, expr: &RValue) -> Rc<dyn BasicValue<'ctx> + 'ctx> {
		Self::to_basic_value(self.generate_expr(expr))
	}

	fn generate_expr(&self, expr: &RValue) -> Rc<dyn AnyValue<'ctx> + 'ctx> {
		match expr {
			RValue::Atom(ty, op_opt, atom) => {
				
				match op_opt {
					Some(Operator::Deref) => {
						let atom_ir = Self::to_basic_value(self.generate_operand(ty, atom));
						Rc::new(self.builder.build_load(atom_ir.as_basic_value_enum().into_pointer_value(), "deref").as_basic_value_enum())
					}

					Some(Operator::Ref) => {
						if let Operand::LValue(lval) = atom {
							Rc::new(self.generate_lvalue(lval))
						} else {
							panic!()
						}
					}

					// TODO: Unary minus, logical NOT, etc

					None => self.generate_operand(ty, atom),
					
					_ => panic!(),
				}
			}

			RValue::Cons([(lhs_ty, lhs), (rhs_ty, rhs)], op) => {
				let lhs_v = Self::to_basic_value(self.generate_operand(lhs_ty, lhs)).as_basic_value_enum();
				let rhs_v = Self::to_basic_value(self.generate_operand(rhs_ty, rhs)).as_basic_value_enum();
				let result;

				if lhs_ty.is_integral() {
					let lhs_i = lhs_v.into_int_value();
					let rhs_i = rhs_v.into_int_value();

					result = match op {
						Operator::Add => {
							self.builder.build_int_add(lhs_i, rhs_i, "iadd")
						}
						Operator::Sub => {
							self.builder.build_int_sub(lhs_i, rhs_i, "isub")
						}
						Operator::Mul => {
							self.builder.build_int_mul(lhs_i, rhs_i, "imul")
						}
						Operator::Div => {
							if lhs_ty.is_signed() {
								self.builder.build_int_signed_div(lhs_i, rhs_i, "idiv")
							} else {
								self.builder
									.build_int_unsigned_div(lhs_i, rhs_i, "udiv")
							}
						}

						_ => panic!(),
					}
					.as_basic_value_enum();
				} else if lhs_ty.is_floating_point() {
					let lhs_f = lhs_v.into_float_value();
					let rhs_f = rhs_v.into_float_value();

					result = match op {
						Operator::Add => {
							self.builder.build_float_add(lhs_f, rhs_f, "fadd")
						}
						Operator::Sub => {
							self.builder.build_float_sub(lhs_f, rhs_f, "fsub")
						}
						Operator::Mul => {
							self.builder.build_float_mul(lhs_f, rhs_f, "fmul")
						}
						Operator::Div => {
							self.builder.build_float_div(lhs_f, rhs_f, "fdiv")
						}

						// Relational operators
						_ => panic!(),
					}
					.as_basic_value_enum()
				} else if lhs_ty.is_boolean() {
					if lhs_v.is_int_value() {
						let lhs_i = lhs_v.into_int_value();
						let rhs_i = rhs_v.into_int_value();

						result = self
							.builder
							.build_int_compare(
								Self::to_int_predicate(
									&op,
									lhs_ty.is_signed(),
								),
								lhs_i,
								rhs_i,
								"icomp",
							)
							.as_basic_value_enum();
					} else if lhs_v.is_float_value() {
						let lhs_f = lhs_v.into_float_value();
						let rhs_f = rhs_v.into_float_value();

						result = self
							.builder
							.build_float_compare(
								Self::to_float_predicate(op),
								lhs_f,
								rhs_f,
								"fcomp",
							)
							.as_basic_value_enum();
					} else {
						panic!()
					}
				} else {
					panic!()
				}

				Rc::new(result)
			}
			
			RValue::Cast { from, to, val } => {
				todo!()
			}
		}
	}

	fn generate_operand(&self, ty: &CIRType, expr: &Operand) -> Rc<dyn AnyValue<'ctx> + 'ctx> {
		match expr {
			Operand::FnCall(name, args) => {
				let fn_v = self
					.module
					.get_function(name.resolved.as_ref().unwrap())
					.unwrap();

				let args_mapped: Vec<_> = args
					.iter()
					.map(|x| {
						Self::to_basic_metadata_value(self.generate_expr(x))
					})
					.collect();

				Rc::new(self.builder.build_call(fn_v, &args_mapped, "fncall"))
			},

			Operand::StringLit(s) => {
				let len = s.as_bytes().len().try_into().unwrap();
				let string_t = self.context.i8_type().array_type(len);
				let val = self.module.add_global(string_t, Some(AddressSpace::Const), ".str");
				
				val.set_visibility(GlobalVisibility::Hidden);
				val.set_linkage(Linkage::Private);
				val.set_unnamed_addr(true);

				let literal: Vec<_> = s
					.as_bytes()
					.iter()
					.map(|x| self.context.i8_type().const_int(*x as u64, false))
					.collect();

				val.set_initializer(&IntType::const_array(
					self.context.i8_type(),
					&literal,
				));

				Rc::new(
					self.slice_type(&self.context.i8_type()).const_named_struct(&[
						val.as_pointer_value().as_basic_value_enum(),
						self.context
							.i64_type()
							.const_int(len.into(), false)
							.as_basic_value_enum(),
					]),
				)
			},

			Operand::IntegerLit(i) => Rc::new(Self::to_basic_type(self.get_llvm_type(ty)).as_basic_type_enum().into_int_type().const_int(*i as u64, true)),
			Operand::FloatLit(f) => Rc::new(Self::to_basic_type(self.get_llvm_type(ty)).as_basic_type_enum().into_float_type().const_float(*f)),
			Operand::BoolLit(b) => Rc::new(self.context.bool_type().const_int(if *b { 1 } else { 0 }, false)),
			Operand::LValue(l) => Rc::new(self.builder.build_load(self.generate_lvalue(l), "lread")),
			Operand::Undef => Rc::new(self.get_llvm_type(ty).as_any_type_enum().into_struct_type().get_undef()),
		}
	}

	fn generate_lvalue(&self, expr: &LValue) -> PointerValue<'ctx> {
		let mut local = self.variables[expr.local];

		for proj in &expr.projection {
			local = match proj {
				PlaceElem::Deref => self.builder.build_load(local, "deref").as_basic_value_enum().into_pointer_value(),
				PlaceElem::Field(i) => self.builder.build_struct_gep(local, *i as u32, "field").unwrap(),
				PlaceElem::Index(expr) => unsafe { self.builder.build_gep(local, &[self.generate_rvalue(expr).as_basic_value_enum().into_int_value()], "index") },
			}
		}

		todo!()
	}

	fn generate_prototype(&mut self, t: &CIRFunction) -> LLVMResult<FunctionType<'ctx>> {
		let types_mapped: Vec<_> = t.variables[0..t.arg_count]
			.iter()
			.map(|t| Self::to_basic_metadata_type(self.get_llvm_type(&t.0)))
			.collect();

		Ok(match self.get_llvm_type(&t.ret).as_any_type_enum() {
			AnyTypeEnum::ArrayType(a) => a.fn_type(&types_mapped, false),
			AnyTypeEnum::FloatType(f) => f.fn_type(&types_mapped, false),
			AnyTypeEnum::IntType(i) => i.fn_type(&types_mapped, false),
			AnyTypeEnum::PointerType(p) => p.fn_type(&types_mapped, false),
			AnyTypeEnum::StructType(s) => s.fn_type(&types_mapped, false),
			AnyTypeEnum::VectorType(v) => v.fn_type(&types_mapped, false),
			AnyTypeEnum::VoidType(v) => v.fn_type(&types_mapped, false),

			_ => panic!(),
		})
	}
	
	fn create_entry_block_alloca<T: BasicType<'ctx>>(&self, name: &str, ty: T) -> PointerValue<'ctx> {
		let builder = self.context.create_builder();
		let entry = self.fn_value_opt.unwrap().get_first_basic_block().unwrap();

		match entry.get_first_instruction() {
			Some(first_instr) => builder.position_before(&first_instr),
			None => builder.position_at_end(entry),
		};

		builder.build_alloca(ty, name)
	}

	fn to_basic_value(t: Rc<dyn AnyValue<'ctx> + 'ctx>) -> Rc<dyn BasicValue<'ctx> + 'ctx> {
		match (*t).as_any_value_enum() {
			AnyValueEnum::ArrayValue(a) => Rc::new(a),
			AnyValueEnum::FloatValue(f) => Rc::new(f),
			AnyValueEnum::IntValue(i) => Rc::new(i),
			AnyValueEnum::PointerValue(p) => Rc::new(p),
			AnyValueEnum::StructValue(s) => Rc::new(s),
			AnyValueEnum::VectorValue(v) => Rc::new(v),
			_ => panic!(),
		}
	}

	fn to_basic_type(t: Rc<dyn AnyType<'ctx> + 'ctx>) -> Rc<dyn BasicType<'ctx> + 'ctx> {
		match (*t).as_any_type_enum() {
			AnyTypeEnum::ArrayType(a) => Rc::new(a),
			AnyTypeEnum::FloatType(f) => Rc::new(f),
			AnyTypeEnum::IntType(i) => Rc::new(i),
			AnyTypeEnum::PointerType(p) => Rc::new(p),
			AnyTypeEnum::StructType(s) => Rc::new(s),
			AnyTypeEnum::VectorType(v) => Rc::new(v),
			_ => panic!(),
		}
	}

	fn to_basic_metadata_type(t: Rc<dyn AnyType<'ctx> + 'ctx>) -> BasicMetadataTypeEnum<'ctx> {
		match t.as_any_type_enum() {
			AnyTypeEnum::ArrayType(a) => BasicMetadataTypeEnum::ArrayType(a),
			AnyTypeEnum::FloatType(f) => BasicMetadataTypeEnum::FloatType(f),
			AnyTypeEnum::IntType(i) => BasicMetadataTypeEnum::IntType(i),
			AnyTypeEnum::PointerType(p) => BasicMetadataTypeEnum::PointerType(p),
			AnyTypeEnum::StructType(s) => BasicMetadataTypeEnum::StructType(s),
			AnyTypeEnum::VectorType(v) => BasicMetadataTypeEnum::VectorType(v),
			_ => panic!(),
		}
	}

	fn to_basic_metadata_value(t: Rc<dyn AnyValue<'ctx> + 'ctx>) -> BasicMetadataValueEnum<'ctx> {
		match t.as_any_value_enum() {
			AnyValueEnum::ArrayValue(a) => BasicMetadataValueEnum::ArrayValue(a),
			AnyValueEnum::FloatValue(f) => BasicMetadataValueEnum::FloatValue(f),
			AnyValueEnum::IntValue(i) => BasicMetadataValueEnum::IntValue(i),
			AnyValueEnum::PointerValue(p) => BasicMetadataValueEnum::PointerValue(p),
			AnyValueEnum::StructValue(s) => BasicMetadataValueEnum::StructValue(s),
			AnyValueEnum::VectorValue(v) => BasicMetadataValueEnum::VectorValue(v),
			_ => panic!(),
		}
	}

	fn get_llvm_type(&self, ty: &CIRType) -> Rc<dyn AnyType<'ctx> + 'ctx> {
		match ty {
			CIRType::Basic(basic) => match basic {
				Basic::INTEGRAL { size_bytes, .. } => Rc::new(match size_bytes {
					8 => self.context.i64_type(),
					4 => self.context.i32_type(),
					2 => self.context.i16_type(),
					1 => self.context.i8_type(),
					_ => panic!(),
				}),

				Basic::SIZEINT { .. } => Rc::new(
					self.context
						.ptr_sized_int_type(&get_target_machine().get_target_data(), None),
				),

				Basic::FLOAT { size_bytes } => Rc::new(
					if *size_bytes == 8 {
						self.context.f64_type()
					} else {
						self.context.f32_type()
					}
				),

				Basic::CHAR => Rc::new(self.context.i8_type()),
				Basic::BOOL => Rc::new(self.context.bool_type()),
				Basic::VOID => Rc::new(self.context.void_type()),
				Basic::STR => Rc::new(self.slice_type(&self.context.i8_type())),
			}

			CIRType::Array(arr_ty, size) => Rc::new(Self::to_basic_type(self.get_llvm_type(arr_ty)).array_type(size.iter().sum::<i128>() as u32)),
			
			CIRType::Pointer(pointee) | CIRType::Reference(pointee) => Rc::new(Self::to_basic_type(self.get_llvm_type(pointee)).ptr_type(AddressSpace::Generic)),

			CIRType::TypeRef(idx) => self.type_map[*idx].clone(),
		}
	}

	fn slice_type(&self, ty: &dyn BasicType<'ctx>) -> StructType<'ctx> {
		self.context.struct_type(
			&[
				BasicTypeEnum::PointerType(ty.ptr_type(AddressSpace::Generic)),
				BasicTypeEnum::IntType(self.context.i64_type()),
			],
			true,
		)
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
}