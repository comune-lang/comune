use crate::parser::ast::{ASTElem, ASTNode};
use crate::parser::controlflow::ControlFlow;
use crate::parser::expression::{Expr, Atom, Operator};
use crate::parser::types::{Type, Basic, InnerType};

use inkwell::IntPredicate;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{AnyTypeEnum, BasicTypeEnum, FunctionType, BasicMetadataTypeEnum, AnyType, BasicType};
use inkwell::values::{AnyValueEnum, FunctionValue, BasicValue, BasicValueEnum, AnyValue};


// This shit is a mess of enum conversions. hat  it

type LLVMResult<T> = Result<T, String>;

pub struct LLVMBackend<'ctx> {
	pub context: &'ctx Context,
	pub module: Module<'ctx>,
	pub builder: Builder<'ctx>,
	pub fn_value_opt: Option<FunctionValue<'ctx>>,
}


impl<'ctx> LLVMBackend<'ctx> {

	pub fn generate_fn(&mut self, name: String, t: &Type, body: &Option<ASTElem>) -> LLVMResult<FunctionValue> {
		let fn_t = self.generate_prototype(t)?;
		let fn_v = self.module.add_function(name.as_str(), fn_t, None);
		let entry = self.context.append_basic_block(fn_v, "entry");

		self.builder.position_at_end(entry);

		self.fn_value_opt = Some(fn_v);
	
		if let Some(body) = body {
			self.generate_node(body)?;
		}

		self.builder.build_return(None);

		Ok(fn_v)
	}

	fn generate_node(&self, elem: &ASTElem) -> LLVMResult<Option<Box<dyn BasicValue<'ctx>>>> {
		let mut ret = None;

		match &elem.node {
			ASTNode::Block(elems) => {
				for elem in elems {
					let node_ret = self.generate_node(elem)?;
					if node_ret.is_some() {
						ret = node_ret;
					}
				}
			},
			
			ASTNode::Expression(e) => {
				self.generate_expr(&e, elem.type_info.borrow().as_ref().unwrap()); 
			},

			ASTNode::Declaration(t, n, e) => {

			},
			ASTNode::ControlFlow(ctrl) => {
				self.generate_control_flow(ctrl.as_ref())?;
			},
		};

		Ok(ret)
	}

	fn generate_prototype(&self, t: &Type) -> LLVMResult<FunctionType<'ctx>> {
		if let InnerType::Function(ret, args) = &t.inner {

			let types_mapped: Vec<_> = args.iter().map(
				|t| LLVMBackend::to_basic_metadata_enum(self.get_llvm_type(t.as_ref())).unwrap()
			).collect();

			Ok(match self.get_llvm_type(&ret).as_any_type_enum() {
				AnyTypeEnum::ArrayType(a) => a.fn_type(&types_mapped, false),
				AnyTypeEnum::FloatType(f) => f.fn_type(&types_mapped, false),
				AnyTypeEnum::IntType(i) => i.fn_type(&types_mapped, false),
				AnyTypeEnum::PointerType(p) => p.fn_type(&types_mapped, false),
				AnyTypeEnum::StructType(s) => s.fn_type(&types_mapped, false),
				AnyTypeEnum::VectorType(v) => v.fn_type(&types_mapped, false),

				_ => panic!()
			})
		} else {
			panic!()
		}
	}

	fn generate_control_flow(&self, ctrl: &ControlFlow) -> LLVMResult<Option<Box<dyn AnyValue<'ctx> + 'ctx>>> {
		match ctrl {
			ControlFlow::If { cond, body, else_body } => {
				let parent = self.fn_value_opt.unwrap();

				let expr;
				if let ASTNode::Expression(e) = &cond.node { expr = e; } else { unreachable!(); }

				let cond = self.generate_expr(&expr, cond.type_info.borrow().as_ref().unwrap_or(&Type::from_basic(Basic::VOID)));
				let cond = self.builder.build_int_compare(IntPredicate::NE, cond.into_int_value(), self.context.i64_type().const_zero(), "ifcond");
				
				let then_bb = self.context.append_basic_block(parent, "then");
				let else_bb = self.context.append_basic_block(parent, "else");
				let cont_bb = self.context.append_basic_block(parent, "ifcont");

				self.builder.build_conditional_branch(cond, then_bb, else_bb);
				
				// Build then block
				self.builder.position_at_end(then_bb);
				let then_val = self.generate_node(body)?;
				self.builder.build_unconditional_branch(cont_bb);

				let then_bb = self.builder.get_insert_block().unwrap();
				
				// Build else block
				self.builder.position_at_end(else_bb);
				let mut else_val = None;

				if let Some(else_body) = else_body {
					else_val = Some(self.generate_node(else_body)?);
				}
				self.builder.build_unconditional_branch(cont_bb);

				let else_bb = self.builder.get_insert_block().unwrap();


				// Emit merge block
				self.builder.position_at_end(cont_bb);

				let phi = self.builder.build_phi(self.context.i8_type(), "iftmp");
				

				let mut phi_vals = vec![];
				
				if then_val.is_some() {
					phi_vals.push((then_val.as_ref().unwrap().as_ref(), then_bb));
				}

				if else_val.is_some() && else_val.as_ref().unwrap().is_some() {
					phi_vals.push((else_val.as_ref().unwrap().as_ref().unwrap().as_ref(), else_bb));
				}
				
				phi.add_incoming(&phi_vals);
	
				Ok(Some(Box::new(phi.as_basic_value())))
			},

			ControlFlow::While { cond, body } => todo!(),
			ControlFlow::For { init, cond, iter, body } => todo!(),

			ControlFlow::Return { expr } => {
				if let Some(expr) = expr {
					let expr_inner = match &expr.node {
						ASTNode::Expression(expr_inner) => expr_inner,
						_ => panic!(), 
					};

					let e = LLVMBackend::to_basic_value(Box::new(self.generate_expr(expr_inner, expr.type_info.borrow().as_ref().unwrap())));

					Ok(Some(Box::new(self.builder.build_return(Some(e.as_ref())))))
				} else {
					Ok(Some(Box::new(self.builder.build_return(None))))
				}
				
			},
			ControlFlow::Break => todo!(),
			ControlFlow::Continue => todo!(),
		}
	}



	fn generate_expr(&self, expr: &Expr, t: &Type) -> AnyValueEnum<'ctx> {
		match expr {
			Expr::Atom(atom, _meta) => {
				match atom {
					Atom::IntegerLit(i) => AnyValueEnum::IntValue(self.context.i32_type().const_int(*i as u64, false)),
					Atom::BoolLit(b) => AnyValueEnum::IntValue(self.context.i8_type().const_int(if *b { 1 } else { 0 }, false)),
					Atom::FloatLit(f) => AnyValueEnum::FloatValue(self.context.f32_type().const_float(*f)),
					Atom::StringLit(_) => todo!(),
					Atom::Variable(_) => todo!(), // might have to merge code generation with type validation, or store types in ASTElem
					Atom::ArrayLit(_) => todo!(),
					Atom::FnCall { name, args } => todo!(),
				}
			},
			Expr::Cons(op, elems, _meta) => 
			{
				let lhs = &elems[0];
				let rhs = &elems[1];
				match &t.inner {
					crate::parser::types::InnerType::Basic(b) => {
						match b { //self.builder.build_int_add(lhs, rhs, name)
							
							Basic::ISIZE | Basic::USIZE | Basic::I64 | Basic::U64 | Basic::I32 | Basic::U32 | Basic::I16 | Basic::U16 | Basic::I8 | Basic::U8 | Basic::CHAR => {
								let lhs = self.generate_expr(lhs, t).into_int_value();
								let rhs = self.generate_expr(rhs, t).into_int_value();

								AnyValueEnum::IntValue(
									match op {
										Operator::Add => self.builder.build_int_add(lhs, rhs, "iadd"),
										Operator::Sub => self.builder.build_int_sub(lhs, rhs, "isub"),
										Operator::Mult => self.builder.build_int_mul(lhs, rhs, "imul"),
										Operator::Div => self.builder.build_int_signed_div(lhs, rhs, "idiv"), // TODO: Add unsigned

										_ => todo!(),
									}
								)
							},
							Basic::F64 | Basic::F32 => {
								let lhs = self.generate_expr(lhs, t).into_float_value();
								let rhs = self.generate_expr(rhs, t).into_float_value();

								AnyValueEnum::FloatValue(
									match op {
										Operator::Add => self.builder.build_float_add(lhs, rhs, "fadd"),
										Operator::Sub => self.builder.build_float_sub(lhs, rhs, "fsub"),
										Operator::Mult => self.builder.build_float_mul(lhs, rhs, "fmul"),
										Operator::Div => self.builder.build_float_div(lhs, rhs, "fdiv"),

										_ => todo!(),
									}
								)
	
							},
							Basic::BOOL => todo!(),
							Basic::VOID => todo!(),
						}
					},
					InnerType::Alias(_, _) => todo!(),
					InnerType::Aggregate(_) => todo!(),
					InnerType::Pointer(_) => todo!(),
					InnerType::Function(_, _) => todo!(),
					InnerType::Unresolved(_) => todo!(),
				}
			},
		}
	}

	fn to_basic_value(t: Box<dyn AnyValue<'ctx> + 'ctx>) -> Box<dyn BasicValue<'ctx> + 'ctx> {
		match (*t).as_any_value_enum() {
			AnyValueEnum::ArrayValue(a) => Box::new(a),
			AnyValueEnum::FloatValue(f) => Box::new(f),
			AnyValueEnum::IntValue(i) => Box::new(i),
			AnyValueEnum::PointerValue(p) => Box::new(p),
			AnyValueEnum::StructValue(s) => Box::new(s),
			AnyValueEnum::VectorValue(v) => Box::new(v),
			_ => panic!(),
		}
	}

	fn to_basic_type(t: Box<dyn AnyType<'ctx> + 'ctx>) -> Box<dyn BasicType<'ctx> + 'ctx> {
		match (*t).as_any_type_enum() {
			AnyTypeEnum::ArrayType(a) => Box::new(a),
			AnyTypeEnum::FloatType(f) => Box::new(f),
			AnyTypeEnum::IntType(i) => Box::new(i),
			AnyTypeEnum::PointerType(p) => Box::new(p),
			AnyTypeEnum::StructType(s) => Box::new(s),
			AnyTypeEnum::VectorType(v) => Box::new(v),
			_ => panic!(),
		}
	}

	fn to_basic_metadata_enum(t: Box<dyn AnyType<'ctx> + 'ctx>) -> Option<BasicMetadataTypeEnum<'ctx>> {
		match t.as_any_type_enum() {
			AnyTypeEnum::ArrayType(a) => Some(BasicMetadataTypeEnum::ArrayType(a)),
			AnyTypeEnum::FloatType(f) => Some(BasicMetadataTypeEnum::FloatType(f)),
			AnyTypeEnum::IntType(i) => Some(BasicMetadataTypeEnum::IntType(i)),
			AnyTypeEnum::PointerType(p) => Some(BasicMetadataTypeEnum::PointerType(p)),
			AnyTypeEnum::StructType(s) => Some(BasicMetadataTypeEnum::StructType(s)),
			AnyTypeEnum::VectorType(v) => Some(BasicMetadataTypeEnum::VectorType(v)),
			AnyTypeEnum::VoidType(_) => None,
			AnyTypeEnum::FunctionType(_) => None,

		}
	}
	
	fn get_llvm_type(&self, t: &Type) -> Box<dyn AnyType<'ctx> + 'ctx> {
		match &t.inner {
			InnerType::Basic(b) => match b {
				Basic::I64 | Basic::U64 =>				Box::new(self.context.i64_type()),
				Basic::I32 | Basic::U32 =>				Box::new(self.context.i32_type()),
				Basic::I16 | Basic::U16 =>				Box::new(self.context.i16_type()),
				Basic::I8 | Basic::U8 | Basic::CHAR =>	Box::new(self.context.i8_type()),
				Basic::ISIZE | Basic::USIZE => 			Box::new(self.context.i64_type()),
				Basic::F64 => 							Box::new(self.context.f64_type()),
				Basic::F32 => 							Box::new(self.context.f64_type()),
				Basic::BOOL => 							Box::new(self.context.bool_type()),
				Basic::VOID => 							Box::new(self.context.void_type()),
			},

			InnerType::Alias(_id, t) => self.get_llvm_type(t.as_ref()),

			InnerType::Aggregate(types) => {
				let types_mapped : Vec<_> = types.values().map(
					|t| LLVMBackend::to_basic_type(self.get_llvm_type(t.as_ref())).as_basic_type_enum()
				).collect();

				Box::new(self.context.struct_type(&types_mapped, false))
			},

			InnerType::Pointer(_) => todo!(),
			InnerType::Function(_, _) => todo!(),
			InnerType::Unresolved(_) => panic!(),
		}
	}

	fn convert_basic_value(&self, val: &BasicValueEnum<'ctx>, t: &BasicTypeEnum) -> Box<dyn BasicValue<'ctx> + 'ctx> {
		match t {
			BasicTypeEnum::ArrayType(_) =>		Box::new(val.into_array_value()),
			BasicTypeEnum::FloatType(_) =>		Box::new(val.into_float_value()),
			BasicTypeEnum::IntType(_) => 		Box::new(val.into_int_value()),
			BasicTypeEnum::PointerType(_) =>	Box::new(val.into_pointer_value()),
			BasicTypeEnum::StructType(_) => 	Box::new(val.into_struct_value()),
			BasicTypeEnum::VectorType(_) => 	Box::new(val.into_vector_value()),
		}
	}
}