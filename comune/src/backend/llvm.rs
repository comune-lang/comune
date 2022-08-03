use std::cell::{RefCell, Ref};
use std::collections::HashMap;

use crate::parser::ast::{ASTElem, ASTNode};
use crate::parser::controlflow::ControlFlow;
use crate::parser::expression::{Expr, Atom, Operator};
use crate::parser::types::{Type, Basic, InnerType};

use inkwell::{IntPredicate, AddressSpace};
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Module, Linkage};
use inkwell::passes::PassManager;
use inkwell::types::{AnyTypeEnum, BasicTypeEnum, FunctionType, BasicMetadataTypeEnum, AnyType, BasicType, IntType, StructType};
use inkwell::values::{AnyValueEnum, FunctionValue, BasicValue, AnyValue, PointerValue, BasicMetadataValueEnum, BasicValueEnum};


// This shit is a mess of enum conversions. hat  it

type LLVMResult<T> = Result<T, String>;

pub struct LLVMBackend<'ctx> {
	pub context: &'ctx Context,
	pub module: Module<'ctx>,
	pub builder: Builder<'ctx>,
	pub fpm: Option<PassManager<FunctionValue<'ctx>>>,
	pub fn_value_opt: Option<FunctionValue<'ctx>>,
}

struct LLVMScope<'ctx, 'scope> {
	variables: RefCell<HashMap<String, PointerValue<'ctx>>>,
	parent: Option<&'scope LLVMScope<'ctx, 'scope>>,
}

impl<'ctx, 'scope> LLVMScope<'ctx, 'scope> {

	fn get_variable<'a>(&'a self, name: &str) -> Option<Ref<'a, PointerValue<'ctx>>> {
		// Safety: we convert the reference obtained from the guarded borrow
		// into a pointer. Dropping the reference allows us to consume the
		// original borrow guard and turn it into a new one (with the same
		// lifetime) that refers to the value inside the hashmap.
		let s = self.variables.borrow();
		let ret = s.get(name)
			.map(|v| v as *const _)
			.map(|v| Ref::map(s, |_| unsafe { &*v }));
		
		if ret.is_some() {
			ret
		} else if let Some(parent) = self.parent {
			parent.get_variable(name)
		} else {
			None
		}
	}

	fn add_variable(&self, name: &str, var: PointerValue<'ctx>) {
		self.variables.borrow_mut().insert(name.to_string(), var);
	}

	fn new() -> Self {
		LLVMScope { variables: RefCell::new(HashMap::new()), parent: None }
	}
	fn from_parent(parent: &'scope LLVMScope<'ctx, 'scope>) -> Self {
		LLVMScope { 
			variables: RefCell::new(HashMap::new()), 
			parent: Some(parent) 
		}
	}
}


impl<'ctx> LLVMBackend<'ctx> {

	
	pub fn generate_libc_bindings(&self) {
		let exit_t = self.context.void_type().fn_type(&[BasicMetadataTypeEnum::IntType(self.context.i32_type())], false);
		self.module.add_function("_exit", exit_t, Some(Linkage::External));		
	}

	pub fn register_fn(&mut self, name: String, t: &Type) -> LLVMResult<FunctionValue> {
		let fn_t = self.generate_prototype(t)?;
		let fn_v = self.module.add_function(name.as_str(), fn_t, None);

		Ok(fn_v)
	}

	pub fn generate_fn(&mut self, name: String, t: &Type, body: &Option<ASTElem>) -> LLVMResult<FunctionValue> {
		let fn_v = self.module.get_function(name.as_str()).unwrap();

		self.fn_value_opt = Some(fn_v);
		self.fpm = Some(PassManager::create(&self.module));

		if let Some(body) = body {
			let entry = self.context.append_basic_block(fn_v, "entry");
			self.builder.position_at_end(entry);

			let mut scope = LLVMScope::new();
	
			// Add parameters to variable list
			if let InnerType::Function(_ret, args) = &t.inner {
				for (i, param) in fn_v.get_param_iter().enumerate() {

					// Only add parameter to scope is it is named
					if let Some(arg_name) = &args[i].1 {

						let alloca = self.create_entry_block_alloca(&arg_name, param.get_type());
					
						self.builder.build_store(alloca, param);

						scope.add_variable(arg_name.as_str(), alloca);
					}
				}
			} else { 
				panic!(); 
			}
			
			self.generate_node(body, &mut scope)?;
		}

		
		Ok(fn_v)
	}


	fn generate_prototype(&self, t: &Type) -> LLVMResult<FunctionType<'ctx>> {
		if let InnerType::Function(ret, args) = &t.inner {

			let types_mapped: Vec<_> = args.iter().map(
				|t| LLVMBackend::to_basic_metadata_enum(self.get_llvm_type(t.0.as_ref())).unwrap()
			).collect();

			Ok(match self.get_llvm_type(&ret).as_any_type_enum() {
				AnyTypeEnum::ArrayType(a) => a.fn_type(&types_mapped, false),
				AnyTypeEnum::FloatType(f) => f.fn_type(&types_mapped, false),
				AnyTypeEnum::IntType(i) => i.fn_type(&types_mapped, false),
				AnyTypeEnum::PointerType(p) => p.fn_type(&types_mapped, false),
				AnyTypeEnum::StructType(s) => s.fn_type(&types_mapped, false),
				AnyTypeEnum::VectorType(v) => v.fn_type(&types_mapped, false),
				AnyTypeEnum::VoidType(v) => v.fn_type(&types_mapped, false),

				_ => panic!()
			})
		} else {
			panic!()
		}
	}


	fn generate_node(&self, elem: &ASTElem, scope: &LLVMScope<'ctx, '_>) -> LLVMResult<Option<Box<dyn BasicValue<'ctx> + 'ctx>>> {
		let mut ret = None;

		match &elem.node {
			ASTNode::Block(elems) => {
				let subscope = LLVMScope::from_parent(scope);

				for elem in elems {
					let node_ret = self.generate_node(elem, &subscope)?;
					if node_ret.is_some() {
						ret = node_ret;
					}
				}
			},
			
			ASTNode::Expression(e) => {
				self.generate_expr(&e, elem.type_info.borrow().as_ref().unwrap(), scope); 
			},

			ASTNode::Declaration(t, n, e) => {
				let name = n.to_string();
				let alloca = self.create_entry_block_alloca(
					&name, 
					LLVMBackend::to_basic_type(self.get_llvm_type(t)).as_basic_type_enum()
				);

				if let Some(expr) = e {
					if let ASTNode::Expression(expr) = &expr.as_ref().node {
						self.builder.build_store(alloca, LLVMBackend::into_basic_value(self.generate_expr(&expr, t, scope)).as_basic_value_enum());
					} else {
						unreachable!(); //idk
					}
				}

				scope.add_variable(&name, alloca);
			},

			ASTNode::ControlFlow(ctrl) => {
				self.generate_control_flow(ctrl.as_ref(), scope)?;
			},
		};

		Ok(ret)
	}



	fn generate_control_flow(&self, ctrl: &ControlFlow, scope: &LLVMScope<'ctx, '_>) -> LLVMResult<Option<Box<dyn AnyValue<'ctx> + 'ctx>>> {
		match ctrl {
			ControlFlow::If { cond, body, else_body } => {
				let parent = self.fn_value_opt.unwrap();

				let expr;
				if let ASTNode::Expression(e) = &cond.node { expr = e; } else { unreachable!(); }

				let cond = self.generate_expr(&expr, cond.type_info.borrow().as_ref().unwrap_or(&Type::from_basic(Basic::VOID)), scope);
				
				let cond = self.builder.build_int_compare(
					IntPredicate::NE, 
					cond.as_any_value_enum().into_int_value(), 
					self.context.bool_type().const_zero(), 
					"ifcond"
				);
				
				let then_bb = self.context.append_basic_block(parent, "then");
				let else_bb = self.context.append_basic_block(parent, "else");
				let cont_bb = self.context.append_basic_block(parent, "ifcont");

				self.builder.build_conditional_branch(cond, then_bb, else_bb);
				
				// Build then block
				self.builder.position_at_end(then_bb);
				self.generate_node(body, scope)?;
				self.builder.build_unconditional_branch(cont_bb);

				
				// Build else block
				self.builder.position_at_end(else_bb);
				if let Some(else_body) = else_body {
					self.generate_node(else_body, scope)?;
				}
				self.builder.build_unconditional_branch(cont_bb);


				self.builder.position_at_end(cont_bb);

				Ok(None)
			},


			ControlFlow::While { .. } => todo!(),


			ControlFlow::For { init, cond, iter, body } => {
				let parent = self.fn_value_opt.unwrap();
				let subscope = LLVMScope::from_parent(scope);


				if let Some(init) = init {
					self.generate_node(init, &subscope)?;
				}

				let cond_bb = self.context.append_basic_block(parent, "forcond");
				let body_bb = self.context.append_basic_block(parent, "forblock");
				let end_bb = self.context.append_basic_block(parent, "forend");
				
				self.builder.build_unconditional_branch(cond_bb);

				self.builder.position_at_end(cond_bb);

				if let Some(cond) = cond {
					if let ASTNode::Expression(expr) = &cond.node {
						let cond_expr = self.generate_expr(&expr, &cond.type_info.borrow().as_ref().unwrap(), &subscope);

						let cond_ir = self.builder.build_int_compare(
							IntPredicate::NE, 
							cond_expr.as_any_value_enum().into_int_value(), 
							self.context.bool_type().const_zero(), 
							"forcond"
						);

						self.builder.build_conditional_branch(cond_ir, body_bb, end_bb);

					} else {
						panic!();
					}
				} else {
					self.builder.build_unconditional_branch(end_bb);
				}

				self.builder.position_at_end(body_bb);

				// Generate body
				self.generate_node(body, &subscope)?;

				if let Some(iter) = iter {
					if let ASTNode::Expression(expr) = &iter.node {
						self.generate_expr(&expr, &iter.type_info.borrow().as_ref().unwrap(), &subscope);
					} else {
						panic!();
					}
				}

				self.builder.build_unconditional_branch(cond_bb);

				self.builder.position_at_end(end_bb);

				Ok(None)
			}


			ControlFlow::Return { expr } => {
				if let Some(expr) = expr {
					let expr_inner = match &expr.node {
						ASTNode::Expression(expr_inner) => expr_inner,
						_ => panic!(), 
					};

					let e = self.generate_expr(expr_inner, expr.type_info.borrow().as_ref().unwrap(), scope);
					
					if let Some(e) = LLVMBackend::try_into_basic_value(e) {
						return Ok(Some(Box::new(self.builder.build_return(Some(e.as_ref())))));
					}
				}
				Ok(Some(Box::new(self.builder.build_return(None))))
				
				
			},
			ControlFlow::Break => todo!(),
			ControlFlow::Continue => todo!(),
		}
	}



	fn generate_expr(&self, expr: &Expr, t: &Type, scope: &LLVMScope<'ctx, '_>) -> Box<dyn AnyValue<'ctx> + 'ctx> {
		match expr {
			Expr::Atom(atom, _meta) => {
				let a = atom.borrow();
				match &*a {
					Atom::IntegerLit(i) => Box::new(self.context.i32_type().const_int(*i as u64, false)),
					Atom::BoolLit(b) => Box::new(self.context.bool_type().const_int(if *b { 1 } else { 0 }, false)),
					Atom::FloatLit(f) => Box::new(self.context.f32_type().const_float(*f)),
					Atom::Variable(v) => Box::new(self.builder.build_load(scope.get_variable(&v).unwrap().clone(), "vload")),
					Atom::ArrayLit(_) => todo!(),

					Atom::Cast(elem, to) => {
						if let ASTNode::Expression(expr) = &elem.node {
							self.generate_cast(&expr, elem.type_info.borrow().as_ref().unwrap(), &to, scope)
						} else { panic!(); }
					},

					Atom::FnCall { name, args } => {
						let fn_v = self.module.get_function(&name).unwrap();

						let args_mapped: Vec<_> = args.iter().map(
							|x| LLVMBackend::into_basic_metadata_value(
								self.generate_expr(
									if let ASTNode::Expression(e) = &x.node { &e } else { panic!() }, 
									t,
									scope
								)
							)
						).collect(); 

						Box::new(self.builder.build_call(fn_v, &args_mapped, &name))
					},

					Atom::StringLit(s) => {
						let len = s.as_bytes().len().try_into().unwrap();
						let string_t = self.context.i8_type().array_type(len);
						let val = self.module.add_global(string_t, Some(AddressSpace::Const), ".str");
						let literal: Vec<_> = s.as_bytes().iter().map(|x| self.context.i8_type().const_int(*x as u64, false)).collect();

						val.set_initializer(&IntType::const_array(self.context.i8_type(), &literal));

						Box::new(self.str_type().const_named_struct(&[
								val.as_pointer_value().as_basic_value_enum(), 
								self.context.i64_type().const_int(len.into(), false).as_basic_value_enum()
								]
							)
						)
					}
				}

			},

			Expr::Cons(op, elems, _meta) => 
			{
				if elems.len() == 1 {
					todo!()
				} else {
					let lhs = &elems[0];
					let rhs = &elems[1];

					match &t.inner {
						crate::parser::types::InnerType::Basic(b) => {
							match b { //self.builder.build_int_add(lhs, rhs, name)
								
								Basic::ISIZE | Basic::USIZE | Basic::I64 | Basic::U64 | Basic::I32 | Basic::U32 | Basic::I16 | Basic::U16 | Basic::I8 | Basic::U8 | Basic::CHAR => {
									let lhs_i = self.generate_expr(lhs, t, scope).as_any_value_enum().into_int_value();
									let rhs_i = self.generate_expr(rhs, t, scope).as_any_value_enum().into_int_value();

									Box::new(
										match op {
											Operator::Add => self.builder.build_int_add(lhs_i, rhs_i, "iadd"),
											Operator::Sub => self.builder.build_int_sub(lhs_i, rhs_i, "isub"),
											Operator::Mult => self.builder.build_int_mul(lhs_i, rhs_i, "imul"),
											Operator::Div => self.builder.build_int_signed_div(lhs_i, rhs_i, "idiv"), // TODO: Add unsigned

											Operator::Assign => {
												if let Expr::Atom(a, _) = &lhs {
													if let Atom::Variable(v) = &*a.borrow() {						
														self.builder.build_store(*scope.get_variable(&v).unwrap(), rhs_i);
														return Box::new(rhs_i);
													}
												}
												panic!();
												
											}
											_ => todo!(),
										}
									)
								},
								Basic::F64 | Basic::F32 => {
									let lhs = self.generate_expr(lhs, t, scope).as_any_value_enum().into_float_value();
									let rhs = self.generate_expr(rhs, t, scope).as_any_value_enum().into_float_value();

									Box::new(
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
								Basic::STR => todo!(),
							}
						},
						InnerType::Alias(_, _) => todo!(),
						InnerType::Aggregate(_) => todo!(),
						InnerType::Pointer(_) => todo!(),
						InnerType::Function(_, _) => todo!(),
						InnerType::Unresolved(_) => todo!(),
					}
				}
			},
		}
	}


	fn generate_cast(&self, expr: &Expr, from: &Type, to: &Type, scope: &LLVMScope<'ctx, '_>) -> Box<dyn AnyValue<'ctx> + 'ctx> {
		match from.inner {
			InnerType::Basic(b) => {
				
				if from.is_numeric() {
					if let InnerType::Basic(b) = &to.inner {

						match b {

							Basic::BOOL => {
								let val = self.generate_expr(expr, from, scope);
								match val.as_any_value_enum() {
									
									AnyValueEnum::IntValue(i) => return Box::new(
										self.builder.build_int_cast(i, self.context.bool_type(), "boolcast").as_any_value_enum()
									),

									_ => panic!()
								}
							}

							_ => todo!()
						}

					} else {
						panic!(); // Not a valid cast, semantic analysis went wrong
					}

				} else { // Not numeric, match other Basics

					match b {
						Basic::STR => {
							if let InnerType::Pointer(other_p) = &to.inner {
								if let InnerType::Basic(other_b) = other_p.inner {
									if let Basic::CHAR = other_b {
										// Cast from `str` to char*
										let val = self.generate_expr(expr, from, scope);
										
										match val.as_any_value_enum() {
											AnyValueEnum::StructValue(struct_val) => {
												let val_extracted = match self.builder.build_extract_value(struct_val, 0, "cast").unwrap() {
													BasicValueEnum::PointerValue(p) => p,
													_ => panic!(),
												};

												return Box::new(
													self.builder.build_pointer_cast(
														val_extracted, 
														self.context.i8_type().ptr_type(AddressSpace::Generic), 
														"charcast"
													)
												);
											}
											_ => panic!(),
										}
									}
								}
							}
							panic!()
						},
						
						_ => todo!(),
					}
				}
			},
			InnerType::Alias(_, _) => todo!(),
			InnerType::Aggregate(_) => todo!(),
			InnerType::Pointer(_) => todo!(),
			InnerType::Function(_, _) => todo!(),
			InnerType::Unresolved(_) => todo!(),
		}
	}





	pub fn create_entry_block_alloca<T: BasicType<'ctx>>(&self, name: &str, ty: T) -> PointerValue<'ctx> {
		let builder = self.context.create_builder();
		let entry = self.fn_value_opt.unwrap().get_first_basic_block().unwrap();
		
		match entry.get_first_instruction() {
			Some(first_instr) => builder.position_before(&first_instr),
			None => builder.position_at_end(entry),
		};

		builder.build_alloca(ty, name)
	}




	fn into_basic_metadata_value<'scope>(t: Box<dyn AnyValue<'scope> + 'scope>) -> BasicMetadataValueEnum<'scope> {
		LLVMBackend::try_into_basic_metadata_value(t).unwrap()
	}

	fn try_into_basic_metadata_value<'scope>(t: Box<dyn AnyValue<'scope> + 'scope>) -> Option<BasicMetadataValueEnum<'scope>> {
		match (*t).as_any_value_enum() {
			AnyValueEnum::ArrayValue(a) => Some(inkwell::values::BasicMetadataValueEnum::ArrayValue(a)),
			AnyValueEnum::FloatValue(f) => Some(inkwell::values::BasicMetadataValueEnum::FloatValue(f)),
			AnyValueEnum::IntValue(i) => Some(inkwell::values::BasicMetadataValueEnum::IntValue(i)),
			AnyValueEnum::PointerValue(p) => Some(inkwell::values::BasicMetadataValueEnum::PointerValue(p)),
			AnyValueEnum::StructValue(s) => Some(inkwell::values::BasicMetadataValueEnum::StructValue(s)),
			AnyValueEnum::VectorValue(v) => Some(inkwell::values::BasicMetadataValueEnum::VectorValue(v)),
			_ => panic!(),
		}
	}


	fn into_basic_value<'scope>(t: Box<dyn AnyValue<'scope> + 'scope>) -> Box<dyn BasicValue<'scope> + 'scope> {
		LLVMBackend::try_into_basic_value(t).unwrap()
	}

	fn try_into_basic_value<'scope>(t: Box<dyn AnyValue<'scope> + 'scope>) -> Option<Box<dyn BasicValue<'scope> + 'scope>> {
		match (*t).as_any_value_enum() {
			AnyValueEnum::ArrayValue(a) => Some(Box::new(a)),
			AnyValueEnum::FloatValue(f) => Some(Box::new(f)),
			AnyValueEnum::IntValue(i) => Some(Box::new(i)),
			AnyValueEnum::PointerValue(p) => Some(Box::new(p)),
			AnyValueEnum::StructValue(s) => Some(Box::new(s)),
			AnyValueEnum::VectorValue(v) => Some(Box::new(v)),
			_ => panic!(),
		}
	}

	fn to_basic_type<'scope>(t: Box<dyn AnyType<'scope> + 'scope>) -> Box<dyn BasicType<'scope> + 'scope> {
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

				Basic::STR => 							Box::new(self.str_type()),
			},

			InnerType::Alias(_id, t) => self.get_llvm_type(t.as_ref()),

			InnerType::Aggregate(types) => {
				let types_mapped : Vec<_> = types.values().map(
					|t| LLVMBackend::to_basic_type(self.get_llvm_type(t.as_ref())).as_basic_type_enum()
				).collect();

				Box::new(self.context.struct_type(&types_mapped, false))
			},

			InnerType::Pointer(t_sub) => Box::new(LLVMBackend::to_basic_type(self.get_llvm_type(t_sub)).ptr_type(AddressSpace::Generic)),
			InnerType::Function(_, _) => todo!(),
			InnerType::Unresolved(_) => panic!(),
		}
	}



	fn str_type(&self) -> StructType<'ctx> {
		self.context.struct_type(
			&[
				BasicTypeEnum::PointerType(self.context.i8_type().ptr_type(AddressSpace::Generic)),
				BasicTypeEnum::IntType(self.context.i64_type())
			], false
		)
	}
}