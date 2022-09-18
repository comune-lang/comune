use std::cell::{RefCell, Ref};
use std::collections::HashMap;
use std::rc::Rc;

use crate::parser::ast::{ASTElem, ASTNode};
use crate::parser::controlflow::ControlFlow;
use crate::parser::expression::{Expr, Atom, Operator};
use crate::parser::namespace::Identifier;
use crate::parser::types::{Type, Basic, TypeDef};

use inkwell::{IntPredicate, AddressSpace, FloatPredicate};
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Module, Linkage};
use inkwell::passes::PassManager;
use inkwell::types::{AnyTypeEnum, BasicTypeEnum, FunctionType, BasicMetadataTypeEnum, AnyType, BasicType, IntType, StructType};
use inkwell::values::{AnyValueEnum, FunctionValue, BasicValue, AnyValue, PointerValue, BasicMetadataValueEnum, BasicValueEnum};


// This shit is a mess of enum conversions. hate it


type LLVMResult<T> = Result<T, String>;

pub struct LLVMBackend<'ctx> {
	pub context: &'ctx Context,
	pub module: Module<'ctx>,
	pub builder: Builder<'ctx>,
	pub fpm: Option<PassManager<FunctionValue<'ctx>>>,
	pub fn_value_opt: Option<FunctionValue<'ctx>>,
	pub type_map: RefCell<HashMap<Type, Rc<dyn AnyType<'ctx> + 'ctx>>>, 
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

	pub fn register_fn(&mut self, name_mangled: &String, t: &TypeDef) -> LLVMResult<FunctionValue> {
		let fn_t = self.generate_prototype(t)?;
		let fn_v = self.module.add_function(name_mangled.as_str(), fn_t, None);

		Ok(fn_v)
	}

	pub fn generate_fn(&mut self, name_mangled: &String, t: &TypeDef, body: Option<&ASTElem>) -> LLVMResult<FunctionValue> {
		let fn_v = self.module.get_function(name_mangled.as_str()).unwrap();

		self.fn_value_opt = Some(fn_v);
		self.fpm = Some(PassManager::create(&self.module));

		if let Some(body) = body {
			let entry = self.context.append_basic_block(fn_v, "entry");
			self.builder.position_at_end(entry);

			let mut scope = LLVMScope::new();
	
			// Add parameters to variable list
			if let TypeDef::Function(_ret, args) = &t {
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


	fn generate_prototype(&self, t: &TypeDef) -> LLVMResult<FunctionType<'ctx>> {
		if let TypeDef::Function(ret, args) = &t {

			let types_mapped: Vec<_> = args.iter().map(
				|t| Self::to_basic_metadata_enum(self.get_llvm_type(&t.0)).unwrap()
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
				self.generate_expr(&e.borrow(), elem.type_info.borrow().as_ref().unwrap(), scope); 
			},

			ASTNode::Declaration(t, n, e) => {
				let name = n.to_string();
				let alloca = self.create_entry_block_alloca(
					&name, 
					Self::to_basic_type(self.get_llvm_type(t)).as_basic_type_enum()
				);

				if let Some(expr) = e {
					if let ASTNode::Expression(expr) = &expr.as_ref().node {
						self.builder.build_store(alloca, Self::into_basic_value(self.generate_expr(&expr.borrow(), t, scope)).as_basic_value_enum());
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

				let cond = self.generate_expr(&expr.borrow(), cond.type_info.borrow().as_ref().unwrap_or(&Type::Basic(Basic::VOID)), scope);
				
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


			ControlFlow::While { cond, body } => {
				let parent = self.fn_value_opt.unwrap();

				let expr;
				if let ASTNode::Expression(e) = &cond.node { expr = e; } else { unreachable!(); }


				let cond_bb = self.context.append_basic_block(parent, "whilecond");
				let body_bb = self.context.append_basic_block(parent, "whileblock");
				let end_bb = self.context.append_basic_block(parent, "whileend");

				self.builder.build_unconditional_branch(cond_bb);
				self.builder.position_at_end(cond_bb);

				let cond = self.generate_expr(&expr.borrow(), cond.type_info.borrow().as_ref().unwrap_or(&Type::Basic(Basic::VOID)), scope);
				
				let cond = self.builder.build_int_compare(
					IntPredicate::NE, 
					cond.as_any_value_enum().into_int_value(), 
					self.context.bool_type().const_zero(), 
					"whilecond"
				);

				self.builder.build_conditional_branch(cond, body_bb, end_bb);
				
				self.builder.position_at_end(body_bb);

				// Generate body
				self.generate_node(body, scope)?;
				self.builder.build_unconditional_branch(cond_bb);
				self.builder.position_at_end(end_bb);

				Ok(None)
			},


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
						let cond_expr = self.generate_expr(&expr.borrow(), &cond.type_info.borrow().as_ref().unwrap(), &subscope);

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
					self.builder.build_unconditional_branch(body_bb);
				}

				self.builder.position_at_end(body_bb);

				// Generate body
				self.generate_node(body, &subscope)?;

				if let Some(iter) = iter {
					if let ASTNode::Expression(expr) = &iter.node {
						self.generate_expr(&expr.borrow(), &iter.type_info.borrow().as_ref().unwrap(), &subscope);
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

					let e = self.generate_expr(&expr_inner.borrow(), expr.type_info.borrow().as_ref().unwrap(), scope);
					
					if let Some(e) = Self::try_into_basic_value(e) {
						return Ok(Some(Box::new(self.builder.build_return(Some(e.as_ref())))));
					}
				}
				Ok(Some(Box::new(self.builder.build_return(None))))
				
				
			},
			ControlFlow::Break => todo!(),
			ControlFlow::Continue => todo!(),
		}
	}



	fn generate_expr(&self, expr: &Expr, t: &Type, scope: &LLVMScope<'ctx, '_>) -> Rc<dyn AnyValue<'ctx> + 'ctx> {
		match expr {
			Expr::Atom(a, _meta) => {
				match a {
					Atom::IntegerLit(i, _) => {
						match self.get_llvm_type(t).as_any_type_enum() {
							AnyTypeEnum::IntType(i_t) => return Rc::new(i_t.const_int(*i as u64, false)),
							_ => panic!(),
						}
					}

					Atom::FloatLit(f, _) => {
						match self.get_llvm_type(t).as_any_type_enum() {
							AnyTypeEnum::FloatType(f_t) => return Rc::new(f_t.const_float(*f)),
							_ => panic!(),
						}
					}

					Atom::BoolLit(b) => Rc::new(self.context.bool_type().const_int(if *b { 1 } else { 0 }, false)),
					Atom::Identifier(v) => Rc::new(self.builder.build_load(self.resolve_identifier(scope, v), "vload")),
					Atom::ArrayLit(_) => todo!(),

					Atom::Cast(elem, to) => {
						if let ASTNode::Expression(expr) = &elem.node {
							self.generate_cast(&expr.borrow(), elem.type_info.borrow().as_ref().unwrap(), &to, scope)
						} else { panic!(); }
					},

					Atom::FnCall { name, args } => {
						let fn_v = self.module.get_function(name.resolved.as_ref().unwrap()).unwrap();

						let args_mapped: Vec<_> = args.iter().map(
							|x| {
								let expr;
								if let ASTNode::Expression(e) = &x.node { 
									expr = e.borrow(); 
								} else { 
									panic!() 
								}
								Self::into_basic_metadata_value(self.generate_expr(&expr, t, scope)
								)
							}
						).collect(); 

						Rc::new(self.builder.build_call(fn_v, &args_mapped, name.resolved.as_ref().unwrap()))
					},

					Atom::StringLit(s) => {
						let len = s.as_bytes().len().try_into().unwrap();
						let string_t = self.context.i8_type().array_type(len);
						let val = self.module.add_global(string_t, Some(AddressSpace::Const), ".str");
						let literal: Vec<_> = s.as_bytes().iter().map(|x| self.context.i8_type().const_int(*x as u64, false)).collect();

						val.set_initializer(&IntType::const_array(self.context.i8_type(), &literal));

						Rc::new(self.str_type().const_named_struct(&[
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
					match op {
						Operator::Ref => {
							if let Expr::Atom(a, _) = &elems[0].0 {
								if let Atom::Identifier(v) = &a {						
									return Rc::new(self.resolve_identifier(scope, v));
								}
							}
							panic!()
						}

						Operator::Deref => {
							if let Expr::Atom(a, _) = &elems[0].0 {
								if let Atom::Identifier(v) = &a {
									let ptr = self.builder.build_load(self.resolve_identifier(scope, v), "loadptr").as_basic_value_enum().into_pointer_value();
									return Rc::new(self.builder.build_load(ptr, "deref"));
								}
							}
							panic!()
						}

						_ => todo!(),
					}
				} else {
					let lhs = &elems[0];
					let rhs = &elems[1];
					
					match op {
						Operator::MemberAccess => {
							if let Expr::Atom(Atom::Identifier(id), _) = &rhs.0 {
								let lhs_s = self.generate_expr(&lhs.0, t, scope).as_any_value_enum().into_struct_value();
								Rc::new(self.builder.build_extract_value(lhs_s, id.mem_idx, "memberaccess").unwrap())
							} else {
								panic!();
							}
						}

						Operator::Assign => {
							let rhs_val = Self::into_basic_value(self.generate_expr(&rhs.0, t, scope)).as_basic_value_enum();
							self.builder.build_store(self.generate_lvalue_expr(&lhs.0, t, scope), rhs_val);
							Rc::new(rhs_val)
						}

						_ => {
							let lhs_v = self.generate_expr(&lhs.0, t, scope).as_any_value_enum();
							let rhs_v = self.generate_expr(&rhs.0, t, scope).as_any_value_enum();
							let result;

							let mut used_op = op.clone();
							
							if op.is_compound_assignment() {
								used_op = used_op.get_compound_operator();
							}

							if t.is_integral() {
								let lhs_i = lhs_v.into_int_value();
								let rhs_i = rhs_v.into_int_value();

								result = match used_op {
									Operator::Add => self.builder.build_int_add(lhs_i, rhs_i, "iadd"),
									Operator::Sub => self.builder.build_int_sub(lhs_i, rhs_i, "isub"),
									Operator::Mul => self.builder.build_int_mul(lhs_i, rhs_i, "imul"),
									Operator::Div => 
										if t.is_signed() { 
											self.builder.build_int_signed_div(lhs_i, rhs_i, "idiv")
										} else {
											self.builder.build_int_unsigned_div(lhs_i, rhs_i, "udiv")
										},

									// Relational operators
									_ => self.builder.build_int_compare(Self::to_int_predicate(&used_op, t.is_signed()), lhs_i, rhs_i, "icomp")
									
								}.as_basic_value_enum();

							} else if t.is_floating_point() {
								let lhs_f = lhs_v.into_float_value();
								let rhs_f = rhs_v.into_float_value();

								result = match op {
									Operator::Add => self.builder.build_float_add(lhs_f, rhs_f, "fadd").as_basic_value_enum(),
									Operator::Sub => self.builder.build_float_sub(lhs_f, rhs_f, "fsub").as_basic_value_enum(),
									Operator::Mul => self.builder.build_float_mul(lhs_f, rhs_f, "fmul").as_basic_value_enum(),
									Operator::Div => self.builder.build_float_div(lhs_f, rhs_f, "fdiv").as_basic_value_enum(),

									// Relational operators
									_ => self.builder.build_float_compare(Self::to_float_predicate(op), lhs_f, rhs_f, "fcomp").as_basic_value_enum()
								}
							} else {
								todo!();
							}


							if op.is_compound_assignment() {
								let lhs_store = self.generate_lvalue_expr(&lhs.0, t, scope);
								self.builder.build_store(lhs_store, result);
							}

							Rc::new(result)

							/*} else if t.is_floating_point() {
								let lhs_f = self.generate_expr(&lhs.0, t, scope).as_any_value_enum().into_float_value();
								let rhs_f = self.generate_expr(&rhs.0, t, scope).as_any_value_enum().into_float_value();

								Rc::new(match op {
									Operator::Add => self.builder.build_float_add(lhs_f, rhs_f, "fadd").as_any_value_enum(),
									Operator::Sub => self.builder.build_float_sub(lhs_f, rhs_f, "fsub").as_any_value_enum(),
									Operator::Mul => self.builder.build_float_mul(lhs_f, rhs_f, "fmul").as_any_value_enum(),
									Operator::Div => self.builder.build_float_div(lhs_f, rhs_f, "fdiv").as_any_value_enum(),

									// TODO: Compound assignment

									// Relational operators
									_ => self.builder.build_float_compare(Self::to_float_predicate(op), lhs_f, rhs_f, "fcomp").as_any_value_enum()
								})
							} else {
								todo!()
							}*/
						}
					}
				}
			},
		}
	}

	// an lvalue expression is an expression that is assignable
	fn generate_lvalue_expr(&self, expr: &Expr, t: &Type, scope: &LLVMScope<'ctx, '_>) -> PointerValue<'ctx> {
		match expr {
			Expr::Atom(Atom::Identifier(id), _) => self.resolve_identifier(scope, id),
			
			Expr::Cons(op, elems, _) => {
				match op {

					Operator::Deref => {
						if let Expr::Atom(Atom::Identifier(id), _) = &elems[0].0 {
							// In LLVM, pointers are really pointers-to-pointers, so for lvalue expressions we only 
							// load through the pointer to get the pointer it points to. are ya confused yet
							self.builder.build_load(self.resolve_identifier(scope, id), "loadptr")
								.as_basic_value_enum()
								.into_pointer_value()
						} else {
							panic!()
						}
					}

					Operator::MemberAccess => {
						let lhs = self.generate_lvalue_expr(&elems[0].0, t, scope);
						
						if let Expr::Atom(Atom::Identifier(id), _) = &elems[1].0 {
							self.builder.build_struct_gep(lhs, id.mem_idx, "memberaccess").unwrap()
						} else { 
							panic!(); 
						}
					}
					_ => panic!(),
				}
			}
			_ => panic!(),
		}
	}


	fn generate_cast(&self, expr: &Expr, from: &Type, to: &Type, scope: &LLVMScope<'ctx, '_>) -> Rc<dyn AnyValue<'ctx> + 'ctx> {
		match from {
			Type::Basic(b) => {
				
				if from.is_numeric() {
					let val = self.generate_expr(expr, from, scope);
					match val.as_any_value_enum() {
									
						AnyValueEnum::IntValue(i) => {
							if let Type::Basic(b) = &to {
								match b {

									Basic::BOOL => 
										return Rc::new(
											self.builder.build_int_compare(IntPredicate::NE, i, i.get_type().const_zero(), "boolcast")
										),

									_ => {

										if to.is_numeric() {
											match self.get_llvm_type(to).as_any_type_enum() {
												AnyTypeEnum::IntType(t) => return Rc::new(self.builder.build_int_cast(i, t, "icast")),
												
												_ => panic!(),
											}
										}

										todo!()
									}
								}

							}
						},

						AnyValueEnum::FloatValue(_) => todo!(),

						_ => panic!(),
					}
					
					panic!() // Didn't return, incorrect cast

				} else { // Not numeric, match other Basics

					match b {
						Basic::STR => {
							if let Type::Pointer(other_p) = &to {
								if let Type::Basic(other_b) = **other_p {
									if let Basic::CHAR = other_b {
										// Cast from `str` to char*
										let val = self.generate_expr(expr, from, scope);
										
										match val.as_any_value_enum() {
											AnyValueEnum::StructValue(struct_val) => {
												let val_extracted = match self.builder.build_extract_value(struct_val, 0, "cast").unwrap() {
													BasicValueEnum::PointerValue(p) => p,
													_ => panic!(),
												};

												return Rc::new(
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
			Type::Pointer(_) => todo!(),
			Type::Unresolved(_) => todo!(),
    		Type::TypeRef(_) => todo!(),
		}
	}


	
	fn resolve_identifier(&self, scope: &LLVMScope<'ctx, '_>, id: &Identifier) -> PointerValue<'ctx> {
		*scope.get_variable(id.resolved.as_ref().unwrap()).unwrap()
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




	fn into_basic_metadata_value<'scope>(t: Rc<dyn AnyValue<'scope> + 'scope>) -> BasicMetadataValueEnum<'scope> {
		Self::try_into_basic_metadata_value(t).unwrap()
	}

	fn try_into_basic_metadata_value<'scope>(t: Rc<dyn AnyValue<'scope> + 'scope>) -> Option<BasicMetadataValueEnum<'scope>> {
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


	fn into_basic_value<'scope>(t: Rc<dyn AnyValue<'scope> + 'scope>) -> Rc<dyn BasicValue<'scope> + 'scope> {
		Self::try_into_basic_value(t).unwrap()
	}

	fn try_into_basic_value<'scope>(t: Rc<dyn AnyValue<'scope> + 'scope>) -> Option<Rc<dyn BasicValue<'scope> + 'scope>> {
		match (*t).as_any_value_enum() {
			AnyValueEnum::ArrayValue(a) => Some(Rc::new(a)),
			AnyValueEnum::FloatValue(f) => Some(Rc::new(f)),
			AnyValueEnum::IntValue(i) => Some(Rc::new(i)),
			AnyValueEnum::PointerValue(p) => Some(Rc::new(p)),
			AnyValueEnum::StructValue(s) => Some(Rc::new(s)),
			AnyValueEnum::VectorValue(v) => Some(Rc::new(v)),
			_ => panic!(),
		}
	}

	fn to_basic_type<'scope>(t: Rc<dyn AnyType<'scope> + 'scope>) -> Rc<dyn BasicType<'scope> + 'scope> {
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

	fn to_basic_metadata_enum(t: Rc<dyn AnyType<'ctx> + 'ctx>) -> Option<BasicMetadataTypeEnum<'ctx>> {
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
	
	fn get_llvm_type(&self, t: &Type) -> Rc<dyn AnyType<'ctx> + 'ctx> {
		match &t {
			Type::Basic(b) => match b {
				Basic::I64 | Basic::U64 =>				Rc::new(self.context.i64_type()),
				Basic::I32 | Basic::U32 =>				Rc::new(self.context.i32_type()),
				Basic::I16 | Basic::U16 =>				Rc::new(self.context.i16_type()),
				Basic::I8 | Basic::U8 | Basic::CHAR =>	Rc::new(self.context.i8_type()),
				Basic::ISIZE | Basic::USIZE => 			Rc::new(self.context.i64_type()),
				Basic::F64 => 							Rc::new(self.context.f64_type()),
				Basic::F32 => 							Rc::new(self.context.f32_type()),
				Basic::BOOL => 							Rc::new(self.context.bool_type()),
				Basic::VOID => 							Rc::new(self.context.void_type()),
				Basic::STR => 							Rc::new(self.str_type()),
			},

			Type::TypeRef(t_ref) => match &*t_ref.borrow() {
				TypeDef::Alias(_id, t) => self.get_llvm_type(t),

				TypeDef::Aggregate(aggregate) => {
					let mapped_t = { self.type_map.borrow().get(t).cloned() };

					if let Some(mapped_t) = mapped_t {
						mapped_t.clone()
					} else {
						let result_type = Rc::new(self.context.opaque_struct_type("agg"));
						self.type_map.borrow_mut().insert(t.clone(), result_type.clone());

						let mut types_mapped = vec![];
						types_mapped.reserve(aggregate.members.len());
						
						for m in aggregate.members.iter() {
							types_mapped.push(Self::to_basic_type(self.get_llvm_type(&m.1.0)).as_basic_type_enum())
						}

						result_type.set_body(&types_mapped, false);

						result_type
					}
				},
   				TypeDef::Function(_, _) => todo!(),
			}
			Type::Pointer(t_sub) => Rc::new(Self::to_basic_type(self.get_llvm_type(t_sub)).ptr_type(AddressSpace::Generic)),
			Type::Unresolved(_) => panic!(),
		}
	}


	fn to_int_predicate(op: &Operator, signed: bool) -> IntPredicate {
		if signed {
			match op {
				Operator::Eq =>			IntPredicate::EQ,
				Operator::NotEq =>		IntPredicate::NE,
				Operator::Greater =>	IntPredicate::SGT,
				Operator::GreaterEq =>	IntPredicate::SGE,
				Operator::Less =>		IntPredicate::SLT,
				Operator::LessEq =>		IntPredicate::SLE,
				
				_ => panic!(),
			}
		} else {
			match op {
				Operator::Eq =>			IntPredicate::EQ,
				Operator::NotEq =>		IntPredicate::NE,
				Operator::Greater =>	IntPredicate::UGT,
				Operator::GreaterEq =>	IntPredicate::UGE,
				Operator::Less =>		IntPredicate::ULT,
				Operator::LessEq =>		IntPredicate::ULE,
				
				_ => panic!(),
			}
		}
	}


	fn to_float_predicate(op: &Operator) -> FloatPredicate {
		match op {
			Operator::Eq =>			FloatPredicate::OEQ,
			Operator::NotEq =>		FloatPredicate::ONE,
			Operator::Greater =>	FloatPredicate::OGT,
			Operator::GreaterEq =>	FloatPredicate::OGE,
			Operator::Less =>		FloatPredicate::OLT,
			Operator::LessEq =>		FloatPredicate::OLE,
			
			_ => panic!(),
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