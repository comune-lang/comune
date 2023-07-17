use std::{collections::HashMap, rc::Rc, sync::Arc};

use inkwell::{
	attributes::{Attribute, AttributeLoc},
	basic_block::BasicBlock,
	builder::Builder,
	context::Context,
	debug_info::DebugInfoBuilder,
	module::{Linkage, Module},
	targets::{InitializationConfig, Target, TargetMachine, TargetTriple},
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

use crate::{
	ast::{
		expression::Operator,
		types::{
			Basic, BindingProps, DataLayout, FloatSize, FnPrototype, IntSize, TupleKind, Type,
		},
	},
	cir::{CIRCallId, CIRFunction, CIRModule, CIRStmt, LValue, Operand, PlaceElem, RValue},
	constexpr::{ConstExpr, ConstValue},
};


type LLVMResult<T> = Result<T, String>;

pub struct LLVMBackend<'ctx> {
	pub context: &'ctx Context,
	pub module: Module<'ctx>,
	pub target_machine: TargetMachine,
	builder: Builder<'ctx>,
	di_builder: Option<DebugInfoBuilder<'ctx>>,
	fn_value_opt: Option<FunctionValue<'ctx>>,
	type_map: HashMap<String, AnyTypeEnum<'ctx>>,
	fn_map: HashMap<Arc<FnPrototype>, String>,
	blocks: Vec<BasicBlock<'ctx>>,
	variables: Vec<(PointerValue<'ctx>, BindingProps, Type)>,
}

impl<'ctx> LLVMBackend<'ctx> {
	pub fn new(
		context: &'ctx Context,
		module_name: &str,
		source_file: &str,
		optimized: bool,
		debug: bool,
	) -> Self {
		let module = context.create_module(module_name);
		let builder = context.create_builder();

		let (di_builder, _compile_unit) = if debug {
			// jesus christ

			let (di_builder, compile_unit) = module.create_debug_info_builder(
				/* allow_unresolved */ true,
				/* language */ inkwell::debug_info::DWARFSourceLanguage::CPlusPlus,
				/* filename */ source_file,
				/* directory */ ".",
				/* producer */ "comune-rs",
				/* is_optimized */ optimized,
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
			di_builder,
			fn_value_opt: None,
			type_map: HashMap::new(),
			fn_map: HashMap::new(),
			blocks: vec![],
			variables: vec![],
		}
	}

	pub fn compile_module(&mut self, module: &CIRModule) -> LLVMResult<()> {
		// Add opaque types

		for (i, _) in &module.types {
			let opaque = self
				.context
				.opaque_struct_type(&i.to_string())
				.as_any_type_enum();

			self.type_map.insert(i.clone(), opaque);
		}

		// Define type bodies

		for (i, ty) in &module.types {
			let ty = ty.read().unwrap();
			let mut members_ir = vec![];

			for (_, mem, _) in &ty.members {
				members_ir.push(Self::to_basic_type(self.get_llvm_type(mem)));
			}

			let type_ir = self.type_map[i].into_struct_type();

			type_ir.set_body(&members_ir, ty.layout == DataLayout::Packed);
		}

		for (proto, func) in &module.functions {
			self.register_fn(func.mangled_name.as_ref().unwrap(), func)?;
			self.fn_map
				.insert(proto.clone(), func.mangled_name.as_ref().unwrap().clone());
		}

		for func in module.functions.values() {
			if !func.is_extern {
				self.generate_fn(func.mangled_name.as_ref().unwrap(), func)?;
			}
		}

		if let Some(di_builder) = &self.di_builder {
			di_builder.finalize();
		}

		Ok(())
	}

	pub fn generate_libc_bindings(&self) {
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

		Ok(fn_v)
	}

	fn generate_fn(&mut self, name: &str, t: &CIRFunction) -> LLVMResult<FunctionValue> {
		let fn_v = self.module.get_function(name).unwrap();

		self.fn_value_opt = Some(fn_v);

		for i in 0..t.blocks.len() {
			self.blocks.push(
				self.context
					.append_basic_block(self.fn_value_opt.unwrap(), &format!("bb{i}")),
			);
		}

		for (i, (ty, props, _)) in t.variables.iter().enumerate() {
			let mut ty_ll = Self::to_basic_type(self.get_llvm_type(ty));

			if self.pass_by_ptr(&ty, props) {
				ty_ll = Self::to_basic_type(self.get_llvm_type(&ty.ptr_type(props.is_mut)));
			}

			self.variables.push((
				self.create_entry_block_alloca(&format!("_{i}"), ty_ll),
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

				self.builder.build_store(self.variables[idx].0, param);
			}
		}

		for i in 0..t.blocks.len() {
			let block = &t.blocks[i];

			self.builder.position_at_end(self.blocks[i]);

			for stmt in block.items.iter() {
				match stmt {
					CIRStmt::Expression(..) => {
						panic!("loose Expression found in LLVM codegen!")
					}

					CIRStmt::Assignment(lval, expr) => {
						self.generate_expr(
							self.generate_lvalue_use(lval, BindingProps::mut_reference())
								.into_pointer_value(),
							expr,
						);
					}

					CIRStmt::RefInit(var, lval) => {
						let reference = self.variables[*var].0;
						let props = self.variables[*var].1;

						assert!(props.is_ref);

						self.builder
							.build_store(reference, self.generate_lvalue_use(lval, props));
					}

					CIRStmt::Jump(block) => {
						self.builder.build_unconditional_branch(self.blocks[*block]);
					}

					CIRStmt::Switch(cond, branches, else_block) => {
						let cond_ir = self
							.generate_operand(&Type::i32_type(true), cond)
							.as_basic_value_enum()
							.into_int_value();

						let cases: Vec<_> = branches
							.iter()
							.map(|(ty, val, branch)| {
								(
									self.generate_operand(ty, val).into_int_value(),
									self.blocks[*branch],
								)
							})
							.collect();

						self.builder
							.build_switch(cond_ir, self.blocks[*else_block], &cases);
					}

					CIRStmt::Return => {
						if let Some(lval) = t.get_return_lvalue() {
							let ret = self.generate_lvalue_use(&lval, t.ret.0);

							self.builder.build_return(Some(&ret));
						} else {
							self.builder.build_return(None);
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
									.generate_lvalue_use(local, BindingProps::value())
									.into_pointer_value();

								CallableValue::try_from(ptr).unwrap()
							}
						};

						let args_mapped: Vec<_> = args
							.iter()
							.map(|(lval, _, props)| {
								Self::to_basic_metadata_value(
									self.generate_lvalue_use(lval, *props).into(),
								)
							})
							.collect();

						let callsite = self.builder.build_call(fn_v, &args_mapped, "");

						if let Some(result) = result {
							if result.props.is_ref {
								// Function return value is a reference - perform reference initialization 
								assert!(result.projection.is_empty());

								self.builder.build_store(
									self.variables[result.local].0,
									callsite.try_as_basic_value().unwrap_left(),
								);
							} else {
								// Function return value is a plain value - use normal assignment
								self.builder.build_store(
									self.generate_lvalue_use(result, BindingProps::mut_reference())
										.into_pointer_value(),
									callsite.try_as_basic_value().unwrap_left(),
								);
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
									.generate_lvalue_use(local, BindingProps::value())
									.into_pointer_value();

								CallableValue::try_from(ptr).unwrap()
							}
						};

						let args_mapped: Vec<_> = args
							.iter()
							.map(|(lval, _, props)| self.generate_lvalue_use(lval, *props))
							.collect();

						let callsite = self.builder.build_invoke(
							fn_v,
							&args_mapped,
							self.blocks[*next],
							self.blocks[*except],
							"",
						);

						if let Some(result) = result {
							self.builder.position_at_end(self.blocks[*next]);

							if result.props.is_ref {
								// Function return value is a reference - perform reference initialization 
								assert!(result.projection.is_empty());

								self.builder.build_store(
									self.variables[result.local].0,
									callsite.try_as_basic_value().unwrap_left(),
								);
							} else {
								// Function return value is a plain value - use normal assignment
								self.builder.build_store(
									self.generate_lvalue_use(result, BindingProps::mut_reference())
										.into_pointer_value(),
									callsite.try_as_basic_value().unwrap_left(),
								);
							}
						}
					}

					// TODO: Generate LLVM intrinsics for these
					CIRStmt::StorageLive(_) => {}

					CIRStmt::StorageDead(_) => {}

					CIRStmt::DropShim { .. } => panic!("encountered DropShim in LLVM codegen!"),
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

	fn generate_expr(&self, store: PointerValue<'ctx>, expr: &RValue) -> InstructionValue<'ctx> {
		match expr {
			RValue::Atom(ty, op_opt, atom, _) => {
				match op_opt {
					Some(Operator::Deref) => {
						let atom_ir = Self::to_basic_value(
							self.generate_operand(ty, atom).as_any_value_enum(),
						);

						self.builder.build_store(
							store,
							self.builder
								.build_load(atom_ir.as_basic_value_enum().into_pointer_value(), "")
								.as_basic_value_enum(),
						)
					}

					Some(Operator::Ref) => {
						if let Operand::LValueUse(lval, props) = atom {
							// Terrible hack
							let mut props = *props;
							props.is_ref = true;

							self.builder
								.build_store(store, self.generate_lvalue_use(lval, props))
						} else {
							panic!()
						}
					}

					// TODO: Unary minus, logical NOT, etc
					None => self
						.builder
						.build_store(store, self.generate_operand(ty, atom)),

					_ => panic!(),
				}
			}

			RValue::Cons(expr_ty, [(lhs_ty, lhs), (rhs_ty, rhs)], op, _) => {
				let lhs_v =
					Self::to_basic_value(self.generate_operand(lhs_ty, lhs).as_any_value_enum())
						.as_basic_value_enum();
				let rhs_v =
					Self::to_basic_value(self.generate_operand(rhs_ty, rhs).as_any_value_enum())
						.as_basic_value_enum();
				let result;

				if expr_ty.is_integral() {
					let lhs_i = lhs_v.into_int_value();
					let rhs_i = rhs_v.into_int_value();

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

						_ => panic!(),
					}
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
					}
					.as_basic_value_enum()
				} else if expr_ty.is_boolean() {
					if lhs_v.is_int_value() {
						let lhs_i = lhs_v.into_int_value();
						let rhs_i = rhs_v.into_int_value();

						result = self
							.builder
							.build_int_compare(
								Self::to_int_predicate(op, lhs_ty.is_signed()),
								lhs_i,
								rhs_i,
								"",
							)
							.as_basic_value_enum();
					} else if lhs_v.is_float_value() {
						let lhs_f = lhs_v.into_float_value();
						let rhs_f = rhs_v.into_float_value();

						result = self
							.builder
							.build_float_compare(Self::to_float_predicate(op), lhs_f, rhs_f, "")
							.as_basic_value_enum();
					} else {
						panic!()
					}
				} else if matches!(expr_ty, Type::Pointer { .. }) {
					let lhs = lhs_v.into_pointer_value();
					let rhs = rhs_v.into_int_value();

					result = unsafe {
						self.builder
							.build_gep(lhs, &[rhs], "")
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
					Type::Tuple(TupleKind::Sum, types) => {
						let val = self.generate_operand(from, val);
						let idx = types.iter().position(|ty| ty == from).unwrap();

						let discriminant = self
							.context
							.i32_type()
							.const_int(idx as u64, false)
							.as_basic_value_enum();

						self.builder.build_store(
							self.builder.build_struct_gep(store, 0, "").unwrap(),
							discriminant,
						);

						let ptr = self.builder.build_pointer_cast(
							self.builder.build_struct_gep(store, 1, "").unwrap(),
							val.get_type().ptr_type(AddressSpace::Generic),
							"",
						);

						self.builder.build_store(ptr, val)
					}

					_ => match from {
						Type::Basic(b) => {
							if from.is_integral() || from.is_floating_point() {
								let val = self.generate_operand(from, val);

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
												)
												.as_basic_value_enum(),
										),

										_ => match self.get_llvm_type(to) {
											AnyTypeEnum::IntType(t) => self.builder.build_store(
												store,
												self.builder
													.build_int_cast(i, t, "")
													.as_basic_value_enum(),
											),

											AnyTypeEnum::FloatType(t) => {
												if from.is_signed() {
													self.builder.build_store(
														store,
														self.builder
															.build_signed_int_to_float(i, t, "")
															.as_basic_value_enum(),
													)
												} else {
													self.builder.build_store(
														store,
														self.builder
															.build_unsigned_int_to_float(i, t, "")
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
												.build_float_cast(f, t, "")
												.as_basic_value_enum(),
										),

										AnyTypeEnum::IntType(t) => {
											if to.is_signed() {
												self.builder.build_store(
													store,
													self.builder
														.build_float_to_signed_int(f, t, "")
														.as_basic_value_enum(),
												)
											} else {
												self.builder.build_store(
													store,
													self.builder
														.build_float_to_unsigned_int(f, t, "")
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
										if let Type::Basic(Basic::Integral { signed, .. }) = to {
											let val = self
												.generate_operand(from, val)
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
													)
													.as_basic_value_enum(),
											)
										} else {
											panic!()
										}
									}

									_ => todo!(),
								}
							}
						}

						Type::Pointer { .. } => {
							let val = self.generate_operand(from, val);
							let to_ir = self.get_llvm_type(to);

							if to.is_boolean() {
								self.builder.build_store(
									store,
									self.builder.build_is_not_null(val.into_pointer_value(), ""),
								)
							} else {
								self.builder.build_store(
									store,
									self.builder
										.build_pointer_cast(
											val.into_pointer_value(),
											to_ir.into_pointer_type(),
											"",
										)
										.as_basic_value_enum(),
								)
							}
						}

						Type::Tuple(TupleKind::Sum, _) => {
							// Tuple downcast, aka just indexing into the data field
							let val = self.generate_operand(from, val);
							let tmp = self.builder.build_alloca(val.get_type(), "");

							self.builder.build_store(tmp, val);

							let gep = self.builder.build_struct_gep(tmp, 1, "").unwrap();

							let cast = self
								.builder
								.build_bitcast(
									gep,
									Self::to_basic_type(self.get_llvm_type(to))
										.ptr_type(AddressSpace::Generic),
									"",
								)
								.into_pointer_value();

							self.builder.build_store(
								store,
								self.builder.build_load(cast, "").as_basic_value_enum(),
							)
						}

						_ => todo!(),
					},
				}
			}
		}
	}

	fn generate_operand(&self, ty: &Type, expr: &Operand) -> BasicValueEnum<'ctx> {
		match expr {
			Operand::StringLit(s, _) => {
				let len = s.as_bytes().len().try_into().unwrap();
				let string_t = self.context.i8_type().array_type(len);
				let val = self
					.module
					.add_global(string_t, Some(AddressSpace::Const), ".str");

				let literal = self.context.const_string(s.as_bytes(), false);

				val.set_visibility(GlobalVisibility::Hidden);
				val.set_linkage(Linkage::Private);
				val.set_unnamed_addr(true);
				val.set_initializer(&literal);

				self.slice_type(&self.context.i8_type())
					.const_named_struct(&[
						val.as_pointer_value().as_basic_value_enum(),
						self.context
							.i64_type()
							.const_int(len.into(), false)
							.as_basic_value_enum(),
					])
					.as_basic_value_enum()
			}

			Operand::CStringLit(s, _) => {
				let val = self.module.add_global(
					self.context
						.i8_type()
						.array_type(s.as_bytes_with_nul().len() as u32),
					Some(AddressSpace::Const),
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

				self.builder
					.build_address_space_cast(
						self.builder
							.build_bitcast(
								val.as_pointer_value(),
								self.context.i8_type().ptr_type(AddressSpace::Const),
								"",
							)
							.into_pointer_value(),
						self.context.i8_type().ptr_type(AddressSpace::Generic),
						"",
					)
					.as_basic_value_enum()
			}

			Operand::IntegerLit(i, _) => Self::to_basic_type(self.get_llvm_type(ty))
				.into_int_type()
				.const_int(*i as u64, true)
				.as_basic_value_enum(),

			Operand::FloatLit(f, _) => Self::to_basic_type(self.get_llvm_type(ty))
				.into_float_type()
				.const_float(*f)
				.as_basic_value_enum(),

			Operand::BoolLit(b, _) => self
				.context
				.bool_type()
				.const_int(u64::from(*b), false)
				.as_basic_value_enum(),

			Operand::LValueUse(lval, props) => self.generate_lvalue_use(lval, *props),

			Operand::Undef => self.get_undef(&Self::to_basic_type(self.get_llvm_type(ty))),
		}
	}

	fn generate_lvalue_use(&self, expr: &LValue, props: BindingProps) -> BasicValueEnum<'ctx> {
		// Get the variable pointer from the function
		let (mut local, lprops, ty) = &self.variables[expr.local];

		// If the lvalue is a reference, perform a load
		// so we're left with a single indirection
		if self.pass_by_ptr(ty, lprops) {
			local = self
				.builder
				.build_load(local, "")
				.as_basic_value_enum()
				.into_pointer_value();
		}

		// Perform geps and whatnot to get a pointer to the sublocation

		for proj in &expr.projection {
			local = match proj {
				PlaceElem::Deref => self
					.builder
					.build_load(local, "")
					.as_basic_value_enum()
					.into_pointer_value(),

				PlaceElem::Field(i) => self.builder.build_struct_gep(local, *i as u32, "").unwrap(),

				PlaceElem::Index(index_ty, expr, op) => {
					let mut idx = self
						.generate_operand(index_ty, expr)
						.as_basic_value_enum()
						.into_int_value();

					if *op == Operator::Sub {
						idx = self.builder.build_int_neg(idx, "");
					}

					local = self.builder.build_load(local, "").into_pointer_value();

					unsafe { self.builder.build_gep(local, &[idx], "") }
				}
			}
		}

		if props.is_ref {
			local.as_basic_value_enum()
		} else {
			self.builder.build_load(local, "")
		}
	}

	fn generate_prototype(&mut self, t: &CIRFunction) -> LLVMResult<FunctionType<'ctx>> {
		let types_mapped: Vec<_> = t.variables[0..t.arg_count]
			.iter()
			.map(|(ty, props, _)| {
				if self.pass_by_ptr(ty, props) {
					Self::to_basic_metadata_type(self.get_llvm_type(&ty.ptr_type(props.is_mut)))
				} else {
					Self::to_basic_metadata_type(self.get_llvm_type(ty))
				}
			})
			.collect();

		let ret = if self.pass_by_ptr(&t.ret.1, &t.ret.0) {
			self.get_llvm_type(&t.ret.1.ptr_type(t.ret.0.is_mut))
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
	) -> PointerValue<'ctx> {
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
			AnyTypeEnum::FunctionType(_) => panic!("attempted to convert FunctionType to BasicTypeEnum!"),
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
				.ptr_type(AddressSpace::Generic)
				.as_any_type_enum(),

			Type::Pointer { pointee, .. } => {
				match &**pointee {
					Type::Slice(slicee) => self
						.slice_type(&Self::to_basic_type(self.get_llvm_type(slicee)))
						.as_any_type_enum(),

					// void* isn't valid in LLVM, so we generate an i8* type instead
					Type::Basic(Basic::Void) => self
						.context
						.i8_type()
						.ptr_type(AddressSpace::Generic)
						.as_any_type_enum(),

					_ => Self::to_basic_type(self.get_llvm_type(pointee))
						.ptr_type(AddressSpace::Generic)
						.as_any_type_enum(),
				}
			}

			Type::TypeRef { .. } => {
				let ir_typename = ty.get_ir_typename();
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
				.ptr_type(AddressSpace::Generic)
				.as_any_type_enum()
			}

			Type::TypeParam(_) => panic!("unexpected TypeParam in codegen!"),

			Type::Unresolved { .. } => panic!(),

			Type::Never => panic!(),
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
}
