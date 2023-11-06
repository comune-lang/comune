use std::{
	collections::HashMap,
	sync::{Arc, RwLock},
};

use crate::{
	ast::{
		controlflow::ControlFlow,
		expression::{Atom, Expr, FnRef, Operator, XtorKind},
		module::{ModuleASTElem, ModuleImpl, ModuleInterface, ModuleItemInterface, Name},
		pattern::{Binding, Pattern},
		statement::Stmt,
		types::{Basic, BindingProps, FnPrototype, GenericArgs, Type, TypeDef, PtrKind},
	},
	lexer::SrcSpan,
	parser::Parser,
};

use super::{
	BlockIndex, CIRBlock, CIRCallId, CIRFunction, CIRModule, CIRStmt, LValue, Operand, PlaceElem,
	RValue, VarIndex,
};

#[derive(Clone)]
pub struct CIRBuilderScope {
	start: BlockIndex,
	end: Option<BlockIndex>,
	#[allow(dead_code)]
	label: Option<Name>,
	variables: Vec<(Option<Name>, VarIndex)>,
	is_loop: bool,
}

pub struct CIRModuleBuilder {
	pub module: CIRModule,

	current_fn: Option<CIRFunction>,
	current_block: BlockIndex,
	scope_stack: Vec<CIRBuilderScope>,
}

impl CIRModuleBuilder {
	pub fn from_ast(ast: &Parser) -> Self {
		let mut result = CIRModuleBuilder {
			module: CIRModule {
				types: HashMap::new(),
				globals: HashMap::new(),
				functions: HashMap::new(),
				impl_solver: ast.interface.impl_solver.clone(),
			},

			current_fn: None,
			current_block: 0,
			scope_stack: vec![],
		};

		result.register_module(&ast.interface);
		result.generate_module(&ast.module_impl);

		result
	}

	fn register_module(&mut self, module: &ModuleInterface) {
		assert!(module.is_typed);

		for (_, im) in &module.impl_solver.impls {
			let im = &*im.read().unwrap();

			for (_, fns) in &im.functions {
				for func in fns {
					let cir_fn = Self::generate_prototype(&func);

					self.module.functions.insert(func.clone(), cir_fn);
				}
			}
		}

		//for import in module.imported.values() {
		//	assert!(import.interface.is_typed);

		//	self.register_module(&import.interface);
		//}

		for (id, item) in &module.children {
			match item {
				ModuleItemInterface::Functions(fns) => {
					for func in &*fns.read().unwrap() {
						let cir_fn = Self::generate_prototype(func);

						self.module.functions.insert(func.clone(), cir_fn);
					}
				}

				ModuleItemInterface::Type(ty) => {
					self.register_typedef(ty);
				}

				ModuleItemInterface::Variable(var) => {
					let ty = var.read().unwrap().clone();
					
					self.module.globals.insert(id.clone(), (ty.clone(), RValue::undef(ty)));
				}

				_ => {}
			}
		}
	}

	fn register_typedef(&mut self, ty: &Arc<RwLock<TypeDef>>) {
		self.module
			.types
			.insert(ty.read().unwrap().name.to_string(), ty.clone());

		for (_, variant) in &ty.read().unwrap().variants {
			self.register_typedef(variant);
		}

		if let Some(drop) = &ty.read().unwrap().drop {
			let cir_fn = Self::generate_prototype(&drop);

			self.module.functions.insert(drop.clone(), cir_fn);
		}

		for init in &ty.read().unwrap().init {
			let proto = init.clone();
			let cir_fn = Self::generate_prototype(&proto);

			self.module.functions.insert(proto, cir_fn);
		}
	}

	fn generate_module(&mut self, module_impl: &ModuleImpl) {
		for (func, ast) in &module_impl.fn_impls {
			let ModuleASTElem::Parsed(ast) = ast else { panic!() };

			self.generate_function(&func, ast);
		}
	}

	pub fn generate_prototype(func: &FnPrototype) -> CIRFunction {
		CIRFunction {
			variables: func
				.params
				.params
				.iter()
				.map(|(ty, name, props)| (ty.clone(), *props, name.clone()))
				.collect(),
			blocks: vec![],
			ret: func.ret.clone(),
			arg_count: func.params.params.len(),
			generics: func.generics.clone(),
			attributes: func.attributes.clone(),
			is_extern: true,
			is_variadic: func.params.variadic,
		}
	}

	pub fn generate_function(&mut self, proto: &FnPrototype, fn_block: &Expr) {
		let Some((proto, func)) = self.module.functions.remove_entry(proto) else {
			panic!(
				"failed to get cIR function {proto} from module! function list:\n\n{:?}\n",
				self.module.functions.keys()
			)
		};

		self.current_fn = Some(func);
		self.scope_stack.clear();
		self.current_block = 0;

		let mut params_map = vec![];

		// Insert function parameters into name stack
		for (i, (.., name)) in self.get_fn().variables.iter().enumerate() {
			if let Some(name) = name {
				params_map.push((Some(name.clone()), i));
			}
		}

		self.scope_stack.push(CIRBuilderScope {
			start: 0,
			end: None,
			label: None,
			variables: params_map,
			is_loop: false,
		});

		if !proto.ret.1.is_void_or_never() {
			// If the return type isn't void, insert a
			// variable to write the return value to
			let mut props = proto.ret.0;
			props.is_mut = true;

			self.insert_variable(Some("return".into()), props, proto.ret.1.clone());
		}

		// Generate function body
		self.append_block();

		let _ = self.generate_expr(fn_block, BindingProps::default());

		let func = self.get_fn_mut();
		func.is_extern = false;

		// Find block preds & succs

		for i in 0..func.blocks.len() {
			if func.blocks[i].items.is_empty() {
				panic!("encountered empty basic block in cIR!");
			}

			let succs = match func.blocks[i].items.last().unwrap() {
				CIRStmt::Invoke { next, except, .. } => vec![*next, *except],

				CIRStmt::Jump(jmp) => vec![*jmp],

				CIRStmt::Switch(_, branches, else_idx) => {
					let mut result = vec![];
					result.reserve(branches.len() + 1);
					result.extend(branches.iter().map(|(.., idx)| *idx));
					result.push(*else_idx);

					result
				}

				CIRStmt::Return => vec![],

				CIRStmt::DropShim { next, .. } => vec![*next],

				CIRStmt::Unreachable => vec![],

				term => panic!("invalid terminator in cIR: {term}"),
			};

			for succ in &succs {
				func.blocks[*succ].preds.push(i);
			}

			func.blocks[i].succs = succs;
		}


		self.module
			.functions
			.insert(proto, self.current_fn.take().unwrap());
	}

	// Shorthand
	fn get_fn_mut(&mut self) -> &mut CIRFunction {
		self.current_fn.as_mut().unwrap()
	}

	fn get_fn(&self) -> &CIRFunction {
		self.current_fn.as_ref().unwrap()
	}

	fn write(&mut self, stmt: CIRStmt) {
		self.current_fn.as_mut().unwrap().blocks[self.current_block]
			.items
			.push(stmt)
	}

	fn append_block(&mut self) -> BlockIndex {
		self.get_fn_mut().blocks.push(CIRBlock {
			items: vec![],
			preds: vec![],
			succs: vec![],
		});
		self.current_block = self.get_fn().blocks.len() - 1;
		self.current_block
	}

	#[must_use]
	fn generate_stmt(&mut self, stmt: &Stmt) -> Option<()> {
		match stmt {
			Stmt::Expr(expr) => {
				// RValues have no side effects, so we can discard the result
				// of this expression. However, we still propagate whether it
				// returns normally or not.
				self.generate_expr(expr, BindingProps::default())
					.map(|_| ())
			}

			Stmt::Decl(bindings, expr, _) => {
				if bindings.len() != 1 {
					todo!()
				}

				// TODO: Handle destructuring assignment
				let (ty, name, props) = &bindings[0];

				let val = if let Some(expr) = expr {
					// Stop building early if the expression never returns
					let result = self.generate_expr(expr, *props)?;

					Some(result)
				} else {
					None
				};

				let var = self.insert_variable(Some(name.clone()), *props, ty.clone());

				self.write(CIRStmt::StorageLive(var.local));

				if let Some(val) = val {
					self.generate_raw_assign(ty, var, val);
				}

				Some(())
			}
		}
	}

	// For a given pattern match, generate the appropriate bindings
	fn generate_pattern_bindings(&mut self, pattern: Pattern, mut value: LValue, value_ty: &Type) {
		match pattern {
			Pattern::Binding(Binding {
				name: Some(name),
				ty,
				props,
			}) => {
				let idx = self.get_fn().variables.len();

				self.get_fn_mut()
					.variables
					.push((ty.clone(), props, Some(name.clone())));

				self.scope_stack
					.last_mut()
					.unwrap()
					.variables
					.push((Some(name.clone()), idx));

				let store_place = LValue {
					local: self.get_fn().variables.len() - 1,
					projection: vec![],
					props,
				};

				if value_ty.get_variant_index(&ty).is_some() {
					value.projection.push(PlaceElem::SumData(ty.clone()));

					self.generate_raw_assign(
						&ty,
						store_place,
						RValue::lvalue_use(ty.clone(), value, props),
					);
				} else if &ty != value_ty {
					self.generate_raw_assign(
						&ty,
						store_place,
						RValue::Cast {
							to: ty.clone(),
							from: value_ty.clone(),
							val: Operand::LValueUse(value, props),
							span: SrcSpan::new(),
						},
					);
				} else {
					self.generate_raw_assign(
						&ty,
						store_place,
						RValue::lvalue_use(ty.clone(), value, props),
					);
				}
			}

			Pattern::Binding(Binding { name: None, .. }) => {}

			Pattern::Destructure { patterns, pattern_ty, .. } => {
				if value_ty.get_variant_index(&pattern_ty).is_some() {
					value.projection.push(PlaceElem::SumData(pattern_ty.clone()));
				}

				for (i, pattern) in patterns.iter().enumerate() {
					let lval = value.clone().projected(vec![PlaceElem::Field(i)]);
					self.generate_pattern_bindings(pattern.1.clone(), lval, pattern.1.get_type());
				}
			}

			_ => todo!(),
		}
	}

	#[must_use]
	fn generate_block(
		&mut self,
		items: &Vec<Stmt>,
		result: &Option<Box<Expr>>,
		append_current: bool,
	) -> (BlockIndex, Option<RValue>) {
		let jump_idx = if append_current {
			self.current_block
		} else {
			self.append_block()
		};

		let result_location = if let Some(result) = result {
			if result.get_type().is_void_or_never() {
				None
			} else {
				Some(self.insert_variable(None, BindingProps::value(), result.get_type().clone()))
			}
		} else {
			None
		};

		self.generate_scope_start();

		for item in items {
			if self.generate_stmt(item).is_none() {
				// Be sure to pop the scope stack when returning early,
				// otherwise drops will get desynced from the actual scopes
				self.scope_stack.pop();
				return (jump_idx, None);
			}
		}

		// Check if the block has a result statement
		if let Some(result) = result {
			let Some(result_ir) = self.generate_expr(result, self.get_fn().ret.0) else {
				self.scope_stack.pop();
				return (jump_idx, None);
			};

			if let Some(result_location) = result_location {
				self.generate_raw_assign(result.get_type(), result_location.clone(), result_ir);
				self.generate_scope_end();

				(
					jump_idx,
					Some(RValue::Atom(
						result.get_type().clone(),
						None,
						Operand::LValueUse(result_location.clone(), result_location.props),
						result.get_span(),
					)),
				)
			} else {
				self.generate_scope_end();
				(jump_idx, Some(Self::get_void_rvalue()))
			}
		} else {
			self.generate_scope_end();
			(jump_idx, Some(Self::get_void_rvalue()))
		}
	}

	#[must_use]
	fn generate_lvalue_block(
		&mut self,
		items: &Vec<Stmt>,
		result: &Option<Box<Expr>>,
		append_current: bool,
	) -> (BlockIndex, Option<LValue>) {
		let jump_idx = if append_current {
			self.current_block
		} else {
			self.append_block()
		};

		let result_location = if let Some(result) = result {
			if result.get_type().is_void_or_never() {
				None
			} else {
				Some(self.insert_variable(
					None,
					BindingProps::mut_reference(),
					result.get_type().clone(),
				))
			}
		} else {
			None
		};

		self.generate_scope_start();

		for item in items {
			if self.generate_stmt(item).is_none() {
				// Be sure to pop the scope stack when returning early,
				// otherwise drops will get desynced from the actual scopes
				self.scope_stack.pop();
				return (jump_idx, None);
			}
		}

		// Block must have a result expression, this is an lvalue context
		let Some(result) = result else {
			panic!()
		};

		let Some(result_ir) = self.generate_lvalue_expr(result) else {
			self.scope_stack.pop();
			return (jump_idx, None);
		};

		let Some(result_location) = result_location else {
			panic!()
		};

		self.write(CIRStmt::RefInit(result_location.local, result_ir));

		self.generate_scope_end();

		(jump_idx, Some(result_location))
	}

	fn generate_raw_assign(&mut self, location_ty: &Type, location: LValue, expr: RValue) {
		assert!(!expr.get_type().is_void_or_never());

		if location_ty != expr.get_type() {
			panic!("mismatched assignment from {} to {location_ty}", expr.get_type());
		}

		if let RValue::Cast { from, to, val, span } = &expr {
			if let Some(idx) = to.get_variant_index(from) {
				// this is a sum type upcast, so we have to 
				// create a temporary to store the full value in
				//
				// (if we just assigned this to the location directly
				// it'd trip up either init analysis or mutation analysis) 
				
				let tmp = self.insert_temporary(
					location_ty, 
					RValue::undef(location_ty.clone()), 
					SrcSpan::new()
				);

				let mut disc_loc = tmp.clone();
				let mut data_loc = tmp.clone();
				disc_loc.projection.push(PlaceElem::SumDisc);
				data_loc.projection.push(PlaceElem::SumData(from.clone()));

				self.write(CIRStmt::Assignment(
					data_loc, 
					RValue::Atom(
						from.clone(),
						None,
						val.clone(), 
						*span
					)
				));

				self.write(CIRStmt::Assignment(
					disc_loc, 
					RValue::Atom(
						Type::Basic(location_ty.get_discriminant_type().unwrap()),
						None,
						Operand::IntegerLit(idx as i128, SrcSpan::new()),
						SrcSpan::new()
					)
				));

				self.write(CIRStmt::Assignment(
					location, 
					RValue::lvalue_use(
						location_ty.clone(),
						tmp,
						BindingProps::value()
					)
				));

				return
			}
		}

		// normal assignment
		self.write(CIRStmt::Assignment(location, expr));
	}

	fn generate_drop_and_assign(&mut self, location_ty: &Type, location: LValue, expr: RValue) {
		if expr.get_type().needs_drop() {
			self.generate_drop_shim(location.clone());
		}

		self.generate_raw_assign(location_ty, location, expr);
	}
	
	fn generate_scope_start(&mut self) {
		self.scope_stack.push(CIRBuilderScope {
			start: self.current_block,
			end: None,
			label: None,
			variables: vec![],
			is_loop: false,
		});
	}

	fn generate_scope_end(&mut self) {
		let scope = self.scope_stack.pop().unwrap();

		for (_, var) in scope.variables.into_iter().rev() {
			if self.needs_eol_drop(var) {
				self.generate_drop_shim(self.get_local_lvalue(var));
			}
			self.write(CIRStmt::StorageDead(var));
		}
	}

	fn generate_drop_shim(&mut self, var: LValue) {
		let current = self.current_block;
		let next = self.append_block();

		self.current_block = current;
		self.write(CIRStmt::DropShim { var, next });
		self.current_block = next;
	}

	fn needs_eol_drop(&self, var: VarIndex) -> bool {
		if self.get_fn().is_lang_function("forget") {
			return false;
		}

		let (ty, props, _) = &self.get_fn().variables[var];

		!props.is_ref && !self.is_return_location(var) && ty.needs_drop()
	}

	fn is_return_location(&self, var: VarIndex) -> bool {
		var == 0 && !self.current_fn.as_ref().unwrap().ret.1.is_void()
	}

	// generate_expr only returns None if `expr` is a "never expression"
	// aka an expression that will never evaluate to a value
	#[must_use]
	fn generate_expr(&mut self, expr: &Expr, qualifs: BindingProps) -> Option<RValue> {
		let expr_ty = expr.get_type();
		let span = expr.get_span();

		match expr {
			Expr::Atom(atom, _) => match atom {
				Atom::IntegerLit(i, b) => Some(if let Some(b) = b {
					RValue::Atom(Type::Basic(*b), None, Operand::IntegerLit(*i, span), span)
				} else {
					RValue::Atom(expr_ty.clone(), None, Operand::IntegerLit(*i, span), span)
				}),

				Atom::FloatLit(f, b) => Some(if let Some(b) = b {
					RValue::Atom(Type::Basic(*b), None, Operand::FloatLit(*f, span), span)
				} else {
					RValue::Atom(expr_ty.clone(), None, Operand::FloatLit(*f, span), span)
				}),

				Atom::BoolLit(b) => Some(RValue::Atom(
					Type::Basic(Basic::Bool),
					None,
					Operand::BoolLit(*b, span),
					span,
				)),

				Atom::StringLit(s) => Some(RValue::Atom(
					Type::Slice(Box::new(Type::i8_type(false))).ptr_type(PtrKind::Shared),
					None,
					Operand::StringLit(s.clone(), span),
					span,
				)),

				Atom::CStringLit(s) => Some(RValue::Atom(
					Type::Pointer(Box::new(Type::i8_type(false)), PtrKind::Shared),
					None,
					Operand::CStringLit(s.clone(), span),
					span,
				)),

				Atom::ArrayLit(elems) => {
					let tmp = self.insert_temporary(
						expr_ty,
						RValue::Atom(expr_ty.clone(), None, Operand::Undef, span),
						span,
					);

					for (i, expr) in elems.iter().enumerate() {
						let expr_ir = self.generate_expr(expr, BindingProps::default())?;

						let mut tmp_idx = tmp.clone();
						tmp_idx.projection.push(PlaceElem::Index {
							index_ty: Type::isize_type(false),
							index: Operand::IntegerLit(i as i128, SrcSpan::new()),
							op: Operator::Add,
						});

						self.generate_raw_assign(expr.get_type(), tmp_idx, expr_ir)
					}

					Some(RValue::Atom(
						expr_ty.clone(),
						None,
						Operand::LValueUse(tmp, BindingProps::value()),
						span,
					))
				}

				Atom::Identifier(_) => {
					let lval = self.generate_lvalue_expr(expr)?;

					Some(RValue::Atom(
						self.get_fn().variables[lval.local].0.clone(),
						None,
						Operand::LValueUse(
							lval,
							qualifs,
						),
						span,
					))
				}

				Atom::Cast(expr, to) => {
					let from = expr.get_type().clone();
					let to = to.clone();

					self.generate_expr(expr, BindingProps::default())
						.map(|castee| RValue::Cast {
							val: self.get_as_operand(&from, castee, span),
							from,
							to,
							span,
						})
				}

				Atom::FnCall {
					resolved,
					args,
					generic_args,
					..
				} => self.generate_fn_call(args, generic_args, resolved, span),

				Atom::Drop(dropped) => {
					let lvalue = self.generate_lvalue_expr(dropped)?;

					self.generate_drop_shim(lvalue);

					Some(Self::get_void_rvalue())
				}

				Atom::Constructor {
					kind,
					def,
					generic_args,
					placement,
				} => {
					let ty = Type::TypeRef {
						def: def.clone(),
						args: generic_args.clone(),
					};

					match kind {
						XtorKind::Literal { fields } => {
							// Literal constructor, like `new Type { field: expr, }`

							let location = if let Some(placement) = placement {
								self.generate_lvalue_expr(&placement)?
							} else {
								self.insert_temporary(
									&ty,
									RValue::Atom(ty.clone(), None, Operand::Undef, SrcSpan::new()),
									SrcSpan::new(),
								)
							};

							let mut indices = vec![];

							let def = def.upgrade().unwrap();
							let def = def.read().unwrap();

							for (field, _) in fields {
								indices.push(
									def.members
										.iter()
										.position(|(name, ..)| name == field)
										.unwrap(),
								);
							}

							for i in 0..indices.len() {
								let mem_expr =
									self.generate_expr(&fields[i].1, BindingProps::default());
								let mut mem_lval = location.clone();

								mem_lval.projection.push(PlaceElem::Field(indices[i]));
								mem_lval.props.span = fields[i].1.get_span();

								if let Some(mem_expr) = mem_expr {
									self.generate_raw_assign(fields[i].1.get_type(), mem_lval, mem_expr)
								}
							}

							if placement.is_some() {
								Some(Self::get_void_rvalue())
							} else {
								Some(RValue::Atom(
									ty.clone(),
									None,
									Operand::LValueUse(location, qualifs),
									span,
								))
							}
						}

						XtorKind::Constructor { args, resolved } => {
							if placement.is_some() {
								self.generate_fn_call(args, generic_args, resolved, span)
							} else {
								panic!("non-placement constructor call must be desugared!")
							}
						}
					}
				}

				Atom::Block { items, result, .. } => self.generate_block(items, result, true).1,

				Atom::CtrlFlow(ctrl) => match &**ctrl {
					ControlFlow::Return { expr } => {
						if let Some(expr) = expr {
							if let Some(lval) = self.get_fn().get_return_lvalue() {
								if self.get_fn().ret.0.is_ref {
									// The return type is a reference, use RefInit
									let ret = self.generate_lvalue_expr(expr)?;

									self.write(CIRStmt::RefInit(lval.local, ret));
								} else {
									// The return type is a plain value, just assign it
									let ret = self.generate_expr(expr, self.get_fn().ret.0)?;

									self.generate_raw_assign(&self.get_fn().ret.1.clone(), lval, ret);
								}
							}
						}

						for scope in self.scope_stack.clone().into_iter().rev() {
							for (_, var) in scope.variables.iter().rev() {
								if self.needs_eol_drop(*var) {
									self.generate_drop_shim(self.get_local_lvalue(*var));
								}
							}
						}

						self.write(CIRStmt::Return);
						None
					}

					ControlFlow::If {
						cond,
						body: Expr::Atom(Atom::Block { items, result, .. }, _),
						else_body,
					} => {
						let result_loc = if !expr_ty.is_void_or_never() {
							Some(self.insert_temporary(
								expr_ty,
								RValue::Atom(expr_ty.clone(), None, Operand::Undef, span),
								span,
							))
						} else {
							None
						};

						// Generate condition directly in current block, since we don't need to jump back to it
						let cond_ir = self.generate_expr(cond, BindingProps::default())?;
						let cond_ty = cond.get_type();
						let cond_op = self.get_as_operand(cond_ty, cond_ir, cond.get_span());

						let start_block = self.current_block;

						let mut cont_block = None;

						let (if_idx, block_ir) = self.generate_block(items, result, false);

						if let Some(if_val) = block_ir {
							if let Some(result) = &result_loc {
								self.generate_raw_assign(expr_ty, result.clone(), if_val);
							}

							if cont_block.is_none() {
								let current = self.current_block;
								cont_block = Some(self.append_block());
								self.current_block = current;
							}

							self.write(CIRStmt::Jump(cont_block.unwrap()));
						}

						if let Some(Expr::Atom(
							Atom::Block {
								items: else_items,
								result: else_result,
								..
							},
							_,
						)) = else_body
						{
							let (else_idx, else_ir) =
								self.generate_block(else_items, else_result, false);

							if let Some(else_val) = else_ir {
								if let Some(result) = &result_loc {
									self.generate_raw_assign(expr_ty, result.clone(), else_val);
								}

								if cont_block.is_none() {
									let current = self.current_block;
									cont_block = Some(self.append_block());
									self.current_block = current;
								}

								self.write(CIRStmt::Jump(cont_block.unwrap()));
							}

							self.current_block = start_block;
							self.generate_branch(cond_op, if_idx, else_idx);

							if let Some(cont_block) = cont_block {
								self.current_block = cont_block;
							}
						} else {
							if cont_block.is_none() {
								let current = self.current_block;
								cont_block = Some(self.append_block());
								self.current_block = current;
							}

							self.current_block = start_block;
							self.generate_branch(cond_op, if_idx, cont_block.unwrap());
							self.current_block = cont_block.unwrap();
						}

						if cont_block.is_some() {
							if let Some(result) = result_loc {
								Some(RValue::Atom(
									expr_ty.clone(),
									None,
									Operand::LValueUse(result, BindingProps::value()),
									span,
								))
							} else {
								Some(RValue::Atom(expr_ty.clone(), None, Operand::Undef, span))
							}
						} else {
							None
						}
					}

					ControlFlow::While {
						cond,
						body: Expr::Atom(Atom::Block { items, result, .. }, _),
					} => {
						let start_block = self.current_block;
						let cond_block = self.append_block();

						let cond_ir = self.generate_expr(cond, BindingProps::default())?;
						let cond_ty = cond.get_type();
						let cond_op = self.get_as_operand(cond_ty, cond_ir, cond.get_span());

						let cond_write_block = self.current_block;

						let next_block = self.append_block();

						// Write jump-to-cond statement to start block
						self.current_block = start_block;
						self.write(CIRStmt::Jump(cond_block));

						self.scope_stack.push(CIRBuilderScope {
							start: start_block,
							end: Some(next_block),
							label: None,
							variables: vec![],
							is_loop: true,
						});

						// Generate body
						let (body_idx, result) = self.generate_block(items, result, false);

						self.scope_stack.pop();

						// Only write a terminator if the block returns
						if result.is_some() {
							// Write jump-to-cond statement to body block
							self.write(CIRStmt::Jump(cond_block));
						}

						self.current_block = cond_write_block;
						self.generate_branch(cond_op, body_idx, next_block);

						self.current_block = next_block;

						Some(Self::get_void_rvalue())
					}

					ControlFlow::For {
						init,
						cond,
						iter,
						body,
					} => {
						// Write init to start block
						if let Some(init) = init {
							self.generate_stmt(init)?;
						}

						let start_block = self.current_block;
						let body_block = self.append_block();

						// Generate body
						self.generate_expr(body, BindingProps::default())?;

						// Add iter statement to body
						if let Some(iter) = iter {
							self.generate_expr(iter, BindingProps::default())?;
						}

						let body_write_block = self.current_block;
						let loop_block = self.append_block();

						self.current_block = body_write_block;
						self.write(CIRStmt::Jump(loop_block));

						self.current_block = start_block;
						self.write(CIRStmt::Jump(loop_block));

						let next_block = self.append_block();

						self.current_block = loop_block;

						if let Some(cond) = cond {
							if let Some(cond_ir) = self.generate_expr(cond, BindingProps::default())
							{
								let cond_ty = cond.get_type();
								let cond_op =
									self.get_as_operand(cond_ty, cond_ir, cond.get_span());

								self.generate_branch(cond_op, body_block, next_block);
							}
						} else {
							self.write(CIRStmt::Jump(body_block));
						}

						self.current_block = next_block;

						Some(Self::get_void_rvalue())
					}

					ControlFlow::Break | ControlFlow::Continue => {
						let is_break = matches!(&**ctrl, ControlFlow::Break);

						// Iterate backwards through scope stack to find loop scope
						for i in (0..self.scope_stack.len()).rev() {
							// Generate drop shims for variables inside loop
							let scope_names = self.scope_stack[i].variables.clone();

							for (_, var) in scope_names.into_iter().rev() {
								if self.needs_eol_drop(var) {
									self.generate_drop_shim(self.get_local_lvalue(var));
								}
							}

							if !self.scope_stack[i].is_loop {
								continue;
							}

							if is_break {
								let Some(end) = self.scope_stack[i].end else {
									panic!();
								};

								self.write(CIRStmt::Jump(end));
							} else {
								self.write(CIRStmt::Jump(self.scope_stack[i].start));
							}

							return None;
						}

						panic!();
					}

					ControlFlow::Match {
						scrutinee,
						branches,
					} => {
						let scrutinee_lval = self.generate_lvalue_expr(scrutinee)?;
						let scrutinee_ty = scrutinee.get_type();

						let mut branches_ir = vec![];
						let mut has_result = false;

						let disc_lval;
						let disc_ty = Type::Basic(scrutinee_ty.get_discriminant_type().unwrap());

						let start_block = self.current_block;

						let result_loc = if !expr_ty.is_void_or_never() {
							Some(self.insert_temporary(
								expr_ty,
								RValue::Atom(expr_ty.clone(), None, Operand::Undef, SrcSpan::new()),
								span,
							))
						} else {
							None
						};

						if Self::is_trivially_matchable(branches, scrutinee.get_type()) {
							let mut trivial_disc_lval = scrutinee_lval.clone();

							trivial_disc_lval.projection.push(PlaceElem::SumDisc);

							disc_lval = trivial_disc_lval;

							for (pattern, _) in branches.iter() {
								branches_ir.push((
									disc_ty.clone(),
									Operand::IntegerLit(
										Self::get_trivial_match_value(pattern, scrutinee.get_type())
											as i128,
										SrcSpan::new(),
									),
									0,
								));
							}
						} else {
							// Generate switch discriminant calculation
							disc_lval = self.insert_temporary(
								&disc_ty,
								RValue::Atom(
									disc_ty.clone(),
									None,
									Operand::IntegerLit(0, SrcSpan::new()),
									SrcSpan::new(),
								),
								SrcSpan::new(),
							);

							for (i, (pattern, _)) in branches.iter().enumerate() {
								// TODO: There is no usefulness checking here - if a value
								// matches multiple branches, this will probably break
								let match_expr = self.generate_match_expr(
									pattern,
									&scrutinee_lval,
									&scrutinee_ty,
								);
								let match_operand = self.get_as_operand(
									&Type::Basic(Basic::Bool),
									match_expr,
									scrutinee.get_span(),
								);

								let cast_ir = self.get_as_operand(
									&disc_ty,
									RValue::Cast {
										from: Type::Basic(Basic::Bool),
										to: disc_ty.clone(),
										val: match_operand,
										span: SrcSpan::new(),
									},
									SrcSpan::new(),
								);

								let mult_ir = self.get_as_operand(
									&disc_ty,
									RValue::Cons(
										disc_ty.clone(),
										[
											(
												disc_ty.clone(),
												Operand::IntegerLit(i as i128 + 1, SrcSpan::new()),
											),
											(disc_ty.clone(), cast_ir),
										],
										Operator::Mul,
										SrcSpan::new(),
									),
									SrcSpan::new(),
								);

								let add_ir = CIRStmt::Assignment(
									disc_lval.clone(),
									RValue::Cons(
										disc_ty.clone(),
										[
											(
												disc_ty.clone(),
												Operand::LValueUse(
													disc_lval.clone(),
													BindingProps::value(),
												),
											),
											(disc_ty.clone(), mult_ir.clone()),
										],
										Operator::Add,
										SrcSpan::new(),
									),
								);

								self.write(add_ir);

								branches_ir.push((
									disc_ty.clone(),
									Operand::IntegerLit(i as i128 + 1, SrcSpan::new()),
									0,
								));
							}
						}

						let cont_block = self.append_block();

						if expr_ty.is_never() {
							self.write(CIRStmt::Unreachable);
						}

						// Generate branches
						for (i, (pattern, branch)) in branches.iter().enumerate() {
							let binding_idx = self.append_block();
							
							self.generate_scope_start();

							self.generate_pattern_bindings(
								pattern.clone(),
								scrutinee_lval.clone(),
								&scrutinee_ty,
							);

							let match_result = self.generate_expr(branch, qualifs);

							if let Some(match_result) = match_result {
								if let Some(result_loc) = &result_loc {
									self.generate_raw_assign(expr_ty, result_loc.clone(), match_result);
								}

								self.generate_scope_end();

								self.write(CIRStmt::Jump(cont_block));
								has_result = true;
							} else {
								self.scope_stack.pop();
							}

							self.current_block = cont_block;

							branches_ir[i].2 = binding_idx;
						}

						self.current_block = start_block;
						self.write(CIRStmt::Switch(
							Operand::LValueUse(disc_lval, BindingProps::value()),
							branches_ir,
							cont_block,
						));
						self.current_block = cont_block;

						if has_result {
							if let Some(result_loc) = result_loc {
								Some(RValue::Atom(
									expr_ty.clone(),
									None,
									Operand::LValueUse(result_loc, BindingProps::value()),
									span,
								))
							} else {
								Some(Self::get_void_rvalue())
							}
						} else {
							None
						}
					}

					_ => panic!("illegal CtrlFlow construction in cIR!"),
				},
			},

			Expr::Cons([lhs, rhs], op, _) => {
				if op.is_compound_assignment() {
					let op = op.get_compound_operator();
					let lval_ir = self.generate_lvalue_expr(lhs)?;
					let rval_ir = self.generate_expr(rhs, BindingProps::default())?;

					let l_ty = lhs.get_type();
					let r_ty = rhs.get_type();

					let r_tmp = self.get_as_operand(r_ty, rval_ir, rhs.get_span());

					let expr_ir = RValue::Cons(
						l_ty.clone(),
						[
							(
								l_ty.clone(),
								Operand::LValueUse(lval_ir.clone(), BindingProps::value()),
							),
							(r_ty.clone(), r_tmp),
						],
						op,
						expr.get_span(),
					);

					let expr_tmp = self.get_as_operand(l_ty, expr_ir, lhs.get_span());

					self.generate_drop_and_assign(
						l_ty,
						lval_ir.clone(),
						RValue::Atom(r_ty.clone(), None, expr_tmp, rhs.get_span()),
					);

					Some(Self::get_void_rvalue())
				} else {
					match op {
						Operator::MemberAccess => match &**rhs {
							Expr::Atom(
								Atom::FnCall {
									resolved,
									args,
									generic_args,
									..
								},
								_,
							) => self.generate_fn_call(args, generic_args, resolved, rhs.get_span()),

							Expr::Atom(Atom::Identifier(_), _) => {
								let lval = self.generate_lvalue_expr(expr)?;

								Some(RValue::Atom(
									expr_ty.clone(),
									None,
									Operand::LValueUse(lval, qualifs),
									span,
								))
							}

							_ => panic!(),
						},

						Operator::Subscr => {
							let lval = self.generate_lvalue_expr(expr)?;

							Some(RValue::Atom(
								expr_ty.clone(),
								None,
								Operand::LValueUse(lval, qualifs),
								span,
							))
						}

						Operator::Assign => {
							let lval_ir = self.generate_lvalue_expr(lhs)?;
							let rval_ir = self.generate_expr(rhs, BindingProps::value())?;
							let l_ty = lhs.get_type();
							let r_ty = rhs.get_type();

							let r_tmp = self.get_as_operand(r_ty, rval_ir, rhs.get_span());

							self.generate_drop_and_assign(
								l_ty,
								lval_ir.clone(),
								RValue::Atom(r_ty.clone(), None, r_tmp, rhs.get_span()),
							);

							Some(Self::get_void_rvalue())
						}

						_ => {
							let lhs_ir = self.generate_expr(lhs, BindingProps::default())?;
							let rhs_ir = self.generate_expr(rhs, BindingProps::default())?;
							let lhs_ty = lhs.get_type().clone();
							let rhs_ty = rhs.get_type().clone();

							let lhs_tmp = self.get_as_operand(&lhs_ty, lhs_ir, lhs.get_span());
							let rhs_tmp = self.get_as_operand(&rhs_ty, rhs_ir, lhs.get_span());

							Some(RValue::Cons(
								expr_ty.clone(),
								[(lhs_ty, lhs_tmp), (rhs_ty, rhs_tmp)],
								op.clone(),
								expr.get_span(),
							))
						}
					}
				}
			}

			Expr::Unary(sub, op, _) => {
				let sub_expr = self.generate_expr(sub, qualifs)?;
				let temp = self.get_as_operand(sub.get_type(), sub_expr, sub.get_span());

				Some(RValue::Atom(
					expr_ty.clone(),
					Some(op.clone()),
					temp,
					expr.get_span(),
				))
			}
		}
	}

	fn generate_fn_call(
		&mut self,
		args: &[Expr],
		generic_args: &GenericArgs,
		resolved: &FnRef,
		span: SrcSpan,
	) -> Option<RValue> {
		match resolved {
			FnRef::Direct(resolved) => {
				let (mut ret_props, ret) = resolved.ret.clone();
				let ret = ret.get_concrete_type(generic_args);
				
				if !ret_props.is_ref {
					ret_props.is_mut = true;
				}

				let result = if !ret.is_void_or_never() {
					Some(self.insert_variable(None, ret_props, ret.clone()))
				} else {
					None
				};

				self.scope_stack.push(CIRBuilderScope {
					start: self.current_block,
					end: None,
					label: None,
					variables: vec![],
					is_loop: false,
				});

				let cir_args: Vec<_> = args
					.iter()
					.enumerate()
					.map_while(|(i, arg)| {
						// If the function has a parameter matching this arg,
						// get its BindingProps, else use the default (for i.e. variadics)
						let props = if let Some((.., props)) = resolved.params.params.get(i) {
							*props
						} else {
							BindingProps::value()
						};

						if props.is_ref {
							let cir_expr = self.generate_lvalue_expr(arg)?;

							Some((cir_expr, arg.get_type().clone(), props))
						} else {
							let cir_expr = self.generate_expr(arg, props)?;

							if let RValue::Atom(ty, None, Operand::LValueUse(lval, _), _) = cir_expr {
								Some((lval, ty, props))
							} else {
								let temp = self.insert_temporary(
									arg.get_type(),
									cir_expr,
									arg.get_span()
								);

								Some((temp, arg.get_type().clone(), props))
							}
						}
					})
					.collect();

				if cir_args.len() < args.len() {
					// One of the expressions does not return,
					// so stop building the call here
					return None;
				}

				if !self.module.functions.contains_key(resolved) {
					let extern_proto = Self::generate_prototype(resolved);

					self.module.functions.insert(
						resolved.clone(),
						extern_proto
					);
				}
				
				self.write(CIRStmt::Call {
					id: CIRCallId::Direct(resolved.clone(), span),
					args: cir_args.clone(),
					generic_args: generic_args.clone(),
					result: result.clone(),
				});

				self.generate_scope_end();

				if let Some(result) = result {
					Some(RValue::Atom(
						ret,
						None,
						Operand::LValueUse(result, ret_props),
						span,
					))
				} else if ret.is_void() {
					Some(Self::get_void_rvalue())
				} else {
					self.write(CIRStmt::Unreachable);
					None
				}
			}

			FnRef::Indirect(expr) => {
				let fn_val_ir = self.generate_expr(expr, BindingProps::default())?;
				let fn_val_ty = fn_val_ir.get_type().clone();

				let local = if let RValue::Atom(_, None, Operand::LValueUse(lval, _), _) = fn_val_ir
				{
					lval
				} else {
					self.insert_temporary(fn_val_ir.get_type(), fn_val_ir.clone(), span)
				};

				let Type::Function(ret, params) = fn_val_ty else {
					panic!()
				};

				let cir_args: Vec<_> = args
					.iter()
					.enumerate()
					.map_while(|(i, arg)| {
						// If the function has a parameter matching this arg,
						// get its BindingProps, else use the default (for i.e. variadics)
						let props = if let Some((props, ..)) = params.get(i) {
							*props
						} else {
							BindingProps::default()
						};

						let cir_expr = self.generate_expr(arg, props)?;

						if let RValue::Atom(ty, None, Operand::LValueUse(lval, props), _) = cir_expr
						{
							Some((lval, ty, props))
						} else {
							Some((
								self.insert_temporary(
									arg.get_type(),
									cir_expr,
									arg.get_span(),
								),
								arg.get_type().clone(),
								BindingProps::value(),
							))
						}
					})
					.collect();

				if cir_args.len() < args.len() {
					// One of the expressions does not return,
					// so stop building the call here
					return None;
				}

				let result = if ret.is_void() {
					None
				} else {
					// TODO: BindingProps for return type
					Some(self.insert_variable(None, BindingProps::default(), *ret.clone()))
				};

				self.write(CIRStmt::Call {
					id: CIRCallId::Indirect {
						local,
						ret: *ret.clone(),
						args: params
							.into_iter()
							.map(|(props, ty)| (ty, None, props))
							.collect(),
						span: expr.get_span(),
					},
					args: cir_args,
					generic_args: vec![],
					result: result.clone(),
				});

				if let Some(result) = result {
					Some(RValue::Atom(
						*ret,
						None,
						Operand::LValueUse(result, BindingProps::value()),
						span,
					))
				} else {
					Some(Self::get_void_rvalue())
				}
			}

			_ => panic!(),
		}
	}

	fn generate_lvalue_expr(&mut self, expr: &Expr) -> Option<LValue> {
		match expr {
			Expr::Atom(Atom::Identifier(id), meta) => {
				if id.absolute {
					let global_access = self.insert_variable(
						None, 
						BindingProps::mut_reference(), 
						expr.get_type().clone()
					);
					
					self.write(CIRStmt::GlobalAccess { 
						local: global_access.local, 
						symbol: id.clone()
					});

					Some(global_access)
				} else {
					let local = self.get_var_index(id.expect_scopeless().unwrap()).unwrap();

					let mut lval = self.get_local_lvalue(local);
					lval.props.span = meta.span;

					Some(lval)
				}
			}

			Expr::Atom(Atom::Block { items, result, .. }, _) => {
				self.generate_lvalue_block(items, result, true).1
			}

			Expr::Cons([lhs, rhs], op, _) => match op {
				Operator::MemberAccess => {
					let mut lhs_ir = self.generate_lvalue_expr(lhs)?;
					let lhs_ty = lhs.get_type();

					let Type::TypeRef { def, .. } = lhs_ty else { panic!() };

					let def = def.upgrade().unwrap();
					let def = def.read().unwrap();

					let Expr::Atom(Atom::Identifier(id), _) = &**rhs else {
						panic!("invalid lvalue expression:\n{expr}") 
					};

					let idx = def.get_member_index(id.expect_scopeless().unwrap()).unwrap();

					lhs_ir.projection.push(PlaceElem::Field(idx));

					Some(lhs_ir)
				}

				Operator::Subscr => {
					let mut indexed = self.generate_lvalue_expr(lhs)?;
					let index = self.generate_expr(rhs, BindingProps::default())?;
					let index_ty = rhs.get_type();

					indexed.projection.push(PlaceElem::Index {
						index_ty: index_ty.clone(),
						index: self.get_as_operand(index_ty, index, rhs.get_span()),
						op: op.clone(),
					});

					Some(indexed)
				}

				// Not a valid lvalue without an outer deref, handled by case below
				Operator::Add | Operator::Sub => panic!(),

				_ => panic!(),
			},

			Expr::Unary(val, Operator::Deref, _) => match &**val {
				// Special case for *(ptr + n)
				Expr::Cons([lhs, rhs], op @ (Operator::Add | Operator::Sub), _) => {
					let mut indexed = self.generate_lvalue_expr(lhs)?;
					let index = self.generate_expr(rhs, BindingProps::default())?;
					let index_ty = rhs.get_type();

					indexed.projection.push(PlaceElem::Index {
						index_ty: index_ty.clone(),
						index: self.get_as_operand(index_ty, index, rhs.get_span()),
						op: op.clone(),
					});

					Some(indexed)
				}

				_ => {
					let mut derefee = self.generate_lvalue_expr(val)?;
					derefee.projection.push(PlaceElem::Deref);
					Some(derefee)
				}
			},

			Expr::Atom(
				Atom::FnCall {
					args,
					generic_args,
					resolved,
					..
				},
				meta,
			) => {
				let result = self.generate_fn_call(args, generic_args, resolved, meta.span)?;

				let RValue::Atom(_, None, Operand::LValueUse(lval, _), _) = result else {
					panic!("function result is not an lvalue!")
				};

				Some(lval)
			}

			expr => {
				let rval = self.generate_expr(expr, BindingProps::value())?;
				Some(self.insert_temporary(expr.get_type(), rval, SrcSpan::new()))
			}
		}
	}

	fn is_trivially_matchable(branches: &Vec<(Pattern, Expr)>, scrutinee_ty: &Type) -> bool {
		for (branch, _) in branches {
			match branch {
				Pattern::Binding(Binding { ty, .. }) => {
					if scrutinee_ty.get_variant_index(ty).is_none() {
						return false;
					}
				}

				_ => return false,
			}
		}

		true
	}

	fn get_trivial_match_value(branch: &Pattern, scrutinee_ty: &Type) -> usize {
		match branch {
			Pattern::Binding(Binding { ty, .. }) => scrutinee_ty.get_variant_index(ty).unwrap(),

			_ => panic!(),
		}
	}

	fn generate_match_expr(
		&mut self,
		pattern: &Pattern,
		value: &LValue,
		value_ty: &Type,
	) -> RValue {
		match pattern {
			Pattern::Binding(Binding { ty: pattern_ty, .. }) => {
				if pattern_ty == value_ty {
					RValue::const_bool(true)
				} else if let Some(discriminant) = value_ty.get_variant_index(pattern_ty) {
					// TODO: Actually figure out proper discriminant type
					let disc_type = Type::i32_type(true);

					RValue::Cons(
						Type::Basic(Basic::Bool),
						[
							(
								disc_type.clone(),
								Operand::LValueUse(
									LValue {
										local: value.local,
										projection: vec![PlaceElem::SumDisc],
										props: value.props,
									},
									BindingProps::value(),
								),
							),
							(
								disc_type,
								Operand::IntegerLit(discriminant as i128, SrcSpan::new()),
							),
						],
						Operator::Eq,
						SrcSpan::new(),
					)
				} else {
					todo!()
				}
			}

			Pattern::Destructure { patterns, .. } => {
				let mut result = None;

				for (i, pattern) in patterns.iter().enumerate() {
					let lval = value.clone().projected(vec![PlaceElem::Field(i)]);				
					let member = self.generate_match_expr(&pattern.1, &lval, pattern.1.get_type());
					
					if let Some(prev_result) = result {
						let op = self.get_as_operand(pattern.1.get_type(), member, SrcSpan::new());
						let prev = self.get_as_operand(&Type::bool_type(), prev_result, SrcSpan::new());
						
						result = Some(RValue::Cons(
							Type::bool_type(), 
							[
								(Type::bool_type(), prev),
								(Type::bool_type(), op)
							],
							Operator::LogicAnd, 
							SrcSpan::new()
						));
					} else {
						result = Some(member);
					}
				}
				
				if let Some(result) = result {
					result
				} else {
					RValue::const_bool(true)
				}
			},

			Pattern::Or(_, _) => todo!(),
		}
	}

	fn generate_branch(&mut self, cond: Operand, a: BlockIndex, b: BlockIndex) {
		self.write(CIRStmt::Switch(
			cond,
			vec![(
				Type::Basic(Basic::Bool),
				Operand::BoolLit(true, SrcSpan::new()),
				a,
			)],
			b,
		));
	}

	fn get_var_index(&self, name: &Name) -> Option<VarIndex> {
		for stack_frame in self.scope_stack.iter().rev() {
			if let Some((_, idx)) = stack_frame
				.variables
				.iter()
				.rev()
				.find(|(n, _)| n.as_ref() == Some(name))
			{
				return Some(*idx);
			}
		}
		None
	}

	fn get_local_lvalue(&self, local: VarIndex) -> LValue {
		LValue {
			local,
			projection: vec![],
			props: self.get_fn().variables[local].1,
		}
	}

	fn insert_variable(&mut self, name: Option<Name>, props: BindingProps, ty: Type) -> LValue {
		assert!(!ty.is_void_or_never());

		let idx = self.get_fn().variables.len();

		self.scope_stack
			.last_mut()
			.unwrap()
			.variables
			.push((name.clone(), idx));

		self.get_fn_mut().variables.push((ty, props, name));

		LValue {
			local: idx,
			projection: vec![],
			props,
		}
	}

	fn get_as_operand(&mut self, ty: &Type, rval: RValue, span: SrcSpan) -> Operand {
		if let RValue::Atom(_, None, operand, _) = rval {
			operand
		} else {
			Operand::LValueUse(
				self.insert_temporary(ty, rval, span),
				BindingProps::value(),
			)
		}
	}

	fn insert_temporary(&mut self, ty: &Type, rval: RValue, span: SrcSpan) -> LValue {
		assert!(!ty.is_void_or_never());

		let local = self.get_fn().variables.len();
		let props = BindingProps {
			is_mut: true,
			is_ref: false,
			is_new: false,
			span,
		};
		
		self.get_fn_mut().variables.push((ty.clone(), props, None));
		self.scope_stack
			.last_mut()
			.unwrap()
			.variables
			.push((None, local));

		let lval = LValue {
			local,
			projection: vec![],
			props,
		};

		self.generate_raw_assign(ty, lval.clone(), rval);

		lval
	}

	fn get_void_rvalue() -> RValue {
		RValue::Atom(
			Type::Basic(Basic::Void),
			None,
			Operand::Undef,
			SrcSpan::new(),
		)
	}
}
