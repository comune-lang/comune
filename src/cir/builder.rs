use std::{borrow::BorrowMut, collections::HashMap};

use crate::{
	ast::{
		controlflow::ControlFlow,
		expression::{Atom, Expr, FnRef, OnceAtom, Operator},
		module::{
			ItemRef, ModuleASTElem, ModuleImpl, ModuleInterface,
			ModuleItemInterface, Name,
		},
		pattern::{Binding, Pattern},
		statement::Stmt,
		types::{
			Basic, BindingProps, FnPrototype, TupleKind, Type, GenericParamList, TypeRef, TypeDefKind,
		},
	},
	constexpr::{ConstExpr, ConstValue},
	lexer::SrcSpan,
	parser::Parser,
};

use super::{
	BlockIndex, CIRBlock, CIRFnPrototype, CIRFunction, CIRModule, CIRStmt, CIRType, CIRTypeDef,
	CIRTypeParamList, LValue, Operand, PlaceElem, RValue, TypeName, VarIndex, CIRFnCall,
};

pub struct CIRModuleBuilder {
	pub module: CIRModule,

	type_map: HashMap<TypeRef, TypeName>,
	type_param_counter: usize, // Used to assign unique names to type parameters

	current_fn: Option<CIRFunction>,
	name_map_stack: Vec<HashMap<Name, VarIndex>>,
	current_block: BlockIndex,
	loop_stack: Vec<(BlockIndex, BlockIndex)>, // start and end
}

impl CIRModuleBuilder {
	pub fn from_ast(ast: &Parser) -> Self {
		let mut result = CIRModuleBuilder {
			module: CIRModule {
				types: HashMap::new(),
				globals: HashMap::new(),
				functions: HashMap::new(),
			},

			current_fn: None,
			type_map: HashMap::new(),
			type_param_counter: 0,
			name_map_stack: vec![HashMap::new()],
			current_block: 0,
			loop_stack: vec![],
		};

		result.register_module(&ast.interface);
		result.generate_namespace(&ast.module_impl);

		result
	}

	fn register_module(&mut self, module: &ModuleInterface) {
		for (_, im) in &module.trait_solver.local_impls {
			let im = &*im.read().unwrap();

			for (_, fns) in &im.functions {
				for func in fns {
					let (proto, cir_fn) = self.generate_prototype(&*func.read().unwrap());

					self.module.functions.insert(proto, cir_fn);
				}
			}
		}

		for import in module.imported.values() {
			self.register_module(import);
		}

		for (_, elem) in &module.children {
			if let ModuleItemInterface::Functions(fns) = elem {
				for func in fns {
					let (proto, cir_fn) = self.generate_prototype(&*func.read().unwrap());

					self.module.functions.insert(proto, cir_fn);
				}
			}
		}
	}

	fn generate_namespace(&mut self, module_impl: &ModuleImpl) {
		for (func, ast) in module_impl.fn_impls.iter() {
			let ModuleASTElem::Parsed(ast) = ast else { panic!() };

			let proto = self.get_prototype(&*func.read().unwrap());

			self.generate_function(proto, ast);
		}
	}

	fn convert_type(&mut self, ty: &Type) -> CIRType {
		match ty {
			Type::Basic(basic) => CIRType::Basic(*basic),

			Type::TypeRef(ItemRef::Resolved(ty)) => {
				let idx = self.convert_type_def(ty);
				let args_cir = ty.args.iter().map(|ty| self.convert_type(ty)).collect();

				CIRType::TypeRef(idx, args_cir)
			}

			Type::TypeRef(_) => panic!("unresolved TypeRef in cIR!"),

			Type::TypeParam(idx) => CIRType::TypeParam(*idx),

			Type::Pointer { pointee, mutable } => CIRType::Pointer { pointee: Box::new(self.convert_type(pointee)), mutable: *mutable },

			Type::Array(arr_ty, size) => {
				let arr_ty_cir = Box::new(self.convert_type(arr_ty));
				let mut dimensions = vec![];

				for elem in size.read().unwrap().iter() {
					if let ConstExpr::Result(ConstValue::Integral(dim_size, _)) = elem {
						dimensions.push(*dim_size);
					} else {
						panic!("Unresolved ConstExpr during cIR generation!")
					}
				}

				CIRType::Array(arr_ty_cir, dimensions)
			}

			Type::Tuple(kind, types) => CIRType::Tuple(
				*kind,
				types.iter().map(|ty| self.convert_type(ty)).collect(),
			),

			Type::Never => CIRType::Basic(Basic::Void),

			Type::Function(ret, params) => {
				CIRType::FunctionPtr { 
					ret: Box::new(self.convert_type(ret)), 
					args: params.iter().map(|(props, ty)| (*props, self.convert_type(ty))).collect()
				}
			}
		}
	}

	fn convert_type_param_list(&mut self, list: GenericParamList) -> CIRTypeParamList {
		list.into_iter()
			.map(|(name, traits, concrete)| {
				(
					name,
					traits,
					concrete.as_ref().map(|ty| self.convert_type(ty)),
				)
			})
			.collect()
	}

	fn convert_type_def(&mut self, ty: &TypeRef) -> String {
		let TypeRef { def, .. } = ty;

		if let Some(ty_id) = self.type_map.get(ty) {
			ty_id.clone()
		} else {
			let def = def.upgrade().unwrap();
			let def = def.read().unwrap();

			// Found an unregistered TypeDef, convert it
			let (insert_idx, cir_def) = match &def.def {
				TypeDefKind::Algebraic(alg) => {
					let mut members = vec![];
					let mut members_map = HashMap::new();

					for (name, ty, _) in &alg.members {
						members_map.insert(name.clone(), members.len());
						members.push(self.convert_type(ty));
					}

					// TODO: Variant mapping

					(
						def.name.to_string(),
						CIRTypeDef::Algebraic {
							members,
							variants: vec![],
							layout: alg.layout,
							members_map,
							variants_map: HashMap::new(),
							type_params: self.convert_type_param_list(alg.params.clone()),
						},
					)
				}
				TypeDefKind::Class => todo!(),
			};

			self.module.types.insert(insert_idx.clone(), cir_def);
			self.type_map.insert(ty.clone(), insert_idx.clone());

			insert_idx
		}
	}
}

impl CIRModuleBuilder {
	pub fn get_prototype(&mut self, func: &FnPrototype) -> CIRFnPrototype {
		let ret = self.convert_type(&func.ret);
		let params = func
			.params
			.params
			.iter()
			.map(|(param, _, props)| (*props, self.convert_type(param)))
			.collect();

		CIRFnPrototype {
			name: func.path.clone(),
			ret,
			params,
			type_params: self.convert_type_param_list(func.type_params.clone()),
		}
	}

	pub fn generate_prototype(&mut self, func: &FnPrototype) -> (CIRFnPrototype, CIRFunction) {
		let proto = self.get_prototype(func);

		self.current_fn = Some(CIRFunction {
			variables: func.params.params.iter().map(|(ty, name, props)| (self.convert_type(ty), *props, name.clone())).collect(),
			blocks: vec![],
			ret: proto.ret.clone(),
			arg_count: func.params.params.len(),
			type_params: self.convert_type_param_list(func.type_params.clone()),
			attributes: func.attributes.clone(),
			is_extern: true,
			is_variadic: func.params.variadic,
			mangled_name: None,
		});

		(proto, self.current_fn.take().unwrap())
	}

	pub fn generate_function(&mut self, proto: CIRFnPrototype, fn_block: &Expr) {
		self.current_fn = if let Some(func) = self.module.functions.remove(&proto) {
			Some(func)
		} else {
			panic!(
				"failed to get cIR function {proto} from module! function list:\n\n{:?}\n",
				self.module.functions.keys()
			)
		};
		
		self.name_map_stack.clear();
		self.current_block = 0;
		self.loop_stack.clear();

		let mut params_map = HashMap::new();

		for (i, (.., name)) in self.current_fn.as_ref().unwrap().variables.iter().enumerate() {
			if let Some(name) = name {
				params_map.insert(name.clone(), i);
			}
		}
		
		self.name_map_stack.push(params_map);

		// Generate function body
		self.append_block();

		let _ = self.generate_expr(fn_block);

		let func = self.current_fn.borrow_mut().as_mut().unwrap();

		// Find block preds & succs

		for i in 0..func.blocks.len() {
			let succs = match func.blocks[i].items.last().unwrap() {
				CIRStmt::FnCall {
					next,
					except: Some(except),
					..
				} => vec![*next, *except],

				CIRStmt::FnCall {
					next, except: None, ..
				} => vec![*next],

				CIRStmt::Jump(jmp) => vec![*jmp],

				CIRStmt::Switch(_, branches, else_idx) => {
					let mut result = vec![];
					result.reserve(branches.len() + 1);
					result.extend(branches.iter().map(|(.., idx)| *idx));
					result.push(*else_idx);

					result
				}

				CIRStmt::Return(_) => vec![],

				term => panic!("invalid terminator in cIR: {term:?}"),
			};

			for succ in &succs {
				func.blocks[*succ].preds.push(i);
			}

			func.blocks[i].succs = succs;
		}

		self.current_fn.borrow_mut().as_mut().unwrap().is_extern = false;
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
				self.generate_expr(expr).map(|_| ())
			}

			Stmt::Decl(bindings, expr, tk) => {
				if bindings.len() != 1 {
					todo!()
				}

				// TODO: Handle destructuring assignment
				let (ty, name, props) = &bindings[0];

				let val = if let Some(expr) = expr {
					// Stop building early if the expression never returns
					let result = self.generate_expr(expr)?;

					Some(result)
				} else {
					None
				};

				let cir_ty = self.convert_type(ty);
				let var = self.insert_variable(Some(name.clone()), *props, cir_ty);

				self.write(CIRStmt::StorageLive(var.local));

				if let Some(val) = val {
					self.write(CIRStmt::Assignment((var.clone(), *tk), val));
				}

				self.name_map_stack
					.last_mut()
					.unwrap()
					.insert(name.clone(), var.local);
				
				Some(())
			}
		}
	}

	// For a given pattern match, generate the appropriate bindings
	fn generate_pattern_bindings(&mut self, pattern: Pattern, value: LValue, value_ty: &CIRType) {
		match pattern {
			Pattern::Binding(Binding {
				name: Some(name),
				ty,
				props,
			}) => {
				let cir_ty = self.convert_type(&ty);
				let idx = self.get_fn().variables.len();

				self.get_fn_mut()
					.variables
					.push((cir_ty.clone(), props, Some(name.clone())));

				self.name_map_stack
					.last_mut()
					.unwrap()
					.insert(name.clone(), idx);

				let store_place = LValue {
					local: self.get_fn().variables.len() - 1,
					projection: vec![],
				};

				if &cir_ty != value_ty {
					self.write(CIRStmt::Assignment(
						(store_place, SrcSpan::new()),
						RValue::Cast {
							to: cir_ty,
							from: value_ty.clone(),
							val: Operand::LValue(value, SrcSpan::new()),
							span: SrcSpan::new(),
						},
					));
				} else {
					self.write(CIRStmt::Assignment(
						(store_place, SrcSpan::new()),
						RValue::Atom(
							cir_ty,
							None,
							Operand::LValue(value, SrcSpan::new()),
							SrcSpan::new(),
						),
					));
				}
			}

			Pattern::Binding(Binding { name: None, .. }) => {}

			_ => todo!(),
		}
	}

	fn generate_binding(
		&mut self,
		ty: &Type,
		name: Name,
		props: BindingProps,
		elem: &Option<Box<Expr>>,
	) {
		let cir_ty = self.convert_type(ty);
		let idx = self.get_fn().variables.len();

		self.get_fn_mut()
			.variables
			.push((cir_ty, props, Some(name.clone())));
		self.name_map_stack.last_mut().unwrap().insert(name, idx);

		let lval = LValue {
			local: self.get_fn().variables.len() - 1,
			projection: vec![],
		};

		if let Some(elem) = elem {
			if let Some(rval) = self.generate_expr(elem) {
				self.write(CIRStmt::Assignment((lval, elem.get_node_data().tk), rval));
			}
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

		self.name_map_stack.push(HashMap::new());

		for item in items {
			if self.generate_stmt(item).is_none() {
				return (jump_idx, None)
			}
		}

		// Check if the block has a result statement
		if let Some(result) = result {
			let Some(result_ir) = self.generate_expr(result) else { return (jump_idx, None); };
			let result_type = self.convert_type(result.get_type());
			let result_ir = self.get_as_operand(result_type.clone(), result_ir);
			
			for (_, var) in self.name_map_stack.pop().unwrap() {
				self.write(CIRStmt::StorageDead(var));
			}

			(
				jump_idx,
				Some(RValue::Atom(
					result_type,
					None,
					result_ir,
					result.get_node_data().tk,
				)),
			)
		} else {

			for (_, var) in self.name_map_stack.pop().unwrap() {
				self.write(CIRStmt::StorageDead(var));
			}
			
			(jump_idx, Some(Self::get_void_rvalue()))
		}
	}

	// generate_expr only returns None if `expr` is a "never expression"
	// aka an expression that will never evaluate to a value
	#[must_use]
	fn generate_expr(&mut self, expr: &Expr) -> Option<RValue> {
		let expr_ty = expr.get_type();
		let span = expr.get_node_data().tk;

		match expr {
			Expr::Atom(atom, _) => match atom {
				Atom::IntegerLit(i, b) => Some(if let Some(b) = b {
					RValue::Atom(
						CIRType::Basic(*b),
						None,
						Operand::IntegerLit(*i, span),
						span,
					)
				} else {
					RValue::Atom(
						self.convert_type(expr_ty),
						None,
						Operand::IntegerLit(*i, span),
						span,
					)
				}),

				Atom::FloatLit(f, b) => Some(if let Some(b) = b {
					RValue::Atom(CIRType::Basic(*b), None, Operand::FloatLit(*f, span), span)
				} else {
					RValue::Atom(
						self.convert_type(expr_ty),
						None,
						Operand::FloatLit(*f, span),
						span,
					)
				}),

				Atom::BoolLit(b) => Some(RValue::Atom(
					CIRType::Basic(Basic::Bool),
					None,
					Operand::BoolLit(*b, span),
					span,
				)),

				Atom::StringLit(s) => Some(RValue::Atom(
					CIRType::Basic(Basic::Str),
					None,
					Operand::StringLit(s.clone(), span),
					span,
				)),

				Atom::CStringLit(s) => Some(RValue::Atom(
					CIRType::Pointer { pointee: Box::new(CIRType::Basic(Basic::Integral {
						signed: false,
						size_bytes: 1,
					})), mutable: false },
					None,
					Operand::CStringLit(s.clone(), span),
					span,
				)),

				Atom::ArrayLit(elems) => {
					let cir_ty = self.convert_type(expr_ty);

					let tmp = self.insert_temporary(
						cir_ty.clone(),
						RValue::Atom(cir_ty.clone(), None, Operand::Undef, span),
					);

					for (i, expr) in elems.iter().enumerate() {
						let expr_ir = self.generate_expr(expr)?;

						let mut tmp_idx = tmp.clone();
						tmp_idx.projection.push(PlaceElem::Index(
							CIRType::Basic(Basic::PtrSizeInt { signed: false }),
							Operand::IntegerLit(i as i128, SrcSpan::new()),
						));

						self.write(CIRStmt::Assignment((tmp_idx, SrcSpan::new()), expr_ir))
					}

					Some(RValue::Atom(
						cir_ty,
						None,
						Operand::LValue(tmp, SrcSpan::new()),
						span,
					))
				}

				Atom::AlgebraicLit(ty, elems) => {
					let cir_ty = self.convert_type(ty);

					let ty_idx = if let CIRType::TypeRef(idx, _params) = &cir_ty {
						idx
					} else {
						panic!()
					};

					let mut indices = vec![];

					if let CIRTypeDef::Algebraic { members_map, .. } = &self.module.types[ty_idx] {
						for elem in elems {
							indices.push(members_map[&elem.0]);
						}
					} else {
						panic!()
					}

					let tmp = self.insert_temporary(
						cir_ty.clone(),
						RValue::Atom(cir_ty.clone(), None, Operand::Undef, SrcSpan::new()),
					);

					for i in 0..indices.len() {
						let mem_expr = self.generate_expr(&elems[i].1);
						let mut mem_lval = tmp.clone();

						mem_lval.projection.push(PlaceElem::Field(indices[i]));

						if let Some(mem_expr) = mem_expr {
							self.write(CIRStmt::Assignment(
								(mem_lval, elems[i].1.get_node_data().tk),
								mem_expr,
							))
						}
					}

					Some(RValue::Atom(cir_ty, None, Operand::LValue(tmp, span), span))
				}

				Atom::Identifier(id) => {
					let idx = self
						.get_var_index(id.expect_scopeless().unwrap())
						.unwrap_or_else(|| {
							panic!(
								"cIR error: failed to fetch variable {}",
								id.expect_scopeless().unwrap()
							)
						});

					let lval_ty = &self.get_fn().variables[idx].0;

					Some(RValue::Atom(
						lval_ty.clone(),
						None,
						Operand::LValue(
							LValue {
								local: idx,
								projection: vec![],
							},
							span,
						),
						span,
					))
				}

				Atom::Cast(expr, to) => {
					let from = self.convert_type(expr.get_type());
					let to = self.convert_type(to);

					self.generate_expr(expr).map(|castee| RValue::Cast {
						val: self.get_as_operand(from.clone(), castee),
						from,
						to,
						span,
					})
				}

				call @ Atom::FnCall { .. } => self.generate_fn_call(call, span),

				Atom::Block { items, result } => self.generate_block(items, result, true).1,

				Atom::CtrlFlow(ctrl) => match &**ctrl {
					ControlFlow::Return { expr } => {
						if let Some(expr) = expr {
							let expr_ir = self.generate_expr(expr)?;
							let ty = self.convert_type(expr.get_type());
							let operand = self.get_as_operand(ty, expr_ir);

							self.write(CIRStmt::Return(Some(operand)));
						} else {
							self.write(CIRStmt::Return(None));
						}

						None
					}

					ControlFlow::If {
						cond,
						body: Expr::Atom(Atom::Block { items, result }, body_meta),
						else_body,
					} => {
						let cir_ty = self.convert_type(expr_ty);

						let result_loc = if cir_ty != CIRType::Basic(Basic::Void) {
							Some(self.insert_temporary(
								cir_ty.clone(),
								RValue::Atom(cir_ty.clone(), None, Operand::Undef, SrcSpan::new()),
							))
						} else {
							None
						};

						// Generate condition directly in current block, since we don't need to jump back to it
						let cond_ir = self.generate_expr(cond)?;
						let cond_ty = self.convert_type(cond.get_type());
						let cond_op = self.get_as_operand(cond_ty, cond_ir);

						let start_block = self.current_block;

						let mut cont_block = None;

						let (if_idx, block_ir) = self.generate_block(items, result, false);

						if let Some(if_val) = block_ir {
							if let Some(result) = &result_loc {
								self.write(CIRStmt::Assignment(
									(result.clone(), body_meta.tk),
									if_val,
								));
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
							},
							else_meta,
						)) = else_body
						{
							let (else_idx, else_ir) =
								self.generate_block(else_items, else_result, false);

							if let Some(else_val) = else_ir {
								if let Some(result) = &result_loc {
									self.write(CIRStmt::Assignment(
										(result.clone(), else_meta.tk),
										else_val,
									));
								}

								if cont_block.is_none() {
									let current = self.current_block;
									cont_block = Some(self.append_block());
									self.current_block = current;
								}
								
								self.write(CIRStmt::Jump(cont_block.unwrap()));
							}
							
							if let Some(cont_block) = cont_block {
								self.current_block = start_block;
								self.generate_branch(cond_op, if_idx, else_idx);
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
									cir_ty,
									None,
									Operand::LValue(result, span),
									span,
								))
							} else {
								Some(RValue::Atom(cir_ty, None, Operand::Undef, span))
							}
						} else {
							None
						}
					}

					ControlFlow::While {
						cond,
						body: Expr::Atom(Atom::Block { items, result }, _),
					} => {
						let start_block = self.current_block;
						let cond_block = self.append_block();

						let cond_ir = self.generate_expr(cond)?;
						let cond_ty = self.convert_type(cond.get_type());
						let cond_op = self.get_as_operand(cond_ty, cond_ir);

						let cond_write_block = self.current_block;

						let next_block = self.append_block();

						// Write jump-to-cond statement to start block
						self.current_block = start_block;
						self.write(CIRStmt::Jump(cond_block));

						self.loop_stack.push((start_block, next_block));

						// Generate body
						let (body_idx, result) = self.generate_block(items, result, false);

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
						self.generate_expr(body)?;

						// Add iter statement to body
						if let Some(iter) = iter {
							self.generate_expr(iter)?;
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
							if let Some(cond_ir) = self.generate_expr(cond) {
								let cond_ty = self.convert_type(cond.get_type());
								let cond_op = self.get_as_operand(cond_ty, cond_ir);

								self.generate_branch(cond_op, body_block, next_block);
							}
						} else {
							self.write(CIRStmt::Jump(body_block));
						}

						self.current_block = next_block;

						Some(Self::get_void_rvalue())
					}

					ControlFlow::Break => {
						let end_block = self.loop_stack.last().unwrap().1;
						self.write(CIRStmt::Jump(end_block));
						
						None
					}

					ControlFlow::Continue => {
						let start_block = self.loop_stack.last().unwrap().0;
						self.write(CIRStmt::Jump(start_block));
						
						None
					}

					ControlFlow::Match {
						scrutinee,
						branches,
					} => {
						// Generate switch discriminant calculation
						let scrutinee_ir = self.generate_expr(scrutinee)?;
						let scrutinee_ty = self.convert_type(scrutinee.get_type());
						let scrutinee_lval =
							self.insert_temporary(scrutinee_ty.clone(), scrutinee_ir);
						let cir_ty = self.convert_type(expr_ty);

						let disc_ty = CIRType::Basic(scrutinee_ty.get_discriminant_type().unwrap());
						let disc_lval = self.insert_temporary(
							disc_ty.clone(),
							RValue::Atom(
								disc_ty.clone(),
								None,
								Operand::IntegerLit(0, SrcSpan::new()),
								SrcSpan::new(),
							),
						);

						let mut branches_ir = vec![];
						let mut has_result = false;

						let result_loc = if cir_ty != CIRType::Basic(Basic::Void) {
							Some(self.insert_temporary(
								cir_ty.clone(),
								RValue::Atom(cir_ty.clone(), None, Operand::Undef, SrcSpan::new()),
							))
						} else {
							None
						};

						let start_block = self.current_block;

						for (i, (pattern, _)) in branches.iter().enumerate() {
							// TODO: There is no usefulness checking here - if a value
							// matches multiple branches, this will probably break
							let match_expr =
								self.generate_match_expr(pattern, &scrutinee_lval, &scrutinee_ty);
							let match_operand =
								self.get_as_operand(CIRType::Basic(Basic::Bool), match_expr);

							let cast_ir = self.get_as_operand(
								disc_ty.clone(),
								RValue::Cast {
									from: CIRType::Basic(Basic::Bool),
									to: disc_ty.clone(),
									val: match_operand,
									span: SrcSpan::new(),
								},
							);

							let mult_ir = self.get_as_operand(
								disc_ty.clone(),
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
							);

							let add_ir = CIRStmt::Assignment(
								(disc_lval.clone(), SrcSpan::new()),
								RValue::Cons(
									disc_ty.clone(),
									[
										(
											disc_ty.clone(),
											Operand::LValue(disc_lval.clone(), SrcSpan::new()),
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

						let cont_block = self.append_block();

						// Generate branches

						for (i, (pattern, branch)) in branches.iter().enumerate() {
							let Expr::Atom(Atom::Block { items, result }, branch_meta) = branch else { panic!() };

							self.name_map_stack.push(HashMap::new());

							let binding_idx = self.append_block();
							self.generate_pattern_bindings(
								pattern.clone(),
								scrutinee_lval.clone(),
								&scrutinee_ty,
							);

							let (_, match_result) = self.generate_block(items, result, true);

							if let Some(match_result) = match_result {
								if let Some(result_loc) = &result_loc {
									self.write(CIRStmt::Assignment(
										(result_loc.clone(), branch_meta.tk),
										match_result,
									));
								}

								self.write(CIRStmt::Jump(cont_block));
								has_result = true;
							}

							self.name_map_stack.pop();
							self.current_block = cont_block;

							branches_ir[i].2 = binding_idx;
						}

						self.current_block = start_block;
						self.write(CIRStmt::Switch(
							Operand::LValue(disc_lval, SrcSpan::new()),
							branches_ir,
							cont_block,
						));
						self.current_block = cont_block;

						if has_result {
							if let Some(result_loc) = result_loc {
								Some(RValue::Atom(
									cir_ty,
									None,
									Operand::LValue(result_loc, span),
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

				Atom::Once(once) => {
					let cir_ty = self.convert_type(expr_ty);

					if let OnceAtom::Eval(local) = *once.read().unwrap() {
						return Some(RValue::Atom(
							cir_ty,
							None,
							Operand::LValue(
								LValue {
									local,
									projection: vec![],
								},
								SrcSpan::new(),
							),
							SrcSpan::new(),
						));
					}

					let once_uneval = &mut *once.write().unwrap();
					let OnceAtom::Uneval(expr) = once_uneval else { panic!() };

					let span = expr.get_node_data().tk;

					let expr_ir = self.generate_expr(expr)?;
					let local = self.insert_temporary(cir_ty.clone(), expr_ir);

					*once_uneval = OnceAtom::Eval(local.local);

					Some(RValue::Atom(
						cir_ty,
						None,
						Operand::LValue(local, span),
						span,
					))
				}
			},

			Expr::Cons([lhs, rhs], op, _) => {
				if op.is_compound_assignment() {
					let op = op.get_compound_operator();
					let (lval_ir, lval_span) = self.generate_lvalue_expr(lhs)?;
					let rval_ir = self.generate_expr(rhs)?;

					let l_ty = self.convert_type(lhs.get_type());
					let r_ty = self.convert_type(rhs.get_type());

					let r_tmp = self.get_as_operand(r_ty.clone(), rval_ir);

					let expr_ir = RValue::Cons(
						self.convert_type(expr_ty),
						[
							(l_ty.clone(), Operand::LValue(lval_ir.clone(), lval_span)),
							(r_ty.clone(), r_tmp),
						],
						op,
						expr.get_node_data().tk,
					);

					let expr_tmp = self.get_as_operand(l_ty.clone(), expr_ir);

					self.write(CIRStmt::Assignment(
						(lval_ir.clone(), lval_span),
						RValue::Atom(r_ty, None, expr_tmp, rhs.get_node_data().tk),
					));

					Some(RValue::Atom(
						l_ty,
						None,
						Operand::LValue(lval_ir, lval_span),
						span,
					))
				} else {
					match op {
						Operator::MemberAccess => match &**rhs {
							Expr::Atom(call @ Atom::FnCall { .. }, _) => {
								self.generate_fn_call(call, rhs.get_node_data().tk)
							}

							Expr::Atom(Atom::Identifier(_), _) => {
								let (lval, lval_span) = self.generate_lvalue_expr(expr)?;
								let cir_ty = self.convert_type(rhs.get_type());
								Some(RValue::Atom(
									cir_ty,
									None,
									Operand::LValue(lval, lval_span),
									span,
								))
							}

							_ => panic!(),
						},

						Operator::Subscr => {
							let (lval, lval_span) = self.generate_lvalue_expr(expr)?;
							let cir_ty = self.convert_type(expr_ty);
							Some(RValue::Atom(
								cir_ty,
								None,
								Operand::LValue(lval, lval_span),
								span,
							))
						}

						Operator::Assign => {
							let (lval_ir, lval_span) = self.generate_lvalue_expr(lhs)?;
							let rval_ir = self.generate_expr(rhs)?;
							let l_ty = self.convert_type(lhs.get_type());
							let r_ty = self.convert_type(rhs.get_type());

							let r_tmp = self.get_as_operand(r_ty.clone(), rval_ir);

							self.write(CIRStmt::Assignment(
								(lval_ir.clone(), lval_span),
								RValue::Atom(r_ty, None, r_tmp, rhs.get_node_data().tk),
							));

							Some(RValue::Atom(
								l_ty,
								None,
								Operand::LValue(lval_ir, lval_span),
								span,
							))
						}

						_ => {
							let lhs_ir = self.generate_expr(lhs)?;
							let rhs_ir = self.generate_expr(rhs)?;
							let lhs_ty = self.convert_type(lhs.get_type());
							let rhs_ty = self.convert_type(rhs.get_type());
							let lhs_tmp = self.get_as_operand(lhs_ty.clone(), lhs_ir);
							let rhs_tmp = self.get_as_operand(rhs_ty.clone(), rhs_ir);
							Some(RValue::Cons(
								self.convert_type(expr_ty),
								[(lhs_ty, lhs_tmp), (rhs_ty, rhs_tmp)],
								op.clone(),
								expr.get_node_data().tk,
							))
						}
					}
				}
			}

			Expr::Unary(sub, op, _) => {
				let sub_expr = self.generate_expr(sub)?;
				let cir_ty = self.convert_type(sub.get_type());
				let temp = self.get_as_operand(cir_ty.clone(), sub_expr);

				Some(RValue::Atom(
					cir_ty,
					Some(op.clone()),
					temp,
					expr.get_node_data().tk,
				))
			}
		}
	}

	fn generate_fn_call(&mut self, call: &Atom, span: SrcSpan) -> Option<RValue> {
		let Atom::FnCall {
			name: _,
			args,
			type_args,
			resolved,
		} = call else { panic!() };

		let cir_args: Vec<_> = args
			.iter()
			.map_while(|arg| {
				let cir_ty = self.convert_type(arg.get_type());
				let cir_expr = self.generate_expr(arg)?;

				if let RValue::Atom(_, None, Operand::LValue(lval, _), _) = cir_expr {
					Some((lval, arg.get_node_data().tk))
				} else {
					Some((self.insert_temporary(cir_ty, cir_expr), arg.get_node_data().tk))
				}
			})
			.collect();

		// One of the expressions does not return, so stop building the call here
		if cir_args.len() < args.len() {
			return None;
		}

		let cir_type_args = type_args.iter().map(|arg| self.convert_type(arg)).collect();

		match resolved {
			FnRef::Direct(resolved) => {
				let ret = &resolved.read().unwrap().ret;

				let current_block = self.current_block;
				let next = self.append_block();
				self.current_block = current_block;
		
				let result = if ret == &Type::Basic(Basic::Void) {
					None
				} else {
					// TODO: BindingProps for return type
					let cir_ret = self.convert_type(ret);
					Some(self.insert_variable(None, BindingProps::default(), cir_ret))
				};
		
				let id = self.get_prototype(&*resolved.read().unwrap());
		
				self.write(CIRStmt::FnCall {
					id: CIRFnCall::Direct(id, SrcSpan::new()),
					args: cir_args,
					type_args: cir_type_args,
					result: result.clone(),
					next,
					except: None,
				});
		
				self.current_block = next;
		
				if let Some(result) = result {
					Some(RValue::Atom(
						self.convert_type(&ret),
						None,
						Operand::LValue(result, span),
						span,
					))
				} else {
					Some(Self::get_void_rvalue())
				}
			}

			FnRef::Indirect(expr) => {
				let fn_val_ir = self.generate_expr(expr)?;
				let fn_val_ty = fn_val_ir.get_type().clone();

				let local = if let RValue::Atom(_, None, Operand::LValue(lval, _), _) = fn_val_ir {
					lval
				} else {
					self.insert_temporary(fn_val_ir.get_type().clone(), fn_val_ir.clone())
				};

				let CIRType::FunctionPtr { ret, args } = fn_val_ty else { 
					panic!()
				};
				
				let result = if &*ret == &CIRType::Basic(Basic::Void) {
					None
				} else {
					// TODO: BindingProps for return type
					Some(self.insert_variable(None, BindingProps::default(), *ret.clone()))
				};

				let current_block = self.current_block;
				let next = self.append_block();
				self.current_block = current_block;

				self.write(CIRStmt::FnCall { 
					id: CIRFnCall::Indirect { 
						local, 
						ret: *ret.clone(),
						args,
						span: expr.get_node_data().tk
					}, 
					args: cir_args,
					type_args: vec![], 
					result: result.clone(),
					next,
					except: None 
				});

				self.current_block = next;

				if let Some(result) = result {
					Some(RValue::Atom(
						*ret,
						None,
						Operand::LValue(result, span),
						span,
					))
				} else {
					Some(Self::get_void_rvalue())
				}
			}

			_ => panic!()
		}
	}

	fn generate_lvalue_expr(&mut self, expr: &Expr) -> Option<(LValue, SrcSpan)> {
		match expr {
			Expr::Atom(atom, meta) => match atom {
				Atom::Identifier(id) => Some((
					LValue {
						local: self.get_var_index(id.expect_scopeless().unwrap()).unwrap(),
						projection: vec![],
					},
					meta.tk,
				)),

				Atom::Once(_) => {
					let RValue::Atom(_, None, Operand::LValue(lvalue, _), span) = self.generate_expr(expr)? else { panic!() };
					Some((lvalue, span))
				}

				_ => panic!(),
			},

			Expr::Cons([lhs, rhs], op, _) => match op {
				Operator::MemberAccess => {
					let (mut lhs_ir, meta) = self.generate_lvalue_expr(lhs)?;
					let lhs_ty = self.convert_type(lhs.get_type());

					let CIRType::TypeRef(id, _params) = lhs_ty else { panic!() };
					let CIRTypeDef::Algebraic { members_map, .. } = &self.module.types[&id] else { panic!() };

					let Expr::Atom(Atom::Identifier(id), _) = &**rhs else { panic!() };

					let idx = members_map[id.expect_scopeless().unwrap()];

					lhs_ir.projection.push(PlaceElem::Field(idx));

					Some((lhs_ir, meta))
				}

				Operator::Subscr => {
					let (mut indexed, meta) = self.generate_lvalue_expr(lhs)?;
					let index = self.generate_expr(rhs)?;
					let index_ty = self.convert_type(rhs.get_type());
					indexed.projection.push(PlaceElem::Index(
						index_ty.clone(),
						self.get_as_operand(index_ty, index),
					));
					Some((indexed, meta))
				}

				_ => panic!(),
			},

			Expr::Unary(val, op, _) => match op {
				Operator::Deref => {
					let (mut derefee, meta) = self.generate_lvalue_expr(val)?;
					derefee.projection.push(PlaceElem::Deref);
					Some((derefee, meta))
				}

				_ => panic!(),
			},
		}
	}

	fn generate_match_expr(
		&mut self,
		pattern: &Pattern,
		value: &LValue,
		value_ty: &CIRType,
	) -> RValue {
		match pattern {
			Pattern::Binding(Binding { ty: pattern_ty, .. }) => {
				let pattern_ty = self.convert_type(pattern_ty);

				if &pattern_ty == value_ty {
					RValue::const_bool(true)
				} else if let CIRType::Tuple(TupleKind::Sum, types) = value_ty {
					let Some(discriminant) = types.iter().position(|item| item == &pattern_ty) else {
						panic!("invalid match variant type!"); // TODO: Figure this out
					};

					// TODO: Actually figure out proper discriminant type
					let disc_type = CIRType::Basic(Basic::Integral {
						signed: false,
						size_bytes: 4,
					});

					RValue::Cons(
						CIRType::Basic(Basic::Bool),
						[
							(
								disc_type.clone(),
								Operand::LValue(
									LValue {
										local: value.local,
										projection: vec![PlaceElem::Field(0)],
									},
									SrcSpan::new(),
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
			Pattern::Destructure(_, _) => todo!(),
			Pattern::Or(_, _) => todo!(),
		}
	}

	fn generate_branch(&mut self, cond: Operand, a: BlockIndex, b: BlockIndex) {
		self.write(CIRStmt::Switch(
			cond,
			vec![(
				CIRType::Basic(Basic::Bool),
				Operand::BoolLit(true, SrcSpan::new()),
				a,
			)],
			b,
		));
	}

	fn get_var_index(&self, name: &Name) -> Option<VarIndex> {
		for stack_frame in self.name_map_stack.iter().rev() {
			if let Some(idx) = stack_frame.get(name) {
				return Some(*idx);
			}
		}
		None
	}

	fn insert_variable(&mut self, name: Option<Name>, props: BindingProps, ty: CIRType) -> LValue {
		let idx = self.get_fn().variables.len();

		if let Some(name) = &name {
			self.name_map_stack
				.last_mut()
				.unwrap()
				.insert(name.clone(), idx);
		}

		self.get_fn_mut().variables.push((ty, props, name));

		LValue {
			local: idx,
			projection: vec![],
		}
	}

	fn get_as_operand(&mut self, ty: CIRType, rval: RValue) -> Operand {
		if let RValue::Atom(_, None, operand, _) = rval {
			operand
		} else {
			Operand::LValue(self.insert_temporary(ty, rval), SrcSpan::new())
		}
	}

	fn insert_temporary(&mut self, ty: CIRType, rval: RValue) -> LValue {
		self.get_fn_mut().variables.push((
			ty,
			BindingProps {
				is_mut: true,
				is_ref: false,
				is_unsafe: false,
			},
			None,
		));

		let lval = LValue {
			local: self.get_fn().variables.len() - 1,
			projection: vec![],
		};

		self.write(CIRStmt::Assignment((lval.clone(), SrcSpan::new()), rval));

		lval
	}

	fn get_void_rvalue() -> RValue {
		RValue::Atom(
			CIRType::Basic(Basic::Void),
			None,
			Operand::Undef,
			SrcSpan::new(),
		)
	}
}
