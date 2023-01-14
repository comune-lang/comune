use std::{borrow::BorrowMut, collections::HashMap};

use crate::{
	ast::{
		controlflow::ControlFlow,
		expression::{Atom, Expr, Operator, OnceAtom},
		namespace::{Identifier, ItemRef, Name, Namespace, NamespaceASTElem, NamespaceItem},
		pattern::{Pattern, Binding},
		statement::Stmt,
		types::{Basic, FnDef, TupleKind, Type, TypeDef, TypeRef},
		Attribute,
	},
	constexpr::{ConstExpr, ConstValue},
	driver::ModuleState,
};

use super::{
	BlockIndex, CIRFunction, CIRModule, CIRStmt, CIRType, CIRTypeDef, LValue, Operand, PlaceElem,
	RValue, TypeName, VarIndex, CIRFnPrototype,
};

pub struct CIRModuleBuilder {
	pub module: CIRModule,

	type_map: HashMap<TypeRef, TypeName>,
	type_param_counter: usize, // Used to assign unique names to type parameters

	current_fn: Option<CIRFunction>,
	name_map_stack: Vec<HashMap<Name, VarIndex>>,
	current_block: BlockIndex,
}

impl CIRModuleBuilder {
	pub fn from_ast(ast: &ModuleState) -> Self {
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
		};

		result.register_namespace(&ast.parser.namespace);
		result.generate_namespace(&ast.parser.namespace);

		result
	}

	fn register_namespace(&mut self, namespace: &Namespace) {
		for (im_ty, im) in namespace.trait_solver.get_local_impls() {
			let im = im.read().unwrap();

			for (name, fns) in &im.items {
				for (func, _) in fns {
					let (proto, cir_fn) = self.generate_prototype(Identifier::from_parent(&im.scope, name.clone()), &func.read().unwrap(), vec![]);

					self.module.functions.insert(proto, cir_fn);
				}
			}
		}

		for import in &namespace.imported {
			self.register_namespace(import.1);
		}

		for (name, (elem, attribs, _)) in &namespace.children {
			if let NamespaceItem::Functions(fns) = elem {
				for (func, _) in fns {
					let (proto, cir_fn) = self.generate_prototype(name.clone(), &func.read().unwrap(), attribs.clone());

					self.module.functions.insert(proto, cir_fn);
				}
			}
		}
	}

	fn generate_namespace(&mut self, namespace: &Namespace) {
		for (im_ty, im) in namespace.trait_solver.get_local_impls() {
			let im = im.read().unwrap();
			
			for (name, fns) in &im.items {
				for (func, ast) in fns {
					if let NamespaceASTElem::Parsed(ast) = &*ast.borrow() {
						let proto = self.get_prototype(Identifier::from_parent(&im.scope, name.clone()), &func.read().unwrap());
						self.generate_function(proto, ast);
					}
				}
			}
		}

		for (name, (item, ..)) in &namespace.children {
			if let NamespaceItem::Functions(fns) = item {
				for (func, ast) in fns {
					let proto = self.get_prototype(name.clone(), &func.read().unwrap());

					if let NamespaceASTElem::Parsed(ast) = &*ast.borrow() {
						self.generate_function(proto, ast);
					}
				}
			}
		}
	}

	fn convert_type(&mut self, ty: &Type) -> CIRType {
		match ty {
			Type::Basic(basic) => CIRType::Basic(*basic),

			Type::TypeRef(ItemRef::Resolved(ty)) => {
				let idx = self.convert_type_def(ty);
				let args_cir = ty
					.args
					.iter()
					.map(|(_, ty)| self.convert_type(ty))
					.collect();

				CIRType::TypeRef(idx, args_cir)
			}

			Type::TypeParam(idx) => CIRType::TypeParam(*idx),

			Type::Pointer(pointee) => CIRType::Pointer(Box::new(self.convert_type(pointee))),

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

			_ => todo!(),
		}
	}

	fn convert_type_def(&mut self, ty: &TypeRef) -> String {
		let TypeRef { def, name, .. } = ty;

		if let Some(ty_id) = self.type_map.get(ty) {
			ty_id.clone()
		} else {
			// Found an unregistered TypeDef, convert it
			let (insert_idx, cir_def) = match &*def.upgrade().unwrap().read().unwrap() {
				TypeDef::Algebraic(alg) => {
					let mut members = vec![];
					let mut members_map = HashMap::new();

					for (name, ty, _) in &alg.members {
						members_map.insert(name.clone(), members.len());
						members.push(self.convert_type(ty));
					}

					// TODO: Variant mapping

					(
						name.to_string(),
						CIRTypeDef::Algebraic {
							members,
							variants: vec![],
							layout: alg.layout,
							members_map,
							variants_map: HashMap::new(),
							type_params: alg.params.clone(),
						},
					)
				}
				TypeDef::Class => todo!(),
			};

			self.module.types.insert(insert_idx.clone(), cir_def);
			self.type_map.insert(ty.clone(), insert_idx.clone());

			insert_idx
		}
	}
}

impl CIRModuleBuilder {
	pub fn get_prototype(&mut self, name: Identifier, func: &FnDef) -> CIRFnPrototype {
		let ret = self.convert_type(&func.ret);
		let params = func.params.params.iter().map(|(param, _)| self.convert_type(param)).collect();

		CIRFnPrototype {
			name,
			ret,
			params,
			type_params: func.type_params.clone(),
		}
	}

	pub fn generate_prototype(&mut self, name: Identifier, func: &FnDef, attributes: Vec<Attribute>) -> (CIRFnPrototype, CIRFunction) {
		let proto = self.get_prototype(name, func);

		self.current_fn = Some(CIRFunction {
			variables: vec![],
			blocks: vec![],
			ret: proto.ret.clone(),
			arg_count: func.params.params.len(),
			type_params: func.type_params.clone(),
			attributes,
			is_extern: true,
			is_variadic: func.params.variadic,
			mangled_name: None,
		});

		for param in &func.params.params {
			if let Some(name) = &param.1 {
				self.insert_variable(name.clone(), param.0.clone());
			}
			
		}

		(proto, self.current_fn.take().unwrap())
	}

	pub fn generate_function(&mut self, func: CIRFnPrototype, fn_block: &Expr) {
		self.current_fn = self.module.functions.remove(&func);

		let _ = self.generate_expr(fn_block);

		self.current_fn.borrow_mut().as_mut().unwrap().is_extern = false;

		self.module.functions.insert(func, self.current_fn.take().unwrap());
	}

	// Shorthand
	fn get_fn_mut(&mut self) -> &mut CIRFunction {
		self.current_fn.as_mut().unwrap()
	}

	fn get_fn(&self) -> &CIRFunction {
		self.current_fn.as_ref().unwrap()
	}

	fn write(&mut self, stmt: CIRStmt) {
		self.current_fn.as_mut().unwrap().blocks[self.current_block].push(stmt)
	}

	fn append_block(&mut self) -> BlockIndex {
		self.get_fn_mut().blocks.push(vec![]);
		self.current_block = self.get_fn().blocks.len() - 1;
		self.current_block
	}

	fn generate_stmt(&mut self, stmt: &Stmt) {
		match stmt {
			Stmt::Expr(expr) => {
				let Some(expr_ir) = self.generate_expr(expr) else { return };
				self.write(CIRStmt::Expression(expr_ir, expr.get_node_data().tk));
			}

			Stmt::Decl(bindings, expr, tk) => {
				if bindings.len() != 1 {
					todo!()
				}

				let (ty, name) = &bindings[0];

				let var = self.insert_variable(name.clone(), ty.clone());
				let idx = var.local;

				if let Some(expr) = expr {
					let Some(val) = self.generate_expr(expr) else { return };
					self.write(CIRStmt::Assignment(
						(var, *tk),
						(val, expr.get_node_data().tk),
					));
				}

				self.name_map_stack
					.last_mut()
					.unwrap()
					.insert(name.clone(), idx);
			}
		}
	}

	// For a given pattern match, generate the appropriate bindings
	fn generate_pattern_bindings(&mut self, pattern: &Pattern, value: LValue, value_ty: &CIRType) {
		match pattern {
			Pattern::Binding(Binding { name: Some(name), ty, .. }) => {
				let cir_ty = self.convert_type(ty);
				let idx = self.get_fn().variables.len();

				self.get_fn_mut()
					.variables
					.push((cir_ty.clone(), Some(name.clone())));

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
						(store_place, (0, 0)),
						(
							RValue::Cast {
								to: cir_ty,
								from: value_ty.clone(),
								val: Operand::LValue(value),
							},
							(0, 0),
						),
					));
				} else {
					self.write(CIRStmt::Assignment(
						(store_place, (0, 0)),
						(RValue::Atom(cir_ty, None, Operand::LValue(value)), (0, 0)),
					));
				}
			}

			Pattern::Binding(Binding { name: None, ..}) => {}

			_ => todo!(),
		}
	}

	fn generate_binding(&mut self, ty: &Type, name: Name, elem: &Option<Box<Expr>>) {
		let cir_ty = self.convert_type(ty);
		let idx = self.get_fn().variables.len();

		self.get_fn_mut()
			.variables
			.push((cir_ty, Some(name.clone())));
		self.name_map_stack.last_mut().unwrap().insert(name, idx);

		let lval = LValue {
			local: self.get_fn().variables.len() - 1,
			projection: vec![],
		};

		if let Some(elem) = elem {
			if let Some(rval) = self.generate_expr(elem) {
				self.write(CIRStmt::Assignment(
					(lval, (0, 0)),
					(rval, elem.get_node_data().tk),
				));
			}
		}
	}

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
			self.generate_stmt(item);
		}

		// Check if the block has a result statement
		if let Some(result) = result {
			let Some(result_ir) = self.generate_expr(result) else { return (jump_idx, None); };
			let result_type = self.convert_type(result.get_type());
			let result = self.get_as_operand(result_type.clone(), result_ir);

			self.name_map_stack.pop();

			(jump_idx, Some(RValue::Atom(result_type, None, result)))
		} else {
			self.name_map_stack.pop();
			(jump_idx, Some(Self::get_void_rvalue()))
		}
	}

	// generate_expr only returns None if `expr` is a "never expression"
	// aka an expression that will never evaluate to a value
	#[must_use]
	fn generate_expr(&mut self, expr: &Expr) -> Option<RValue> {
		let expr_ty = expr.get_type();

		match expr {
			Expr::Atom(atom, _) => match atom {
				Atom::IntegerLit(i, b) => Some(if let Some(b) = b {
					RValue::Atom(CIRType::Basic(*b), None, Operand::IntegerLit(*i))
				} else {
					RValue::Atom(self.convert_type(expr_ty), None, Operand::IntegerLit(*i))
				}),

				Atom::FloatLit(f, b) => Some(if let Some(b) = b {
					RValue::Atom(CIRType::Basic(*b), None, Operand::FloatLit(*f))
				} else {
					RValue::Atom(self.convert_type(expr_ty), None, Operand::FloatLit(*f))
				}),

				Atom::BoolLit(b) => Some(RValue::Atom(
					CIRType::Basic(Basic::Bool),
					None,
					Operand::BoolLit(*b),
				)),

				Atom::StringLit(s) => Some(RValue::Atom(
					CIRType::Basic(Basic::Str),
					None,
					Operand::StringLit(s.clone()),
				)),

				Atom::CStringLit(s) => Some(RValue::Atom(
					CIRType::Pointer(Box::new(CIRType::Basic(Basic::Integral {
						signed: false,
						size_bytes: 1,
					}))),
					None,
					Operand::CStringLit(s.clone()),
				)),

				Atom::ArrayLit(_a) => todo!(),

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
							indices.push(members_map[elem.0.as_ref().unwrap()]);
						}
					} else {
						panic!()
					}

					let tmp = self.insert_temporary(
						cir_ty.clone(),
						RValue::Atom(cir_ty.clone(), None, Operand::Undef),
					);

					for i in 0..indices.len() {
						let mem_expr = self.generate_expr(&elems[i].1);
						let mut mem_lval = tmp.clone();

						mem_lval.projection.push(PlaceElem::Field(indices[i]));

						if let Some(mem_expr) = mem_expr {
							self.write(CIRStmt::Assignment(
								(mem_lval, (0, 0)),
								(mem_expr, elems[i].1.get_node_data().tk),
							))
						}
					}

					Some(RValue::Atom(cir_ty, None, Operand::LValue(tmp)))
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
						Operand::LValue(LValue {
							local: idx,
							projection: vec![],
						}),
					))
				}

				Atom::Cast(expr, to) => {
					let from = self.convert_type(expr.get_type());
					let to = self.convert_type(to);

					self.generate_expr(expr).map(|castee| RValue::Cast {
						val: self.get_as_operand(from.clone(), castee),
						from,
						to,
					})
				}

				Atom::FnCall {
					name,
					args,
					type_args,
					resolved: Some(resolved),
				} => {
					let cir_args = args
						.iter()
						.map(|arg| {
							let cir_ty = self.convert_type(arg.get_type());
							let cir_expr = self.generate_expr(arg).unwrap();

							if let RValue::Atom(_, None, Operand::LValue(lval)) = cir_expr {
								lval
							} else {
								self.insert_temporary(cir_ty, cir_expr)
							}
						})
						.collect();

					let cir_type_args = type_args
						.iter()
						.map(|arg| self.convert_type(&arg.1))
						.collect();

					let mut name = name.clone();
					name.absolute = true;

					Some(RValue::Atom(
						self.convert_type(&resolved.read().unwrap().ret),
						None,
						Operand::FnCall(self.get_prototype(name, &resolved.read().unwrap()), cir_args, cir_type_args),
					))
				}

				Atom::FnCall { resolved: None, .. } => panic!(),

				Atom::Block { items, result } => self.generate_block(items, result, false).1,

				Atom::CtrlFlow(ctrl) => match &**ctrl {
					ControlFlow::Return { expr } => {
						if let Some(expr) = expr {
							let expr_ir = self.generate_expr(expr)?;

							self.write(CIRStmt::Return(Some((expr_ir, expr.get_node_data().tk))));
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
								RValue::Atom(cir_ty.clone(), None, Operand::Undef),
							))
						} else {
							None
						};

						let mut has_result = false;
						// Generate condition directly in current block, since we don't need to jump back to it
						let cond_ir = self.generate_expr(cond)?;
						let start_block = self.current_block;

						let (if_idx, block_ir) = self.generate_block(items, result, false);

						if let Some(if_val) = block_ir {
							if let Some(result) = &result_loc {
								self.write(CIRStmt::Assignment(
									(result.clone(), (0, 0)),
									(if_val, body_meta.tk),
								));
								has_result = true;
							} else {
								self.write(CIRStmt::Expression(if_val, body_meta.tk));
							}
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
										(result.clone(), (0, 0)),
										(else_val, else_meta.tk),
									));
									has_result = true;
								} else {
									self.write(CIRStmt::Expression(else_val, else_meta.tk));
								}
							}
							let cont_block = self.append_block();

							self.current_block = start_block;

							self.generate_branch(cond_ir, if_idx, else_idx);

							self.get_fn_mut().blocks[if_idx].push(CIRStmt::Jump(cont_block));
							self.get_fn_mut().blocks[else_idx].push(CIRStmt::Jump(cont_block));
							self.current_block = cont_block;
						} else {
							let cont_block = self.append_block();

							self.current_block = start_block;
							self.generate_branch(cond_ir, if_idx, cont_block);

							self.get_fn_mut().blocks[if_idx].push(CIRStmt::Jump(cont_block));
							self.current_block = cont_block;
						}

						if has_result {
							if let Some(result) = result_loc {
								Some(RValue::Atom(cir_ty, None, Operand::LValue(result)))
							} else {
								Some(RValue::Atom(cir_ty, None, Operand::Undef))
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

						// Write jump-to-cond statement to start block
						self.current_block = start_block;
						self.write(CIRStmt::Jump(cond_block));

						// Generate body
						let (body_idx, result) = self.generate_block(items, result, false);

						// Only write a terminator if the block returns, aka result.is_some()
						if result.is_some() {
							// Write jump-to-cond statement to body block
							self.write(CIRStmt::Jump(cond_block));
						}

						let next_block = self.append_block();

						self.current_block = cond_block;
						self.generate_branch(cond_ir, body_idx, next_block);

						self.current_block = next_block;

						Some(Self::get_void_rvalue())
					}

					ControlFlow::For {
						init,
						cond,
						iter,
						body,
					} => {
						let start_block = self.current_block;

						// Write init to start block
						if let Some(init) = init {
							self.generate_stmt(init);
						}

						let loop_block = self.append_block();

						// Generate body
						let body_ir = self.generate_expr(body)?;
						self.write(CIRStmt::Expression(body_ir, (0, 0)));

						let body_block = self.current_block;

						// Add iter statement to body
						if let Some(iter) = iter {
							let iter_ir = self.generate_expr(iter)?;
							self.write(CIRStmt::Expression(iter_ir, (0, 0)));
						}

						self.current_block = body_block;
						self.write(CIRStmt::Jump(loop_block));

						self.current_block = start_block;
						self.write(CIRStmt::Jump(loop_block));

						let next_block = self.append_block();
						self.current_block = loop_block;

						if let Some(cond) = cond {
							if let Some(cond_ir) = self.generate_expr(cond) {
								self.generate_branch(cond_ir, body_block, next_block);
							}
						} else {
							self.write(CIRStmt::Jump(body_block));
						}

						self.current_block = next_block;

						Some(Self::get_void_rvalue())
					}

					ControlFlow::Break => todo!(),
					ControlFlow::Continue => todo!(),

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
							RValue::Atom(disc_ty.clone(), None, Operand::IntegerLit(0)),
						);

						let mut branches_ir = vec![];
						let mut has_result = false;

						let result_loc = if cir_ty != CIRType::Basic(Basic::Void) {
							Some(self.insert_temporary(
								cir_ty.clone(),
								RValue::Atom(cir_ty.clone(), None, Operand::Undef),
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
								},
							);

							let mult_ir = self.get_as_operand(
								disc_ty.clone(),
								RValue::Cons(
									disc_ty.clone(),
									[
										(disc_ty.clone(), Operand::IntegerLit(i as i128 + 1)),
										(disc_ty.clone(), cast_ir),
									],
									Operator::Mul,
								),
							);

							let add_ir = CIRStmt::Assignment(
								(disc_lval.clone(), (0, 0)),
								(
									RValue::Cons(
										disc_ty.clone(),
										[
											(disc_ty.clone(), Operand::LValue(disc_lval.clone())),
											(disc_ty.clone(), mult_ir.clone()),
										],
										Operator::Add,
									),
									(0, 0),
								),
							);

							self.write(add_ir);

							branches_ir.push((
								disc_ty.clone(),
								Operand::IntegerLit(i as i128 + 1),
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
								pattern,
								scrutinee_lval.clone(),
								&scrutinee_ty,
							);

							let (_, match_result) = self.generate_block(items, result, true);

							if let Some(match_result) = match_result {
								if let Some(result_loc) = &result_loc {
									self.write(CIRStmt::Assignment(
										(result_loc.clone(), (0, 0)),
										(match_result, branch_meta.tk),
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
							RValue::Atom(disc_ty, None, Operand::LValue(disc_lval)),
							branches_ir,
							cont_block,
						));
						self.current_block = cont_block;

						if has_result {
							if let Some(result_loc) = result_loc {
								Some(RValue::Atom(cir_ty, None, Operand::LValue(result_loc)))
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
						return Some(RValue::Atom(cir_ty, None, Operand::LValue(LValue { local, projection: vec![] })));
					}

					let once_uneval = &mut *once.write().unwrap();
					let OnceAtom::Uneval(expr) = once_uneval else { panic!() };

					let expr_ir = self.generate_expr(expr)?;
					let local = self.insert_temporary(cir_ty.clone(), expr_ir);
					*once_uneval = OnceAtom::Eval(local.local);

					Some(RValue::Atom(cir_ty, None, Operand::LValue(local)))
				},
			},

			Expr::Cons([lhs, rhs], op, _) => {
				if op.is_compound_assignment() {
					let op = op.get_compound_operator();
					let lval_ir = self.generate_lvalue_expr(lhs)?;
					let rval_ir = self.generate_expr(rhs)?;

					let l_ty = self.convert_type(lhs.get_type());
					let r_ty = self.convert_type(rhs.get_type());

					let r_tmp = self.get_as_operand(r_ty.clone(), rval_ir);

					let expr = RValue::Cons(
						self.convert_type(expr_ty),
						[
							(l_ty.clone(), Operand::LValue(lval_ir.clone())),
							(r_ty.clone(), r_tmp),
						],
						op,
					);

					let expr_tmp = self.get_as_operand(l_ty.clone(), expr);

					self.write(CIRStmt::Assignment(
						(lval_ir.clone(), lhs.get_node_data().tk),
						(RValue::Atom(r_ty, None, expr_tmp), rhs.get_node_data().tk),
					));

					Some(RValue::Atom(l_ty, None, Operand::LValue(lval_ir)))
				} else {
					match op {
						Operator::MemberAccess => match &**rhs {
							Expr::Atom(
								Atom::FnCall {
									name,
									args,
									type_args,
									resolved: Some(resolved),
								},
								_,
							) => {
								let rhs_ty = self.convert_type(rhs.get_type());

								let mut cir_args = vec![];
								cir_args.reserve(args.len());

								for arg in args {
									let cir_ty = self.convert_type(arg.get_type());
									let cir_expr = self.generate_expr(arg)?;
									cir_args.push(self.insert_temporary(cir_ty, cir_expr))
								}

								let cir_type_args = type_args
									.iter()
									.map(|arg| self.convert_type(&arg.1))
									.collect();

								Some(RValue::Atom(
									rhs_ty,
									None,
									Operand::FnCall(self.get_prototype(name.clone(), &resolved.read().unwrap()), cir_args, cir_type_args),
								))
							}

							Expr::Atom(Atom::Identifier(_), _) => {
								let lval = self.generate_lvalue_expr(expr)?;
								let cir_ty = self.convert_type(rhs.get_type());
								Some(RValue::Atom(cir_ty, None, Operand::LValue(lval)))
							}

							_ => panic!(),
						},

						Operator::Subscr => {
							let lval = self.generate_lvalue_expr(expr)?;
							let cir_ty = self.convert_type(expr_ty);
							Some(RValue::Atom(cir_ty, None, Operand::LValue(lval)))
						}

						Operator::Assign => {
							let lval_ir = self.generate_lvalue_expr(lhs)?;
							let rval_ir = self.generate_expr(rhs)?;
							let l_ty = self.convert_type(lhs.get_type());
							let r_ty = self.convert_type(rhs.get_type());

							let r_tmp = self.get_as_operand(r_ty.clone(), rval_ir);

							self.write(CIRStmt::Assignment(
								(lval_ir.clone(), lhs.get_node_data().tk),
								(RValue::Atom(r_ty, None, r_tmp), rhs.get_node_data().tk),
							));

							Some(RValue::Atom(l_ty, None, Operand::LValue(lval_ir)))
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
							))
						}
					}
				}
			}

			Expr::Unary(sub, op, _) => {
				let sub_expr = self.generate_expr(sub)?;
				let cir_ty = self.convert_type(sub.get_type());
				let temp = self.get_as_operand(cir_ty.clone(), sub_expr);

				Some(RValue::Atom(cir_ty, Some(op.clone()), temp))
			}
		}
	}

	fn generate_lvalue_expr(&mut self, expr: &Expr) -> Option<LValue> {
		match expr {
			Expr::Atom(atom, _) => match atom {
				Atom::Identifier(id) => Some(LValue {
					local: self.get_var_index(id.expect_scopeless().unwrap()).unwrap(),
					projection: vec![],
				}),

				Atom::Once(_) => {
					let RValue::Atom(_, None, Operand::LValue(lvalue)) = self.generate_expr(expr)? else { panic!() };
					Some(lvalue)
				},

				_ => panic!(),
			},

			Expr::Cons([lhs, rhs], op, _) => match op {
				Operator::MemberAccess => {
					let mut lhs_ir = self.generate_lvalue_expr(lhs)?;
					let lhs_ty = self.convert_type(lhs.get_type());

					let CIRType::TypeRef(id, _params) = lhs_ty else { panic!() };
					let CIRTypeDef::Algebraic { members_map, .. } = &self.module.types[&id] else { panic!() };

					let Expr::Atom(Atom::Identifier(id), _) = &**rhs else { panic!() };

					let idx = members_map[id.expect_scopeless().unwrap()];

					lhs_ir.projection.push(PlaceElem::Field(idx));

					Some(lhs_ir)
				}

				Operator::Subscr => {
					let mut indexed = self.generate_lvalue_expr(lhs)?;
					indexed
						.projection
						.push(PlaceElem::Index(self.generate_expr(rhs)?));
					Some(indexed)
				}

				_ => panic!(),
			},

			Expr::Unary(val, op, _) => match op {
				Operator::Deref => {
					let mut derefee = self.generate_lvalue_expr(val)?;
					derefee.projection.push(PlaceElem::Deref);
					Some(derefee)
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
								Operand::LValue(LValue {
									local: value.local,
									projection: vec![PlaceElem::Field(0)],
								}),
							),
							(disc_type, Operand::IntegerLit(discriminant as i128)),
						],
						Operator::Eq,
					)
				} else {
					todo!()
				}
			}
			Pattern::Destructure(_, _) => todo!(),
			Pattern::Or(_, _) => todo!(),
		}
	}

	fn generate_branch(&mut self, cond: RValue, a: BlockIndex, b: BlockIndex) {
		self.write(CIRStmt::Switch(
			cond,
			vec![(CIRType::Basic(Basic::Bool), Operand::BoolLit(true), a)],
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

	fn insert_variable(&mut self, name: Name, ty: Type) -> LValue {
		let cir_ty = self.convert_type(&ty);
		let idx = self.get_fn().variables.len();

		self.get_fn_mut()
			.variables
			.push((cir_ty, Some(name.clone())));

		self.name_map_stack.last_mut().unwrap().insert(name, idx);
		LValue {
			local: idx,
			projection: vec![],
		}
	}

	fn get_as_operand(&mut self, ty: CIRType, rval: RValue) -> Operand {
		if let RValue::Atom(_, None, operand) = rval {
			operand
		} else {
			Operand::LValue(self.insert_temporary(ty, rval))
		}
	}

	fn insert_temporary(&mut self, ty: CIRType, rval: RValue) -> LValue {
		self.get_fn_mut().variables.push((ty, None));

		let lval = LValue {
			local: self.get_fn().variables.len() - 1,
			projection: vec![],
		};

		self.write(CIRStmt::Assignment((lval.clone(), (0, 0)), (rval, (0, 0))));

		lval
	}

	fn get_void_rvalue() -> RValue {
		RValue::Atom(CIRType::Basic(Basic::Void), None, Operand::Undef)
	}
}
