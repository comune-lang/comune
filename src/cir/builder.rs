use std::{borrow::BorrowMut, collections::HashMap};

use crate::{
	constexpr::{ConstExpr, ConstValue},
	modules::ModuleState,
	semantic::{
		controlflow::ControlFlow,
		expression::{Atom, Expr, Operator},
		namespace::{Identifier, ItemRef, Name, Namespace, NamespaceASTElem, NamespaceItem},
		statement::Stmt,
		types::{Basic, FnDef, Type, TypeDef, TypeRef},
		Attribute,
	},
};

use super::{
	BlockIndex, CIRFunction, CIRModule, CIRStmt, CIRType, CIRTypeDef, LValue, Operand, PlaceElem,
	RValue, TypeName, VarIndex,
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
		for im in &namespace.impls {
			for elem in im.1 {
				match &elem.1 .0 {
					NamespaceItem::Function(func, _) => {
						let cir_fn = self.generate_prototype(&func.read().unwrap(), vec![]);

						self.module
							.functions
							.insert(Identifier::from_parent(im.0, elem.0.clone()), cir_fn);
					}

					_ => panic!(),
				}
			}
		}

		for import in &namespace.imported {
			self.register_namespace(import.1);
		}

		for (name, elem) in &namespace.children {
			match &elem.0 {
				NamespaceItem::Function(func, _) => {
					let cir_fn = self.generate_prototype(&func.read().unwrap(), elem.1.clone());

					self.module.functions.insert(name.clone(), cir_fn);
				}

				_ => {}
			}
		}
	}

	fn generate_namespace(&mut self, namespace: &Namespace) {
		for im in &namespace.impls {
			for (impl_name, elem) in im.1 {
				match &elem.0 {
					NamespaceItem::Function(_, ast) => {
						let name = Identifier::from_parent(im.0, impl_name.clone());
						let mut cir_fn = self.module.functions.remove(&name).unwrap();

						if let NamespaceASTElem::Parsed(ast) = &*ast.borrow() {
							cir_fn = self.generate_function(cir_fn, ast);
						}

						self.module.functions.insert(name, cir_fn);
					}

					_ => panic!(),
				}
			}
		}

		for elem in &namespace.children {
			match &elem.1 .0 {
				NamespaceItem::Function(_, node) => {
					let name = elem.0.clone();
					let mut cir_fn = self.module.functions.remove(&name).unwrap();

					if let NamespaceASTElem::Parsed(ast) = &*node.borrow() {
						cir_fn = self.generate_function(cir_fn, ast);
					}

					self.module.functions.insert(name, cir_fn);
				}

				_ => {}
			}
		}
	}

	fn convert_type(&mut self, ty: &Type) -> CIRType {
		match ty {
			Type::Basic(basic) => CIRType::Basic(basic.clone()),

			Type::TypeRef(ItemRef::Resolved(ty)) => {
				let idx = self.convert_type_def(&ty);
				let args_cir = ty
					.args
					.iter()
					.map(|(_, ty)| self.convert_type(ty))
					.collect();

				CIRType::TypeRef(idx, args_cir)
			}

			Type::TypeParam(idx) => CIRType::TypeParam(*idx),

			Type::Pointer(pointee) => CIRType::Pointer(Box::new(self.convert_type(pointee))),

			Type::Reference(refee) => CIRType::Reference(Box::new(self.convert_type(refee))),

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

					for item in &alg.items {
						match &item.1 .0 {
							NamespaceItem::Variable(ty, _) => {
								members_map.insert(item.0.clone(), members.len());
								members.push(self.convert_type(&ty));
							}

							NamespaceItem::Type(_ty) => {
								todo!()
							}

							_ => panic!(),
						}
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
	pub fn generate_prototype(&mut self, func: &FnDef, attributes: Vec<Attribute>) -> CIRFunction {
		self.current_fn = Some(CIRFunction {
			variables: vec![],
			blocks: vec![],
			ret: self.convert_type(&func.ret),
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

		self.current_fn.take().unwrap()
	}

	pub fn generate_function(&mut self, func: CIRFunction, fn_block: &Expr) -> CIRFunction {
		self.current_fn = Some(func);

		let result = self.generate_expr(fn_block);

		self.current_fn.borrow_mut().as_mut().unwrap().is_extern = false;

		self.current_fn.take().unwrap()
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

	fn generate_binding(&mut self, ty: &Type, name: Name, elem: &Option<Box<Expr>>) {
		let cir_ty = self.convert_type(ty);
		let idx = self.get_fn().variables.len();

		self.get_fn_mut()
			.variables
			.push((cir_ty, Some(name.clone())));
		self.name_map_stack
			.last_mut()
			.unwrap()
			.insert(name.clone(), idx);

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

	// generate_expr only returns None if `expr` is a "never expression"
	// aka an expression that will never evaluate to a value
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
					CIRType::Basic(Basic::BOOL),
					None,
					Operand::BoolLit(*b),
				)),

				Atom::StringLit(s) => Some(RValue::Atom(
					CIRType::Basic(Basic::STR),
					None,
					Operand::StringLit(s.clone()),
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
						.expect(&format!(
							"cIR error: failed to fetch variable {}",
							id.expect_scopeless().unwrap()
						));
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

					if let Some(castee) = self.generate_expr(expr) {
						Some(RValue::Cast {
							val: self.get_as_operand(from.clone(), castee),
							from,
							to,
						})
					} else {
						None
					}
				}

				Atom::FnCall {
					name,
					args,
					type_args,
					ret,
				} => {
					let cir_args = args
						.iter()
						.map(|arg| {
							let cir_ty = self.convert_type(arg.get_type());
							let cir_expr = self.generate_expr(arg).unwrap();

							self.insert_temporary(cir_ty, cir_expr)
						})
						.collect();

					let cir_type_args = type_args
						.iter()
						.map(|arg| self.convert_type(&arg.1))
						.collect();

					let mut name = name.clone();
					name.absolute = true;

					Some(RValue::Atom(
						self.convert_type(ret.as_ref().unwrap()),
						None,
						Operand::FnCall(name, cir_args, cir_type_args),
					))
				}

				Atom::Block { items, result } => {
					self.append_block();
					self.name_map_stack.push(HashMap::new());

					for item in items {
						self.generate_stmt(item);
					}

					if let Some(result) = result {
						let result_ir = self.generate_expr(result)?;
						let result_type = self.convert_type(result.get_type());
						let result = self.get_as_operand(result_type.clone(), result_ir);

						self.name_map_stack.pop();

						Some(RValue::Atom(result_type, None, result))
					} else {
						self.name_map_stack.pop();
						None
					}
				}

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
						body,
						else_body,
					} => {
						let cir_ty = self.convert_type(expr_ty);

						let result = if cir_ty != CIRType::Basic(Basic::VOID) {
							Some(self.insert_temporary(
								cir_ty.clone(),
								RValue::Atom(cir_ty.clone(), None, Operand::Undef),
							))
						} else {
							None
						};

						let mut has_result = false;

						let cond_ir = self.generate_expr(cond)?;
						let start_block = self.current_block;

						if let Some(if_val) = self.generate_expr(body) {
							if let Some(result) = &result {
								self.write(CIRStmt::Assignment(
									(result.clone(), (0, 0)),
									(if_val, body.get_node_data().tk),
								));
								has_result = true;
							} else {
								self.write(CIRStmt::Expression(if_val, body.get_node_data().tk));
							}
						}

						let if_idx = self.current_block;

						if let Some(else_body) = else_body {
							if let Some(else_val) = self.generate_expr(else_body) {
								if let Some(result) = &result {
									self.write(CIRStmt::Assignment(
										(result.clone(), (0, 0)),
										(else_val, else_body.get_node_data().tk),
									));
									has_result = true;
								} else {
									self.write(CIRStmt::Expression(
										else_val,
										else_body.get_node_data().tk,
									));
								}
							}
							let else_idx = self.current_block;
							let cont_block = self.append_block();

							self.current_block = start_block;
							self.write(CIRStmt::Branch(cond_ir, if_idx, else_idx));

							self.get_fn_mut().blocks[if_idx].push(CIRStmt::Jump(cont_block));
							self.get_fn_mut().blocks[else_idx].push(CIRStmt::Jump(cont_block));
							self.current_block = cont_block;
						} else {
							let cont_block = self.append_block();

							self.current_block = start_block;
							self.write(CIRStmt::Branch(cond_ir, if_idx, cont_block));

							self.get_fn_mut().blocks[if_idx].push(CIRStmt::Jump(cont_block));
							self.current_block = cont_block;
						}

						if has_result {
							if let Some(result) = result {
								Some(RValue::Atom(cir_ty, None, Operand::LValue(result)))
							} else {
								Some(RValue::Atom(cir_ty, None, Operand::Undef))
							}
						} else {
							None
						}
					}

					ControlFlow::While { cond, body } => {
						let cond_ir = self.generate_expr(cond)?;

						let start_block = self.current_block;
						let cond_block = self.append_block();

						// Write jump-to-cond to start block
						self.current_block = start_block;
						self.write(CIRStmt::Jump(cond_block));

						// Generate body
						self.generate_expr(body);
						let body_idx = self.current_block;

						// Write jump-to-cond to body block
						self.write(CIRStmt::Jump(cond_block));

						let next_block = self.append_block();

						self.current_block = cond_block;
						self.write(CIRStmt::Branch(cond_ir, body_idx, next_block));

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

						// Write init and jump to start block

						if let Some(init) = init {
							self.generate_stmt(init);
						}

						let loop_block = self.append_block();
						self.current_block = start_block;
						self.write(CIRStmt::Jump(loop_block));

						// Generate body
						self.generate_expr(body);
						let body_idx = self.current_block;

						// Add iter statement to body
						if let Some(iter) = iter {
							self.generate_expr(iter);
						}

						// Write jump-to-loop to body block
						self.write(CIRStmt::Jump(loop_block));

						let next_block = self.append_block();
						self.current_block = loop_block;

						if let Some(cond) = cond {
							if let Some(cond_ir) = self.generate_expr(cond) {
								self.write(CIRStmt::Branch(cond_ir, body_idx, next_block));
							}
						} else {
							self.write(CIRStmt::Jump(body_idx));
						}

						self.current_block = next_block;

						Some(Self::get_void_rvalue())
					}

					ControlFlow::Break => todo!(),

					ControlFlow::Continue => todo!(),
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
									..
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
									Operand::FnCall(name.clone(), cir_args, cir_type_args),
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

					return Some(lhs_ir);
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
			return operand;
		} else {
			Operand::LValue(self.insert_temporary(ty, rval))
		}
	}

	fn insert_temporary(&mut self, ty: CIRType, rval: RValue) -> LValue {
		self.get_fn_mut().variables.push((ty.clone(), None));

		let lval = LValue {
			local: self.get_fn().variables.len() - 1,
			projection: vec![],
		};

		self.write(CIRStmt::Assignment((lval.clone(), (0, 0)), (rval, (0, 0))));

		lval
	}

	fn get_void_rvalue() -> RValue {
		RValue::Atom(CIRType::Basic(Basic::VOID), None, Operand::Undef)
	}
}
