use std::{borrow::BorrowMut, collections::HashMap, sync::RwLock};

use crate::{
	constexpr::{ConstExpr, ConstValue},
	modules::ModuleState,
	semantic::{
		ast::{ASTElem, ASTNode},
		controlflow::ControlFlow,
		expression::{Atom, Expr, Operator},
		namespace::{Identifier, ItemRef, Name, Namespace, NamespaceASTElem, NamespaceItem},
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

		for elem in &namespace.children {
			match &elem.1 .0 {
				NamespaceItem::Function(func, _) => {
					let cir_fn = self.generate_prototype(&func.read().unwrap(), elem.1 .1.clone());

					self.module.functions.insert(elem.0.clone(), cir_fn);
				}

				_ => {}
			}
		}
	}

	fn generate_namespace(&mut self, namespace: &Namespace) {
		for im in &namespace.impls {
			for elem in im.1 {
				match &elem.1 .0 {
					NamespaceItem::Function(_, ast) => {
						let name = Identifier::from_parent(im.0, elem.0.clone());
						let mut cir_fn = self.module.functions.remove(&name).unwrap();

						if let NamespaceASTElem::Parsed(ast) = &*ast.borrow() {
							cir_fn = self.generate_function(cir_fn, &ast.node);
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
						cir_fn = self.generate_function(cir_fn, &ast.node);
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

	pub fn generate_function(&mut self, func: CIRFunction, fn_block: &ASTNode) -> CIRFunction {
		self.current_fn = Some(func);

		if let ASTNode::Block(elems) = fn_block {
			self.generate_block(elems);
		}

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

	fn generate_block<'ctx>(&mut self, block: &Vec<ASTElem>) -> BlockIndex {
		self.append_block();
		self.name_map_stack.push(HashMap::new());

		for elem in block {
			match &elem.node {
				ASTNode::Block(elems) => {
					self.generate_block(elems);
					self.append_block();
				}

				ASTNode::Expression(expr) => {
					let expr_ir = self
						.generate_expr(&expr.borrow(), elem.type_info.borrow().as_ref().unwrap());
					self.write(CIRStmt::Expression(expr_ir, elem.token_data));
				}

				ASTNode::Declaration(ty, name, elem) => self.generate_decl(ty, name.clone(), elem),

				ASTNode::ControlFlow(ctrl) => match &**ctrl {
					ControlFlow::Return { expr } => {
						if let Some(expr) = expr {
							let expr_ir = self.generate_expr(
								&expr.get_expr().borrow(),
								expr.type_info.borrow().as_ref().unwrap(),
							);
							self.write(CIRStmt::Return(Some((expr_ir, expr.token_data))));
						} else {
							self.write(CIRStmt::Return(None));
						}
					}

					ControlFlow::If {
						cond,
						body,
						else_body,
					} => {
						let cond_ir = self.generate_expr(
							&cond.get_expr().borrow(),
							cond.type_info.borrow().as_ref().unwrap(),
						);
						let start_block = self.current_block;
						let if_block = if let ASTNode::Block(elems) = &body.node {
							self.generate_block(elems)
						} else {
							panic!()
						};

						if let Some(else_body) = else_body {
							let else_block = if let ASTNode::Block(elems) = &else_body.node {
								self.generate_block(elems)
							} else {
								panic!()
							};
							let cont_block = self.append_block();

							self.current_block = start_block;
							self.write(CIRStmt::Branch(cond_ir, if_block, else_block));

							self.get_fn_mut().blocks[if_block].push(CIRStmt::Jump(cont_block));
							self.get_fn_mut().blocks[else_block].push(CIRStmt::Jump(cont_block));
							self.current_block = cont_block;
						} else {
							let cont_block = self.append_block();

							self.current_block = start_block;
							self.write(CIRStmt::Branch(cond_ir, if_block, cont_block));

							self.get_fn_mut().blocks[if_block].push(CIRStmt::Jump(cont_block));
							self.current_block = cont_block;
						}
					}

					ControlFlow::While { cond, body } => {
						let start_block = self.current_block;
						let cond_block = self.append_block();

						// Write jump-to-cond to start block
						self.current_block = start_block;
						self.write(CIRStmt::Jump(cond_block));

						// Generate body
						let body_block = if let ASTNode::Block(elems) = &body.node {
							self.generate_block(elems)
						} else {
							panic!()
						};

						// Write jump-to-cond to body block
						self.write(CIRStmt::Jump(cond_block));

						let next_block = self.append_block();

						self.current_block = cond_block;
						let cond_ir = self.generate_expr(
							&cond.get_expr().borrow(),
							cond.type_info.borrow().as_ref().unwrap(),
						);
						self.write(CIRStmt::Branch(cond_ir, body_block, next_block));

						self.current_block = next_block;
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
							if let ASTNode::Declaration(ty, name, elem) = &init.node {
								self.generate_decl(ty, name.clone(), elem);
							}
						}

						let loop_block = self.append_block();
						self.current_block = start_block;
						self.write(CIRStmt::Jump(loop_block));

						// Generate body
						let body_block = if let ASTNode::Block(elems) = &body.node {
							self.generate_block(elems)
						} else {
							panic!()
						};

						// Add iter statement to body
						if let Some(iter) = iter {
							let iter_ir = self.generate_expr(
								&iter.get_expr().borrow(),
								iter.type_info.borrow().as_ref().unwrap(),
							);
							self.write(CIRStmt::Expression(iter_ir, iter.token_data));
						}

						// Write jump-to-loop to body block
						self.write(CIRStmt::Jump(loop_block));

						let next_block = self.append_block();
						self.current_block = loop_block;

						if let Some(cond) = cond {
							let cond_ir = self.generate_expr(
								&cond.get_expr().borrow(),
								cond.type_info.borrow().as_ref().unwrap(),
							);
							self.write(CIRStmt::Branch(cond_ir, body_block, next_block));
						} else {
							self.write(CIRStmt::Jump(body_block));
						}

						self.current_block = next_block;
					}

					ControlFlow::Break => todo!(),

					ControlFlow::Continue => todo!(),
				},
			}
		}
		self.name_map_stack.pop();

		self.current_block
	}

	fn generate_decl(&mut self, ty: &Type, name: Name, elem: &Option<Box<ASTElem>>) {
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
			let rval = self.generate_expr(&elem.get_expr().borrow(), ty);
			self.write(CIRStmt::Assignment((lval, (0, 0)), (rval, elem.token_data)));
		}
	}

	fn generate_expr(&mut self, expr: &Expr, expr_ty: &Type) -> RValue {
		match expr {
			Expr::Atom(atom, _) => match atom {
				Atom::IntegerLit(i, b) => {
					if let Some(b) = b {
						RValue::Atom(CIRType::Basic(*b), None, Operand::IntegerLit(*i))
					} else {
						RValue::Atom(self.convert_type(expr_ty), None, Operand::IntegerLit(*i))
					}
				}

				Atom::FloatLit(f, b) => {
					if let Some(b) = b {
						RValue::Atom(CIRType::Basic(*b), None, Operand::FloatLit(*f))
					} else {
						RValue::Atom(self.convert_type(expr_ty), None, Operand::FloatLit(*f))
					}
				}

				Atom::BoolLit(b) => {
					RValue::Atom(CIRType::Basic(Basic::BOOL), None, Operand::BoolLit(*b))
				}

				Atom::StringLit(s) => RValue::Atom(
					CIRType::Basic(Basic::STR),
					None,
					Operand::StringLit(s.clone()),
				),

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
						let mem_expr = self.generate_expr(
							&elems[i].1.get_expr().borrow(),
							elems[i].1.type_info.borrow().as_ref().unwrap(),
						);
						let mut mem_lval = tmp.clone();

						mem_lval.projection.push(PlaceElem::Field(indices[i]));

						self.write(CIRStmt::Assignment(
							(mem_lval, (0, 0)),
							(mem_expr, elems[i].2),
						))
					}

					RValue::Atom(cir_ty, None, Operand::LValue(tmp))
				}

				Atom::Identifier(id) => {
					let idx = self.get_var_index(id.expect_scopeless().unwrap()).unwrap();
					let lval_ty = &self.get_fn().variables[idx].0;
					RValue::Atom(
						lval_ty.clone(),
						None,
						Operand::LValue(LValue {
							local: idx,
							projection: vec![],
						}),
					)
				}

				Atom::Cast(expr, to) => {
					let castee = self.generate_expr(
						&expr.get_expr().borrow(),
						expr.type_info.borrow().as_ref().unwrap(),
					);
					let from = self.convert_type(expr.type_info.borrow().as_ref().unwrap());
					let to = self.convert_type(to);
					RValue::Cast {
						val: self.get_as_operand(from.clone(), castee),
						from,
						to,
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
							let cir_ty =
								self.convert_type(arg.type_info.borrow().as_ref().unwrap());
							let cir_expr = self.generate_expr(
								&arg.get_expr().borrow(),
								arg.type_info.borrow().as_ref().unwrap(),
							);

							self.insert_temporary(cir_ty, cir_expr)
						})
						.collect();

					let cir_type_args = type_args
						.iter()
						.map(|arg| self.convert_type(&arg.1))
						.collect();

					let mut name = name.clone();
					name.absolute = true;

					RValue::Atom(
						self.convert_type(ret.as_ref().unwrap()),
						None,
						Operand::FnCall(name, cir_args, cir_type_args),
					)
				}
			},

			Expr::Cons(op, elems, _) => {
				if op.is_compound_assignment() {
					let op = op.get_compound_operator();
					let lval_ir = self.generate_lvalue_expr(&elems[0].0);
					let rval_ir = self.generate_expr(&elems[1].0, elems[1].1.as_ref().unwrap());
					let l_ty = self.convert_type(elems[0].1.as_ref().unwrap());
					let r_ty = self.convert_type(elems[1].1.as_ref().unwrap());

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
						(lval_ir.clone(), elems[0].2),
						(RValue::Atom(r_ty, None, expr_tmp), elems[1].2),
					));

					RValue::Atom(l_ty, None, Operand::LValue(lval_ir))
				} else {
					if elems.len() == 1 {
						let sub_expr =
							self.generate_expr(&elems[0].0, elems[0].1.as_ref().unwrap());
						let cir_ty = self.convert_type(elems[0].1.as_ref().unwrap());
						let temp = self.get_as_operand(cir_ty.clone(), sub_expr);

						RValue::Atom(cir_ty, Some(op.clone()), temp)
					} else {
						match op {
							Operator::MemberAccess => match &elems[1].0 {
								Expr::Atom(
									Atom::FnCall {
										name,
										args,
										type_args,
										..
									},
									_,
								) => {
									let rhs_ty = self.convert_type(elems[1].1.as_ref().unwrap());

									let cir_args = args
										.iter()
										.map(|arg| {
											let cir_ty = self.convert_type(
												arg.type_info.borrow().as_ref().unwrap(),
											);
											let cir_expr = self.generate_expr(
												&arg.get_expr().borrow(),
												arg.type_info.borrow().as_ref().unwrap(),
											);

											self.insert_temporary(cir_ty, cir_expr)
										})
										.collect();

									let cir_type_args = type_args
										.iter()
										.map(|arg| self.convert_type(&arg.1))
										.collect();

									RValue::Atom(
										rhs_ty,
										None,
										Operand::FnCall(name.clone(), cir_args, cir_type_args),
									)
								}

								Expr::Atom(Atom::Identifier(_), _) => {
									let lval = self.generate_lvalue_expr(expr);
									let cir_ty = self.convert_type(elems[1].1.as_ref().unwrap());
									RValue::Atom(cir_ty, None, Operand::LValue(lval))
								}

								_ => panic!(),
							},

							Operator::Subscr => {
								let lval = self.generate_lvalue_expr(expr);
								let cir_ty = self.convert_type(expr_ty);
								RValue::Atom(cir_ty, None, Operand::LValue(lval))
							}

							Operator::Assign => {
								let lval_ir = self.generate_lvalue_expr(&elems[0].0);
								let rval_ir =
									self.generate_expr(&elems[1].0, elems[1].1.as_ref().unwrap());
								let l_ty = self.convert_type(elems[0].1.as_ref().unwrap());
								let r_ty = self.convert_type(elems[1].1.as_ref().unwrap());

								let r_tmp = self.get_as_operand(r_ty.clone(), rval_ir);

								self.write(CIRStmt::Assignment(
									(lval_ir.clone(), elems[0].2),
									(RValue::Atom(r_ty, None, r_tmp), elems[1].2),
								));

								RValue::Atom(l_ty, None, Operand::LValue(lval_ir))
							}

							_ => {
								let lhs =
									self.generate_expr(&elems[0].0, elems[0].1.as_ref().unwrap());
								let rhs =
									self.generate_expr(&elems[1].0, elems[1].1.as_ref().unwrap());
								let lhs_ty = self.convert_type(elems[0].1.as_ref().unwrap());
								let rhs_ty = self.convert_type(elems[1].1.as_ref().unwrap());
								let lhs_tmp = self.get_as_operand(lhs_ty.clone(), lhs);
								let rhs_tmp = self.get_as_operand(rhs_ty.clone(), rhs);
								RValue::Cons(
									self.convert_type(expr_ty),
									[(lhs_ty, lhs_tmp), (rhs_ty, rhs_tmp)],
									op.clone(),
								)
							}
						}
					}
				}
			}
		}
	}

	fn generate_lvalue_expr(&mut self, expr: &Expr) -> LValue {
		match expr {
			Expr::Atom(atom, _) => match atom {
				Atom::Identifier(id) => LValue {
					local: self.get_var_index(id.expect_scopeless().unwrap()).unwrap(),
					projection: vec![],
				},

				_ => panic!(),
			},

			Expr::Cons(op, elems, _) => match op {
				Operator::MemberAccess => {
					let mut lhs = self.generate_lvalue_expr(&elems[0].0);
					let lhs_ty = self.convert_type(&elems[0].1.as_ref().unwrap());

					if let CIRType::TypeRef(id, _params) = lhs_ty {
						if let CIRTypeDef::Algebraic { members_map, .. } = &self.module.types[&id] {
							if let Expr::Atom(Atom::Identifier(id), _) = &elems[1].0 {
								let idx = members_map[id.expect_scopeless().unwrap()];

								lhs.projection.push(PlaceElem::Field(idx));

								return lhs;
							}
						}
					}
					panic!()
				}

				Operator::Deref => {
					let mut derefee = self.generate_lvalue_expr(&elems[0].0);
					derefee.projection.push(PlaceElem::Deref);
					derefee
				}

				Operator::Subscr => {
					let mut indexed = self.generate_lvalue_expr(&elems[0].0);
					let index = self.generate_expr(&elems[1].0, elems[1].1.as_ref().unwrap());
					indexed.projection.push(PlaceElem::Index(index));
					indexed
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

	fn insert_variable(&mut self, name: Name, ty: Type) {
		// TODO: Deal with shadowing and scopes
		let cir_ty = self.convert_type(&ty);
		let idx = self.get_fn().variables.len();

		self.get_fn_mut()
			.variables
			.push((cir_ty, Some(name.clone())));

		self.name_map_stack.last_mut().unwrap().insert(name, idx);
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
}
