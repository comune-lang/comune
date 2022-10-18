#![allow(dead_code)]

use std::collections::HashMap;

use crate::{
	constexpr::{ConstExpr, ConstValue},
	modules::ModuleState,
	semantic::{
		ast::{ASTElem, ASTNode},
		controlflow::ControlFlow,
		expression::{Atom, Expr, Operator},
		namespace::{Namespace, NamespaceASTElem, NamespaceItem, Identifier},
		types::{Basic, DataLayout, Type, TypeDef},
	},
};

mod serialize;

// Bunch of type aliases to make code more readable
type CIRBlock = Vec<CIRStmt>;
type BlockIndex = usize;
type StmtIndex = usize;
type VarIndex = usize;
type FieldIndex = usize;
type TypeIndex = usize;

#[derive(Clone, Debug)]
pub struct LValue {
	pub local: VarIndex,
	pub projection: Vec<PlaceElem>,
}

#[derive(Clone, Debug)]
pub enum PlaceElem {
	Deref,
	Field(FieldIndex),
	Index(u64),
}

#[derive(Debug)]
pub enum RValue {
	Atom(CIRType, Option<Operator>, Operand),
	Cons([(CIRType, Operand); 2], Operator),
	Cast{ from: CIRType, to: CIRType, op: Operand},
}

// An Operand represents a single element of a CIR expression.
// This may either be a constant, or a copy or move of an lvalue.
#[derive(Debug)]
pub enum Operand {
	FnCall(Identifier, Vec<RValue>),
	IntegerLit(i128),
	FloatLit(f64),
	StringLit(String),
	BoolLit(bool),
	LValue(LValue),
	Undef,
}

#[derive(Clone, Debug)]
pub enum CIRType {
	Basic(Basic),
	Pointer(Box<CIRType>),
	Array(Box<CIRType>, Vec<i128>),
	Reference(Box<CIRType>),
	TypeRef(TypeIndex),
}

#[derive(Debug)]
pub enum CIRTypeDef {
	Algebraic {
		members: Vec<CIRType>,
		variants: Vec<CIRTypeDef>,
		layout: DataLayout,

		members_map: HashMap<String, usize>,
		variants_map: HashMap<String, usize>,
	},

	Class {

	},
}

#[derive(Debug)]
pub enum CIRStmt {
	Expression(RValue),
	Assignment(LValue, RValue),
	Jump(BlockIndex),
	Branch(RValue, BlockIndex, BlockIndex),
	Return(Option<RValue>),
}

// cIR representation of a function.
// in cIR, variables have no names, just indices.
pub struct CIRFunction {
	pub variables: Vec<(CIRType, Option<String>)>, // Optional name
	pub blocks: Vec<CIRBlock>,
	pub ret: CIRType,
	pub arg_count: usize,

	current_block: BlockIndex,

	name_map: HashMap<String, VarIndex>,
}

pub struct CIRModule {
	pub types: Vec<CIRTypeDef>,
	pub globals: HashMap<String, (CIRType, RValue)>,
	pub functions: HashMap<String, CIRFunction>,

	// We use this during cIR generation to keep track of which TypeRefs map to which CIR type indices.
	// Once cIR generation is complete, we don't use any AST `Type`s anymore, so this field isn't serialized.
	type_map: HashMap<Type, TypeIndex>,
}

impl CIRModule {
	pub fn from_ast(ast: &ModuleState) -> Self {
		let mut result = CIRModule {
			types: vec![],
			globals: HashMap::new(),
			functions: HashMap::new(),
			type_map: HashMap::new(),
		};

		result.generate_namespace(
			&ast.parser.current_namespace().borrow(),
			&ast.parser.current_namespace().borrow(),
		);

		result
	}

	fn generate_namespace(&mut self, namespace: &Namespace, root: &Namespace) {
		for elem in &namespace.children {
			match &elem.1 .0 {
				NamespaceItem::Namespace(ns) => {
					self.generate_namespace(&ns.as_ref().borrow(), root)
				}

				NamespaceItem::Function(ty, node) => {
					if let NamespaceASTElem::Parsed(ast) = &*node.borrow() {
						let cir_fn = CIRFunction::from_ast(&ast.node, &*ty.read().unwrap(), self);

						self.functions
							.insert(elem.1 .2.as_ref().unwrap().clone(), cir_fn);
					}
				}

				_ => {}
			}
		}
	}

	fn convert_type(&mut self, ty: &Type) -> CIRType {
		match ty {
			Type::Basic(basic) => CIRType::Basic(basic.clone()),

			Type::TypeRef(def, _) => {
				if let Some(ty_ref) = self.type_map.get(ty) {
					CIRType::TypeRef(*ty_ref)
				} else {
					let cir_def = self.convert_type_def(&def.upgrade().unwrap().read().unwrap());
					self.types.push(cir_def);
					self.type_map.insert(ty.clone(), self.types.len() - 1);
					CIRType::TypeRef(self.types.len() - 1)
				}
			}

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

			_ => todo!(),
		}
	}

	fn convert_type_def(&mut self, def: &TypeDef) -> CIRTypeDef {
		match def {
			TypeDef::Function(_, _) => todo!(),
			TypeDef::Algebraic(alg) => {
				let mut members = vec![];
				let variants = vec![];
				let mut members_map = HashMap::new();
				let variants_map = HashMap::new();

				for item in &alg.items {
					match &item.1 .0 {
						NamespaceItem::Variable(ty, _) => {
							members_map.insert(item.0.clone(), members.len());
							members.push(self.convert_type(ty));
						}

						NamespaceItem::Type(_ty) => {
							todo!()
						}

						_ => panic!(),
					}
				}

				CIRTypeDef::Algebraic {
					members,
					variants,
					layout: alg.layout,
					members_map,
					variants_map,
				}
			}
		}
	}
}

impl CIRFunction {
	pub fn from_ast(fn_block: &ASTNode, ty: &TypeDef, module: &mut CIRModule) -> Self {
		if let TypeDef::Function(ret, args) = ty {
			let mut result = CIRFunction {
				variables: vec![],
				blocks: vec![],
				current_block: 0,
				name_map: HashMap::new(),
				ret: module.convert_type(ret),
				arg_count: args.len(),
			};

			for param in args {
				if let Some(name) = &param.1 {
					result.insert_variable(name.clone(), param.0.clone(), module);
				}
			}

			if let ASTNode::Block(elems) = fn_block {
				result.generate_block(elems, module);
			}

			result
		} else {
			panic!()
		}
	}

	fn write(&mut self, stmt: CIRStmt) {
		self.blocks[self.current_block].push(stmt)
	}

	fn append_block(&mut self) -> BlockIndex {
		self.blocks.push(vec![]);
		self.current_block = self.blocks.len() - 1;
		self.current_block
	}

	fn generate_block(&mut self, block: &Vec<ASTElem>, module: &mut CIRModule) -> BlockIndex {
		self.append_block();

		for elem in block {
			match &elem.node {
				ASTNode::Block(elems) => {
					self.generate_block(elems, module);
					self.append_block();
				}

				ASTNode::Expression(expr) => {
					let expr_ir = self.generate_expr(&expr.borrow(), module);
					self.write(CIRStmt::Expression(expr_ir));
				}

				ASTNode::Declaration(ty, name, elem) => elem
					.as_ref()
					.and_then(|elem| Some(self.generate_decl(ty, name.clone(), elem, module)))
					.unwrap(),

				ASTNode::ControlFlow(ctrl) => match &**ctrl {
					ControlFlow::Return { expr } => {
						if let Some(expr) = expr {
							let expr_ir = self.generate_expr(&expr.get_expr().borrow(), module);
							self.write(CIRStmt::Return(Some(expr_ir)));
						} else {
							self.write(CIRStmt::Return(None));
						}
					}

					ControlFlow::If {
						cond,
						body,
						else_body,
					} => {
						let cond_ir = self.generate_expr(&cond.get_expr().borrow(), module);
						let start_block = self.current_block;
						let if_block = if let ASTNode::Block(elems) = &body.node {
							self.generate_block(elems, module)
						} else {
							panic!()
						};

						if let Some(else_body) = else_body {
							let else_block = if let ASTNode::Block(elems) = &else_body.node {
								self.generate_block(elems, module)
							} else {
								panic!()
							};
							let cont_block = self.append_block();

							self.current_block = start_block;
							self.write(CIRStmt::Branch(cond_ir, if_block, else_block));

							self.blocks[if_block].push(CIRStmt::Jump(cont_block));
							self.blocks[else_block].push(CIRStmt::Jump(cont_block));
							self.current_block = cont_block;
						} else {
							let cont_block = self.append_block();

							self.current_block = start_block;
							self.write(CIRStmt::Branch(cond_ir, if_block, cont_block));

							self.blocks[if_block].push(CIRStmt::Jump(cont_block));
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
							self.generate_block(elems, module)
						} else {
							panic!()
						};

						// Write jump-to-cond to body block
						self.write(CIRStmt::Jump(cond_block));
						
						let next_block = self.append_block();

						self.current_block = cond_block;
						let cond_ir = self.generate_expr(&cond.get_expr().borrow(), module);
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
							if let ASTNode::Declaration(ty, name, Some(elem)) = &init.node {
								self.generate_decl(ty, name.clone(), elem, module);
							}
						}

						let loop_block = self.append_block();
						self.current_block = start_block;
						self.write(CIRStmt::Jump(loop_block));
						
						// Generate body
						let body_block = if let ASTNode::Block(elems) = &body.node {
							self.generate_block(elems, module)
						} else {
							panic!()
						};

						// Add iter statement to body
						if let Some(iter) = iter {
							let iter_ir = self.generate_expr(&iter.get_expr().borrow(), module);
							self.write(CIRStmt::Expression(iter_ir));
						}

						// Write jump-to-loop to body block
						self.write(CIRStmt::Jump(loop_block));
						
						let next_block = self.append_block();
						self.current_block = loop_block;

						if let Some(cond) = cond {
							let cond_ir = self.generate_expr(&cond.get_expr().borrow(), module);
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

		self.current_block
	}

	fn generate_decl(
		&mut self,
		ty: &Type,
		name: String,
		elem: &Box<ASTElem>,
		module: &mut CIRModule,
	) {
		let cir_ty = module.convert_type(ty);

		let rval = self.generate_expr(&elem.get_expr().borrow(), module);

		self.variables.push((cir_ty, Some(name.clone())));
		self.name_map.insert(name.clone(), self.variables.len() - 1);

		let lval = LValue {
			local: self.variables.len() - 1,
			projection: vec![],
		};

		self.write(CIRStmt::Assignment(lval, rval))
	}

	fn generate_expr(&mut self, expr: &Expr, module: &mut CIRModule) -> RValue {
		match expr {
			Expr::Atom(atom, _) => match atom {
				Atom::IntegerLit(i, b) => {
					RValue::Atom(CIRType::Basic(b.unwrap()), None, Operand::IntegerLit(*i))
				}

				Atom::FloatLit(f, b) => {
					RValue::Atom(CIRType::Basic(b.unwrap()), None, Operand::FloatLit(*f))
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
					let cir_ty = module.convert_type(ty);
					let ty_idx = if let CIRType::TypeRef(idx) = cir_ty { idx } else { panic!() };

					let mut indices = vec![];

					if let CIRTypeDef::Algebraic { members_map, .. } = &module.types[ty_idx] {
						for elem in elems {
							indices.push(members_map[elem.0.as_ref().unwrap()]);
						}
					} else {
						panic!()
					}

					let tmp = self.insert_temporary(cir_ty.clone(), RValue::Atom(cir_ty.clone(), None, Operand::Undef));
					
					for i in 0..indices.len() {
						let mem_expr = self.generate_expr(&elems[i].1.borrow(), module);
						let mut mem_lval = tmp.clone(); 

						mem_lval.projection.push(PlaceElem::Field(indices[i]));
						
						self.write(CIRStmt::Assignment(mem_lval, mem_expr))
					}

					RValue::Atom(cir_ty, None, Operand::LValue(tmp))
				}

				Atom::Identifier(id) => {
					let idx = self.name_map[&id.expect_scopeless().unwrap()];
					let lval_ty = &self.variables[idx].0;
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
					let castee = self.generate_expr(&expr.get_expr().borrow(), module);
					let from = module.convert_type(expr.type_info.borrow().as_ref().unwrap());
					let to = module.convert_type(to);
					RValue::Cast {
						op: self.get_as_operand(from.clone(), castee),
						from,
						to,
					}
				}

				Atom::FnCall { name, args, ret } => {
					let cir_args = args
						.iter()
						.map(|arg| self.generate_expr(&arg.get_expr().borrow(), module))
						.collect();
					RValue::Atom(
						module.convert_type(ret.as_ref().unwrap()),
						None,
						Operand::FnCall(name.clone(), cir_args),
					)
				}
			},

			Expr::Cons(op, elems, _) => {
				if op.is_compound_assignment() {
					let op = op.get_compound_operator();
					let lval_ir = self.generate_lvalue_expr(&elems[0].0, module);
					let rval_ir = self.generate_expr(&elems[1].0, module);
					let l_ty = module.convert_type(elems[0].1.as_ref().unwrap());
					let r_ty = module.convert_type(elems[1].1.as_ref().unwrap());

					let r_tmp = self.get_as_operand(r_ty.clone(), rval_ir);

					let expr = RValue::Cons(
						[
							(l_ty.clone(), Operand::LValue(lval_ir.clone())),
							(r_ty.clone(), r_tmp)
						],
						op
					);

					let expr_tmp = self.get_as_operand(l_ty.clone(), expr);
					self.write(CIRStmt::Assignment(lval_ir.clone(), RValue::Atom(r_ty, None, expr_tmp)));

					RValue::Atom(l_ty, None, Operand::LValue(lval_ir))
				} else {
					if elems.len() == 1 {
						let sub_expr = self.generate_expr(&elems[0].0, module);
						let cir_ty = module.convert_type(elems[0].1.as_ref().unwrap());
						let temp = self.get_as_operand(cir_ty.clone(), sub_expr);

						RValue::Atom(cir_ty, Some(op.clone()), temp)
					} else {
						match op {
							Operator::MemberAccess => {

								match &elems[1].0 {
									Expr::Atom(Atom::FnCall { name, args, .. }, _) => {
										let rhs_ty = module.convert_type(elems[1].1.as_ref().unwrap());

										let cir_args = args.iter().map(|arg| self.generate_expr(&arg.get_expr().borrow(), module)).collect();

										RValue::Atom(rhs_ty, None, Operand::FnCall(name.clone(), cir_args))
									}

									Expr::Atom(Atom::Identifier(_), _) => {
										let lval = self.generate_lvalue_expr(expr, module);
										let cir_ty = module.convert_type(elems[1].1.as_ref().unwrap());
										RValue::Atom(cir_ty, None, Operand::LValue(lval))
									}

									_ => panic!(),
								}

								
							}

							_ => {
								let lhs = self.generate_expr(&elems[0].0, module);
								let rhs = self.generate_expr(&elems[1].0, module);
								let lhs_ty = module.convert_type(elems[0].1.as_ref().unwrap());
								let rhs_ty = module.convert_type(elems[1].1.as_ref().unwrap());
								let lhs_tmp = self.get_as_operand(lhs_ty.clone(), lhs);
								let rhs_tmp = self.get_as_operand(rhs_ty.clone(), rhs);
								RValue::Cons(
									[
										(lhs_ty, lhs_tmp),
										(rhs_ty, rhs_tmp),
									],
									op.clone(),
								)
							}
						}
					}
				}
			}
		}
	}

	fn generate_lvalue_expr(&mut self, expr: &Expr, module: &mut CIRModule) -> LValue {
		match expr {
			Expr::Atom(atom, _) => match atom {
				Atom::Identifier(id) => LValue {
					local: *self.name_map.get(&id.expect_scopeless().unwrap()).unwrap(),
					projection: vec![],
				},

				_ => panic!(),
			},

			Expr::Cons(op, elems, _) => match op {
				Operator::MemberAccess => {
					let mut lhs = self.generate_lvalue_expr(&elems[0].0, module);
					let lhs_ty = module.convert_type(&elems[0].1.as_ref().unwrap());

					if let CIRType::TypeRef(id) = lhs_ty {
						if let CIRTypeDef::Algebraic { members_map, .. } = &module.types[id] {
							if let Expr::Atom(Atom::Identifier(id), _) = &elems[1].0 {
								let idx = members_map[&id.expect_scopeless().unwrap()];

								lhs.projection.push(PlaceElem::Field(idx));

								return lhs;
							}
						}
					}
					panic!()
				}

				Operator::Deref => {
					let mut derefee = self.generate_lvalue_expr(&elems[0].0, module);
					derefee.projection.push(PlaceElem::Deref);
					derefee
				}

				_ => panic!(),
			},
		}
	}

	fn insert_variable(&mut self, name: String, ty: Type, module: &mut CIRModule) {
		// TODO: Deal with shadowing and scopes
		self.variables.push((module.convert_type(&ty), Some(name.clone())));
		self.name_map.insert(name, self.variables.len() - 1);
	}

	fn get_as_operand(&mut self, ty: CIRType, rval: RValue) -> Operand {
		if let RValue::Atom(_, None, operand) = rval {
			return operand;
		} else {
			Operand::LValue(self.insert_temporary(ty, rval))
		}
	}

	fn insert_temporary(&mut self, ty: CIRType, rval: RValue) -> LValue {
		self.variables.push((ty.clone(), None));

		let lval = LValue {
			local: self.variables.len() - 1,
			projection: vec![],
		};

		self.write(CIRStmt::Assignment(lval.clone(), rval));

		lval
	}
}
