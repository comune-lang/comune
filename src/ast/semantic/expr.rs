use std::sync::{Arc, RwLock};

use crate::{
	ast::types::Type,
	ast::{
		controlflow::ControlFlow,
		expression::{Atom, Expr, FnRef, NodeData, Operator, XtorKind},
		module::{Identifier, Name},
		pattern::Binding,
		statement::Stmt,
		types::{Basic, BindingProps, FloatSize, IntSize, TupleKind, PtrKind},
		FnScope,
	},
	constexpr::{ConstExpr, ConstValue},
	errors::{ComuneErrCode, ComuneError},
	lexer::SrcSpan,
	parser::ComuneResult,
};

use super::func::{self, resolve_method_call, validate_fn_call, validate_arg_list};

impl Expr {
	pub fn create_cast(expr: Expr, to: Type, meta: NodeData) -> Expr {
		Expr::Atom(Atom::Cast(Box::new(expr), to), meta)
	}

	pub fn validate<'ctx>(&mut self, scope: &mut FnScope<'ctx>) -> ComuneResult<Type> {
		let result = match self {
			Expr::Atom(a, meta) => a.validate(scope, meta),

			Expr::Cons([lhs, rhs], op, meta) => {
				match op {
					// Special cases for type-asymmetric operators
					Operator::MemberAccess => {
						let ty = Self::validate_member_access(lhs, rhs, scope, meta)?;

						if matches!(&**rhs, Expr::Atom(Atom::FnCall { .. }, _)) {
							*self = *rhs.clone();
						}

						Ok(ty)
					}

					Operator::Subscr => {
						let idx_type = Type::isize_type(false);

						let first_t = lhs.validate(scope)?;
						let second_t = rhs.validate(scope)?;

						if let Type::Array(ty, _) = &first_t {
							if second_t != idx_type {
								if rhs.coercable_to(&idx_type, scope) {
									rhs.wrap_in_cast(idx_type);
								} else {
									return Err(ComuneError::new(
										ComuneErrCode::InvalidSubscriptRHS { t: second_t },
										meta.span,
									));
								}
							}

							Ok(*ty.clone())
						} else {
							Err(ComuneError::new(
								ComuneErrCode::InvalidSubscriptLHS { t: first_t },
								meta.span,
							))
						}
					}

					// General case for binary expressions
					_ => {
						let first_t = lhs.validate(scope)?;
						let second_t = rhs.validate(scope)?;

						match (&first_t, &op, &second_t) {
							(
								Type::Pointer { .. },
								Operator::Add | Operator::Sub,
								Type::Basic(Basic::Integral { .. }),
							) => Ok(first_t),

							_ => {
								if first_t != second_t {
									// Try to coerce one to the other

									if lhs.coercable_to(&second_t, scope) {
										lhs.wrap_in_cast(second_t.clone());
									} else if rhs.coercable_to(&first_t, scope) {
										rhs.wrap_in_cast(first_t.clone());
									} else {
										return Err(ComuneError::new(
											ComuneErrCode::ExprTypeMismatch(
												first_t,
												second_t,
												op.clone(),
											),
											meta.span,
										));
									}
								}

								// Handle operators that change the expression's type here
								match op {
									Operator::Eq
									| Operator::NotEq
									| Operator::Less
									| Operator::Greater
									| Operator::LessEq
									| Operator::GreaterEq => Ok(Type::bool_type()),

									Operator::Assign => Ok(Type::void_type()),
									_ if op.is_compound_assignment() => Ok(Type::void_type()),

									_ => Ok(second_t),
								}
							}
						}
					}
				}
			}

			Expr::Unary(expr, op, meta) => {
				let expr_ty = expr.validate(scope)?;

				match op {
					Operator::Ref => Ok(expr_ty.ptr_type(PtrKind::Shared)),
					Operator::RefMut => Ok(expr_ty.ptr_type(PtrKind::Unique)),
					Operator::RefRaw => Ok(expr_ty.ptr_type(PtrKind::Raw)),

					Operator::Deref => match expr_ty {
						Type::Pointer(pointee, kind) => {
							if kind == PtrKind::Raw && !scope.is_unsafe {
								return Err(ComuneError::new(
									ComuneErrCode::UnsafeOperation,
									meta.span,
								));
							}

							Ok(*pointee)
						}

						_ => Err(ComuneError::new(
							ComuneErrCode::InvalidDeref(expr_ty),
							meta.span,
						)),
					},

					_ => Ok(expr_ty),
				}
			}
		}?;

		result.validate(scope)?;

		self.set_type_hint(result.get_concrete_type(&scope.generics.get_as_arg_list()));

		Ok(result)
	}

	// Check whether an Expr is coercable to a type
	pub fn coercable_to(&self, target: &Type, scope: &FnScope) -> bool {
		match target {
			Type::Tuple(TupleKind::Sum, types) => {
				let tuple_matches = types
					.iter()
					.filter(|ty| self.coercable_to(ty, scope))
					.count();

				match tuple_matches {
					0 => false,
					1 => true,
					_ => false, // TODO: Error reporting for ambiguous tuple conversion
				}
			}

			_ => match self {
				Expr::Atom(a, _) => match a {
					Atom::IntegerLit(_, Some(t)) | Atom::FloatLit(_, Some(t)) => {
						*target == Type::Basic(*t)
					}

					Atom::IntegerLit(_, None) => target.is_integral(),
					Atom::FloatLit(_, None) => target.is_floating_point(),

					Atom::BoolLit(_) => target.is_boolean(),

					Atom::CStringLit(_) => {
						if let Type::Pointer(other_p, PtrKind::Shared) = &target {
							if **other_p == Type::i8_type(false) {
								return true;
							}
						}

						false
					}

					_ => self.get_type().is_subtype_of(target),
				},

				_ => self.get_type().is_subtype_of(target),
			},
		}
	}

	fn validate_member_access(
		lhs: &mut Expr,
		rhs: &mut Expr,
		scope: &mut FnScope,
		meta: &NodeData,
	) -> ComuneResult<Type> {
		lhs.validate(scope)?;
		
		match rhs {
			// Member access
			Expr::Atom(Atom::Identifier(id), _) => {
				let Type::TypeRef { def, args } = lhs.get_type() else {
					return Err(ComuneError::new(ComuneErrCode::InvalidSubscriptLHS { t: lhs.get_type().clone() }, meta.span));
				};
		
				let def = def.upgrade().unwrap();
				let def = def.read().unwrap();

				if let Some(m) = def.get_member_type(id.name(), &args) {
					rhs.set_type_hint(m.clone());

					Ok(m)
				} else {
					Err(ComuneError::new(
						ComuneErrCode::InvalidMemberAccess {
							t: lhs.get_type().clone(),
							idx: id.name().to_string(),
						},
						rhs.get_node_data().span,
					))
				}
			}

			// Method call
			// jesse. we have to call METHods
			Expr::Atom(call @ Atom::FnCall { .. }, meta) => {
				let ret = resolve_method_call(lhs.get_type(), lhs, call, scope, meta.span)?;
				rhs.set_type_hint(ret.clone());

				Ok(ret)
			}

			_ => panic!(),
		}
	}
}

impl Atom {
	pub fn validate<'ctx>(
		&mut self,
		scope: &mut FnScope<'ctx>,
		meta: &NodeData,
	) -> ComuneResult<Type> {
		match self {
			Atom::IntegerLit(_, t) => {
				if let Some(t) = t {
					Ok(Type::Basic(*t))
				} else if let Some(Type::Basic(Basic::Integral { .. })) = meta.ty {
					Ok(meta.ty.as_ref().unwrap().clone())
				} else {
					Ok(Type::i32_type(true))
				}
			}

			Atom::FloatLit(_, t) => {
				if let Some(t) = t {
					Ok(Type::Basic(*t))
				} else if let Some(Type::Basic(Basic::Float { .. })) = meta.ty {
					Ok(meta.ty.as_ref().unwrap().clone())
				} else {
					*t = Some(Basic::Float {
						size: FloatSize::F32,
					});
					Ok(Type::Basic(t.unwrap()))
				}
			}

			Atom::BoolLit(_) => Ok(Type::Basic(Basic::Bool)),

			Atom::StringLit(_) => Ok(Type::Slice(Box::new(Type::i8_type(false)))),

			Atom::CStringLit(_) => Ok(Type::Pointer(
				Box::new(Type::i8_type(false)),
				PtrKind::Shared,
			)),

			Atom::Identifier(name) => {
				if let Some((id, ty)) = scope.find_symbol(name, true) {
					// Replace name with fully-qualified ID
					*name = id;
					Ok(ty)
				} else {
					Err(ComuneError::new(
						ComuneErrCode::UndeclaredIdentifier(name.to_string()),
						meta.span,
					))
				}
			}

			Atom::Cast(expr, to) => {
				let expr_t = expr.validate(scope)?;

				if expr_t.castable_to(to) {
					Ok(to.clone())
				} else {
					Err(ComuneError::new(
						ComuneErrCode::CastTypeMismatch {
							from: expr_t,
							to: to.clone(),
						},
						expr.get_node_data().span,
					))
				}
			}

			Atom::FnCall { .. } => validate_fn_call(self, scope, meta),

			Atom::ArrayLit(elems) => {
				let array_len = Arc::new(RwLock::new(ConstExpr::Result(ConstValue::Integral(
					elems.len() as i128,
					Some(Basic::Integral {
						signed: false,
						size: IntSize::IAddr,
					}),
				))));

				match &meta.ty {
					Some(Type::Array(ty, _)) => {
						for elem in elems {
							elem.set_type_hint(*ty.clone());
							elem.validate(scope)?;
						}

						Ok(Type::Array(ty.clone(), array_len))
					}

					_ => {
						let mut last_ty = None;

						for elem in elems {
							let current_ty = elem.validate(scope)?;

							if let Some(last_ty) = &last_ty {
								if &current_ty != last_ty {
									todo!()
								}
							} else {
								last_ty = Some(current_ty.clone());
							}
						}
						if let Some(ty) = &meta.ty {
							// Type hint is not an array type
							Err(ComuneError::new(
								ComuneErrCode::AssignTypeMismatch {
									expr: Type::Array(Box::new(last_ty.unwrap()), array_len),
									to: ty.clone(),
								},
								meta.span,
							))
						} else {
							Ok(Type::Array(Box::new(last_ty.unwrap()), array_len))
						}
					}
				}
			}

			Atom::Constructor {
				def: def_weak,
				kind,
				generic_args,
				placement,
			} => {
				let def = def_weak.upgrade().unwrap();
				let def = def.read().unwrap();

				let ty = Type::TypeRef {
					def: def_weak.clone(),
					args: generic_args.clone(),
				};

				if let Some(placement) = placement {
					// If this is a placement-new expression, check if the
					// location exists and matches our type.
					let placement_ty = placement.validate(scope)?;

					if placement_ty != ty {
						return Err(ComuneError::new(
							ComuneErrCode::AssignTypeMismatch {
								expr: placement_ty,
								to: ty,
							},
							placement.get_span(),
						));
					}
				}

				match kind {
					XtorKind::Literal { fields } => {
						// Constructor literal

						for (name, expr) in fields.iter_mut() {
							let Some(member_ty) = def.get_member_type(name, generic_args) else {
								// Invalid member in strenum literal
								todo!()
							};

							expr.set_type_hint(member_ty.clone());

							let expr_ty = expr.validate(scope)?;

							if !expr.coercable_to(&member_ty, scope) {
								return Err(ComuneError::new(
									ComuneErrCode::AssignTypeMismatch {
										expr: expr_ty,
										to: member_ty,
									},
									expr.get_node_data().span,
								));
							}
						}

						let mut missing_members = vec![];

						for (member, ..) in &def.members {
							if !fields.iter().any(|(m, _)| member == m) {
								missing_members.push(member.clone());
							}
						}

						if !missing_members.is_empty() {
							return Err(ComuneError::new(
								ComuneErrCode::MissingInitializers {
									ty: ty.clone(),
									members: missing_members,
								},
								meta.span,
							));
						}
					}

					XtorKind::Constructor { args, resolved } => {
						if let Some(placement) = placement {
							// Constructor call

							for arg in args.iter_mut() {
								arg.validate(scope)?;
							}

							if resolved == &FnRef::None {
								args.insert(0, *placement.clone());
							}

							let mut candidates: Vec<_> = def
								.init
								.iter()
								.filter(|init| func::is_candidate_viable(args, &generic_args, init))
								.cloned()
								.collect();

							let func = func::try_select_candidate(
								&def.name,
								args,
								generic_args,
								&mut candidates,
								meta.span,
								scope,
							)?;

							validate_arg_list(args, &func.params, generic_args, scope)?;

							*resolved = FnRef::Direct(func);
						} else {
							// Desugar `x = new T()` into `x = { T _tmp; new (_tmp) T(args); _tmp }`

							let tmp_id: Name = "_tmp".into();

							let block = Atom::Block {
								items: vec![
									// T tmp;
									Stmt::Decl(
										vec![(
											ty.clone(),
											tmp_id.clone(),
											BindingProps::mut_value(),
										)],
										None,
										SrcSpan::new(),
									),
									// new (tmp) T(args);
									Stmt::Expr(Expr::Atom(
										Atom::Constructor {
											def: def_weak.clone(),
											generic_args: std::mem::take(generic_args),
											kind: std::mem::replace(
												kind,
												XtorKind::Literal { fields: vec![] },
											),
											placement: Some(Box::new(Expr::Atom(
												Atom::Identifier(Identifier::from_name(
													tmp_id.clone(),
													false,
												)),
												NodeData::new(),
											))),
										},
										NodeData::new(),
									)),
								],

								result: Some(Box::new(Expr::Atom(
									Atom::Identifier(Identifier::from_name(tmp_id.clone(), false)),
									NodeData::new(),
								))),

								is_unsafe: false,
							};

							// re-validate, now with the desugared placement-new form
							*self = block;
							return self.validate(scope, meta);
						}
					}
				}

				if let Some(placement) = placement {
					if !ty.is_subtype_of(placement.get_type()) {
						return Err(ComuneError::new(
							ComuneErrCode::AssignTypeMismatch {
								expr: ty,
								to: placement.get_type().clone(),
							},
							meta.span,
						));
					}

					// Placement-new does not return the constructed value,
					// so we return void as the type here
					Ok(Type::void_type())
				} else {
					// Not a placement-new expr, just return the type
					Ok(ty)
				}
			}

			Atom::Drop(dropped) => {
				dropped.validate(scope)?;
				Ok(Type::void_type())
			}

			Atom::Block {
				items,
				result,
				is_unsafe,
			} => {
				let mut subscope = FnScope::from_parent(scope, false, *is_unsafe);
				let mut is_never = false;

				for item in items {
					let ty = item.validate(&mut subscope)?;
					if ty.is_never() {
						is_never = true;
					}
				}

				if is_never {
					if let Some(result) = result {
						result.validate(&mut subscope)?;
					}

					Ok(Type::Never)
				} else {
					if let Some(result) = result {
						result.validate(&mut subscope)
					} else {
						Ok(Type::void_type())
					}
				}
				
			}

			Atom::CtrlFlow(ctrl) => match &mut **ctrl {
				ControlFlow::If {
					cond,
					body,
					else_body,
				} => {
					let mut subscope = FnScope::from_parent(scope, false, false);

					cond.validate(&mut subscope)?;
					cond.try_wrap_in_cast(Type::bool_type())?;

					let body_ty = body.validate(&mut subscope)?;

					if let Some(else_body) = else_body {
						let else_ty = else_body.validate(&mut subscope)?;

						if body_ty == else_ty {
							Ok(body_ty)
						} else {
							Ok(Type::common_type([&body_ty, &else_ty]))
						}
					} else {
						Ok(Type::void_type())
					}
				}

				ControlFlow::While { cond, body } => {
					let mut subscope = FnScope::from_parent(scope, true, false);

					cond.validate(&mut subscope)?;
					cond.try_wrap_in_cast(Type::bool_type())?;

					body.validate(&mut subscope)
				}

				ControlFlow::For {
					init,
					cond,
					iter,
					body,
				} => {
					let mut subscope = FnScope::from_parent(scope, true, false);

					if let Some(init) = init {
						init.validate(&mut subscope)?;
					}

					if let Some(cond) = cond {
						cond.validate(&mut subscope)?;
						cond.try_wrap_in_cast(Type::bool_type())?;
					}

					if let Some(iter) = iter {
						iter.validate(&mut subscope)?;
					}

					body.validate(&mut subscope)
				}

				ControlFlow::Return { expr: Some(expr) } => {
					let expr_ty = expr.validate(scope)?;

					if expr_ty == scope.ret.1 {
						Ok(Type::Never)
					} else if expr.coercable_to(&scope.ret.1, scope) {
						expr.wrap_in_cast(scope.ret.1.clone());
						Ok(Type::Never)
					} else {
						Err(ComuneError::new(
							ComuneErrCode::ReturnTypeMismatch {
								expected: scope.ret.1.clone(),
								got: expr_ty,
							},
							meta.span,
						))
					}
				}

				ControlFlow::Return { expr: None } => {
					if scope.ret.1.is_void() {
						Ok(Type::Never)
					} else {
						Err(ComuneError::new(
							ComuneErrCode::ReturnTypeMismatch {
								expected: scope.ret.1.clone(),
								got: Type::void_type(),
							},
							meta.span,
						))
					}
				}

				ControlFlow::Break | ControlFlow::Continue => {
					if scope.is_inside_loop {
						Ok(Type::Never)
					} else {
						Err(ComuneError::new(
							ComuneErrCode::LoopCtrlOutsideLoop(if **ctrl == ControlFlow::Break {
								"break"
							} else {
								"continue"
							}),
							meta.span,
						))
					}
				}

				ControlFlow::Match {
					scrutinee,
					branches,
				} => {
					if branches.is_empty() {
						return Ok(Type::void_type());
					}

					let scrutinee_type = scrutinee.validate(scope)?;
					let mut branch_types = vec![];

					for branch in branches {
						let mut subscope = FnScope::from_parent(scope, false, false);

						for binding in branch.0.get_bindings() {
							if let Binding {
								name: Some(name),
								ty,
								props,
							} = binding
							{
								subscope.add_variable(ty.clone(), name.clone(), *props);
							}
						}

						branch_types.push(branch.1.validate(&mut subscope)?);

						branch.1.wrap_in_block();

						if !branch.0.get_type().is_subtype_of(&scrutinee_type) {
							return Err(ComuneError::new(
								ComuneErrCode::MatchTypeMismatch {
									scrutinee: scrutinee_type,
									branch: branch.0.get_type().clone(),
								},
								branch.1.get_span(),
							));
						}
					}

					Ok(Type::common_type(&branch_types))
				}
			},
		}
	}
}
