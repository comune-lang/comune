use std::sync::{Arc, RwLock};

use crate::{
	ast::types::Type,
	ast::{
		controlflow::ControlFlow,
		expression::{Atom, Expr, FnRef, NodeData, Operator, XtorKind},
		pattern::Binding,
		types::{Basic, TupleKind},
		FnScope,
	},
	constexpr::{ConstExpr, ConstValue},
	errors::{ComuneErrCode, ComuneError},
	parser::ComuneResult,
};

use super::func::{resolve_method_call, validate_fn_call};

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
						let lhs_ty = lhs.validate(scope)?;
						Self::validate_member_access(&lhs_ty, lhs, rhs, scope, meta)
					}

					Operator::Subscr => {
						let idx_type = Type::Basic(Basic::PtrSizeInt { signed: false });

						let first_t = lhs.validate(scope)?;
						let second_t = rhs.validate(scope)?;

						if let Type::Array(ty, _) = &first_t {
							if second_t != idx_type {
								if rhs.coercable_to(&second_t, &idx_type, scope) {
									rhs.wrap_in_cast(idx_type);
								} else {
									return Err(ComuneError::new(
										ComuneErrCode::InvalidSubscriptRHS { t: second_t },
										meta.tk,
									));
								}
							}

							Ok(*ty.clone())
						} else {
							Err(ComuneError::new(
								ComuneErrCode::InvalidSubscriptLHS { t: first_t },
								meta.tk,
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
								Type::Basic(Basic::Integral { .. } | Basic::PtrSizeInt { .. }),
							) => Ok(first_t),

							_ => {
								if first_t != second_t {
									// Try to coerce one to the other

									if lhs.coercable_to(&first_t, &second_t, scope) {
										lhs.wrap_in_cast(second_t.clone());
									} else if rhs.coercable_to(&second_t, &first_t, scope) {
										rhs.wrap_in_cast(first_t.clone());
									} else {
										return Err(ComuneError::new(
											ComuneErrCode::ExprTypeMismatch(
												first_t,
												second_t,
												op.clone(),
											),
											meta.tk,
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

									Operator::PostDec | Operator::PostInc => Ok(first_t),

									Operator::Assign | _ if op.is_compound_assignment() => {
										Ok(Type::void_type())
									}

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
					Operator::Ref => Ok(expr_ty.ptr_type(true)),

					Operator::Deref => match expr_ty {
						Type::Pointer { pointee, .. } => {
							if !scope.is_unsafe {
								return Err(ComuneError::new(
									ComuneErrCode::UnsafeOperation,
									meta.tk,
								));
							}

							Ok(*pointee)
						}

						_ => Err(ComuneError::new(
							ComuneErrCode::InvalidDeref(expr_ty),
							meta.tk,
						)),
					},

					_ => Ok(expr_ty),
				}
			}
		}?;

		result.validate(scope)?;

		self.get_node_data_mut().ty.replace(result.clone());

		Ok(result)
	}

	// Check whether an Expr is coercable to a type
	pub fn coercable_to(&self, from: &Type, target: &Type, scope: &FnScope) -> bool {
		match target {
			Type::Tuple(TupleKind::Sum, types) => {
				let tuple_matches = types
					.iter()
					.filter(|ty| self.coercable_to(from, ty, scope))
					.count();

				match tuple_matches {
					0 => false,
					1 => true,
					_ => false, // TODO: Error reporting for ambiguous tuple conversion
				}
			}

			_ => match self {
				Expr::Atom(a, _) => match a {
					Atom::IntegerLit(_, t) => {
						if t.is_some() {
							*target == Type::Basic(t.unwrap())
						} else {
							target.is_integral()
						}
					}

					Atom::FloatLit(_, t) => {
						if t.is_some() {
							*target == Type::Basic(t.unwrap())
						} else {
							target.is_floating_point()
						}
					}

					Atom::BoolLit(_) => target.is_boolean(),

					Atom::CStringLit(_) => {
						if let Type::Pointer { pointee: other_p, mutable: false } = &target {
							if **other_p == Type::i8_type(false) {
								return true;
							}
						}

						false
					}

					Atom::FnCall { resolved, .. } => {
						if let FnRef::Direct(resolved) = resolved {
							resolved.read().unwrap().ret.1 == *target
						} else if let FnRef::Indirect(expr) = resolved {
							let Some(Type::Function(ret, _)) = &expr.get_node_data().ty else {
								panic!()
							};

							&**ret == target
						} else {
							false
						}
					}

					Atom::Cast(_, cast_t) => target == cast_t,

					_ => from == target,
				},

				_ => from == target,
			},
		}
	}

	fn validate_member_access(
		lhs_ty: &Type,
		lhs: &Expr,
		rhs: &mut Expr,
		scope: &mut FnScope,
		meta: &NodeData,
	) -> ComuneResult<Type> {
		let Type::TypeRef { def: lhs_def, args: lhs_args } = lhs_ty else {
			return Err(ComuneError::new(ComuneErrCode::InvalidSubscriptLHS { t: lhs_ty.clone() }, meta.tk));
		};
		let lhs_def = lhs_def.upgrade().unwrap();
		let lhs_def = lhs_def.read().unwrap();

		match rhs {
			// Member access
			Expr::Atom(Atom::Identifier(id), _) => {
				if let Some((_, m)) = lhs_def.get_member(id.name(), Some(lhs_args)) {
					rhs.get_node_data_mut().ty = Some(m.clone());

					Ok(m)
				} else {
					Err(ComuneError::new(
						ComuneErrCode::InvalidMemberAccess {
							t: lhs_ty.clone(),
							idx: id.name().to_string(),
						},
						rhs.get_node_data().tk,
					))
				}
			}

			// Method call
			// jesse. we have to call METHods
			Expr::Atom(Atom::FnCall { .. }, _) => {
				let Expr::Atom(rhs_atom, ..) = rhs else { panic!() };
				let ret = resolve_method_call(lhs_ty, lhs, rhs_atom, scope)?;

				rhs.get_node_data_mut().ty = Some(ret.clone());

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
				} else if let Some(Type::Basic(_)) = meta.ty {
					Ok(meta.ty.as_ref().unwrap().clone())
				} else {
					Ok(Type::i32_type(true))
				}
			}

			Atom::FloatLit(_, t) => {
				if let Some(t) = t {
					Ok(Type::Basic(*t))
				} else if let Some(Type::Basic(b)) = meta.ty {
					*t = Some(b);
					Ok(meta.ty.as_ref().unwrap().clone())
				} else {
					*t = Some(Basic::Float { size_bytes: 4 });
					Ok(Type::Basic(t.unwrap()))
				}
			}

			Atom::BoolLit(_) => Ok(Type::Basic(Basic::Bool)),

			Atom::StringLit(_) => Ok(Type::Slice(Box::new(Type::i8_type(false)))),

			Atom::CStringLit(_) => Ok(Type::Pointer {
				pointee: Box::new(Type::i8_type(false)),
				mutable: false,
			}),

			Atom::Identifier(name) => {
				if let Some((id, ty)) = scope.find_symbol(name, true) {
					// Replace name with fully-qualified ID
					*name = id;
					Ok(ty)
				} else {
					Err(ComuneError::new(
						ComuneErrCode::UndeclaredIdentifier(name.to_string()),
						meta.tk,
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
						expr.get_node_data().tk,
					))
				}
			}

			Atom::FnCall { .. } => validate_fn_call(self, scope, meta),

			Atom::ArrayLit(elems) => {
				let array_len = Arc::new(RwLock::new(ConstExpr::Result(ConstValue::Integral(
					elems.len() as i128,
					Some(Basic::PtrSizeInt { signed: false }),
				))));

				match &meta.ty {
					Some(Type::Array(ty, _)) => {
						for elem in elems {
							elem.get_node_data_mut().ty = Some(*ty.clone());

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
								meta.tk,
							))
						} else {
							Ok(Type::Array(Box::new(last_ty.unwrap()), array_len))
						}
					}
				}
			}

			Atom::Constructor {
				def: def_weak,
				kind: XtorKind::Literal { fields },
				generic_args,
				placement,
			} => {
				let def = def_weak.upgrade().unwrap();
				let def = def.read().unwrap();

				for (name, expr) in fields.iter_mut() {
					let member_ty = if let Some((_, ty)) = def.get_member(name, Some(generic_args))
					{
						ty
					} else {
						// Invalid member in strenum literal
						todo!()
					};

					expr.get_node_data_mut().ty.replace(member_ty.clone());
					let expr_ty = expr.validate(scope)?;

					if !expr.coercable_to(&expr_ty, &member_ty, scope) {
						return Err(ComuneError::new(
							ComuneErrCode::AssignTypeMismatch {
								expr: expr_ty,
								to: member_ty,
							},
							expr.get_node_data().tk,
						));
					}
				}
				let mut missing_members = vec![];

				for (member, ..) in &def.members {
					if !fields.iter().any(|(m, _)| member == m) {
						missing_members.push(member.clone());
					}
				}

				let ty = Type::TypeRef {
					def: def_weak.clone(),
					args: generic_args.clone(),
				};

				if !missing_members.is_empty() {
					return Err(ComuneError::new(
						ComuneErrCode::MissingInitializers {
							ty: ty.clone(),
							members: missing_members,
						},
						meta.tk,
					));
				}

				if let Some(placement) = placement {
					// If this is a placement-new expression, check if the
					// location exists and matches our type.
					let place_ty = placement.validate(scope)?;

					if !ty.is_subtype_of(&place_ty) {
						return Err(ComuneError::new(
							ComuneErrCode::AssignTypeMismatch {
								expr: ty,
								to: place_ty,
							},
							meta.tk,
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

			Atom::Constructor { .. } => {
				todo!()
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

				for item in items {
					item.validate(&mut subscope)?;
				}

				if let Some(result) = result {
					result.validate(&mut subscope)
				} else {
					Ok(Type::void_type())
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
							todo!()
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

				ControlFlow::Return { expr } => {
					if let Some(expr) = expr {
						let expr_ty = expr.validate(scope)?;

						if expr_ty == scope.fn_return_type.1 {
							Ok(Type::Never)
						} else if expr.coercable_to(&expr_ty, &scope.fn_return_type.1, scope) {
							expr.wrap_in_cast(scope.fn_return_type.1.clone());
							Ok(Type::Never)
						} else {
							Err(ComuneError::new(
								ComuneErrCode::ReturnTypeMismatch {
									expected: scope.fn_return_type.1.clone(),
									got: expr_ty,
								},
								meta.tk,
							))
						}
					} else if scope.fn_return_type.1 == Type::void_type() {
						Ok(Type::Never)
					} else {
						Err(ComuneError::new(
							ComuneErrCode::ReturnTypeMismatch {
								expected: scope.fn_return_type.1.clone(),
								got: Type::void_type(),
							},
							meta.tk,
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
							meta.tk,
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

					let mut last_branch_type = None;
					let scrutinee_type = scrutinee.validate(scope)?;

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

						let branch_ty = branch.1.validate(&mut subscope)?;

						if let Some(last_branch_type) = last_branch_type {
							if branch_ty != last_branch_type {
								todo!()
							}
						}

						last_branch_type = Some(branch_ty);

						if !branch.0.get_type().is_subtype_of(&scrutinee_type) {
							todo!()
						}
					}

					Ok(last_branch_type.unwrap()) // TODO: This'll panic with an empty match expression
				}
			},
		}
	}
}
