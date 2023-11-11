use itertools::Itertools;

use crate::{
	ast::{statement::Stmt, pattern::Pattern},
	errors::{ComuneErrCode, ComuneError},
	parser::ComuneResult, lexer::SrcSpan,
};

use crate::ast::{types::Type, FnScope};

impl Stmt {
	pub fn validate(&mut self, scope: &mut FnScope) -> ComuneResult<Type> {
		match self {
			Stmt::Decl(names, expr, span) => {
				if names.len() != 1 {
					todo!()
				}

				let (binding_ty, binding_name, binding_props) = &mut names[0];

				if let Some(expr) = expr {
					expr.set_type_hint(binding_ty.clone());

					let expr_ty = expr.validate(scope)?;
					
					binding_ty.resolve_inference_vars(expr_ty.clone(), binding_props.span)?;
					binding_ty.validate(scope, *span)?;

					if expr_ty != *binding_ty {
						if expr_ty.is_subtype_of(&binding_ty) {
							expr.wrap_in_cast(binding_ty.clone());
						} else {
							return Err(ComuneError::new(
								ComuneErrCode::AssignTypeMismatch {
									expr: expr_ty,
									to: binding_ty.clone(),
								},
								*span,
							));
						}
					}

					if binding_props.is_ref {
						return Err(ComuneError::new(
							ComuneErrCode::UnstableFeature("ref_locals"),
							*span,
						));
					}
				} else {
					binding_ty.validate(scope, *span)?;

					// References must be initialized in their declaration
					if binding_props.is_ref {
						return Err(ComuneError::new(ComuneErrCode::UninitReference, *span));
					}

					// new& is only allowed in function parameters
					if binding_props.is_new {
						return Err(ComuneError::new(ComuneErrCode::LocalNewReference, *span));
					}
				}
				
				scope.add_variable(binding_ty.clone(), binding_name.clone(), *binding_props);
				Ok(binding_ty.clone())
			}

			Stmt::Expr(expr) => expr.validate(scope),
		}
	}
}

impl Pattern {
	pub fn validate(&mut self, scope: &mut FnScope) -> ComuneResult<Type> {
		match self {
			Pattern::Binding(binding) => {
				binding.ty.validate(scope, binding.props.span)?;
				Ok(binding.ty.clone())
			}

			Pattern::Destructure { patterns, pattern_ty, exhaustive, span } => {
				let Type::TypeRef { def, .. } = pattern_ty else {
					return Err(ComuneError::new(ComuneErrCode::Other, SrcSpan::new()))
				};
				
				let def = def.upgrade().unwrap();
				let def = def.read().unwrap();
				let mut names = vec![];

				if *exhaustive { names.reserve(patterns.len()) }

				for pattern in patterns {
					pattern.1.validate(scope)?;
					
					if *exhaustive {
						names.push(pattern.0.clone())
					}

					// Check if name actually refers to a member
					if !def.members.iter().any(|(m, ..)| *m == pattern.0) {
						return Err(ComuneError::new(
							ComuneErrCode::InvalidMemberAccess { 
								t: pattern_ty.clone(), 
								idx: pattern.0.to_string()
							},
							*span
						));
					}
				}

				if *exhaustive {
					let mut members = def.members.iter().map(|(name, ..)| name.clone()).collect_vec();
					
					members.retain(|m| !names.contains(m));

					if !members.is_empty() {
						return Err(ComuneError::new(
							ComuneErrCode::DestructureNotExhaustive(members),
							*span
						))
					}
					
				}

				pattern_ty.validate(scope, *span)?;

				Ok(pattern_ty.clone())
			}

			_ => todo!(),
		}
	}
}