use std::{cell::RefCell, collections::HashMap};

use super::{types::{Type, InnerType, Basic, Typed}, CMNError, ASTResult, namespace::{Namespace, Identifier, ScopePath}, ast::{ASTElem, ASTNode, TokenData}, controlflow::ControlFlow, expression::{Expr, Operator, Atom}, lexer, errors::{CMNMessage, CMNWarning}};


// SEMANTIC ANALYSIS
// This module contains structs and impls related to AST checking, name resolution, and type validation.

#[derive(PartialEq, Clone, Debug)]
pub struct Attribute {
	pub name: String,
	pub args: Vec<ASTElem>,
}

pub fn get_attribute<'a>(attributes: &'a Vec<Attribute>, attr_name: &str) -> Option<&'a Attribute> {
	attributes.iter().find(|a| a.name == attr_name.to_string())
}


pub struct FnScope<'ctx> {
	context: &'ctx RefCell<Namespace>,
	parent: Option<&'ctx FnScope<'ctx>>,
	fn_return_type: Type,
	root_namespace: &'ctx RefCell<Namespace>,

	variables: HashMap<String, Type>
}


impl<'ctx> FnScope<'ctx> {

	pub fn from_parent(parent: &'ctx FnScope) -> Self {
		FnScope { 
			context: parent.context.clone(), 
			parent: Some(parent), 
			fn_return_type: parent.fn_return_type.clone(),
			root_namespace: parent.root_namespace, 
			variables: HashMap::new() 
		}
	}

	pub fn new(context: &'ctx RefCell<Namespace>, return_type: Type) -> Self {
		FnScope {
			context, 
			parent: None,
			fn_return_type: return_type,
			root_namespace: context,
			variables: HashMap::new(),
		}
	}


	pub fn find_symbol(&self, id: &Identifier) -> Option<(String, Type)> {
		let mut result = None;
		if id.path.scopes.is_empty() {
			// Unqualified name, perform scope-level lookup first
			let local_lookup;
			
			if self.variables.contains_key(&id.name) {
				local_lookup = Some((id.name.clone(), self.variables.get(&id.name).cloned().unwrap()));
			} else if let Some(parent) = self.parent {
				local_lookup = parent.find_symbol(id);
			} else {
				local_lookup = None;
			}

			if local_lookup.is_some() {
				// Identifier refers to a non-namespace variable, so resolve it to the plain name
				result = local_lookup;
			}
		}
		
		if result.is_none() {
			// Oh boy it's name resolution time
			
			// Traverse the namespace tree, from either our current namespace or root
			let root;
			if id.path.absolute {
				root = &self.root_namespace;
			} else {
				root = &self.context;
			}

			let mut namespace : &Namespace = &root.borrow();
			for sub_ns in &id.path.scopes {
				let child = namespace.parsed_children.get(sub_ns);
				if let Some(child) = child {
					namespace = child;
				} else {
					return None; // TODO: Return a Result instead
				}
			}

			match namespace.get_symbol(&id.name) {
				Some((t, _, a)) => result = Some((namespace.get_mangled_name(&id.name, a), t.clone())),
				None => result = None,
			}
		}

		return result;
	}
	pub fn get_identifier_type(&self, id: &Identifier) -> Option<Type> {
		if let Some(result) = self.find_symbol(id) {
			Some(result.1)
		} else {
			None
		}
	}

	pub fn resolve_identifier(&self, id: &mut Identifier) -> Option<Type> {
		if let Some(find_result) = self.find_symbol(id) {
			id.resolved = Some(find_result.0);
			Some(find_result.1.clone())
		} else {
			None
		}
	}

	// Make this a parse-time thing
	pub fn resolve_type(&self, id: &mut Identifier) -> Option<Type> {		
		// Oh boy it's name resolution time again
		
		// Traverse the namespace tree, from either our current namespace or root
		let root;
		if id.path.absolute {
			root = &self.root_namespace;
		} else {
			root = &self.context;
		}

		let mut namespace : &Namespace = &root.borrow();
		for sub_ns in &id.path.scopes {
			let child = namespace.parsed_children.get(sub_ns);
			if let Some(child) = child {
				namespace = child;
			} else {
				return None; // TODO: Return a Result instead
			}
		}

		// Found the namespace, resolve the name
		let name = &id.name;

		if let Some(s) = namespace.get_type(name) {
			id.resolved = Some("mangled here lol".to_string());
			Some(s.clone())
		} else {
			None
		}
	
	}

	pub fn add_variable(&mut self, t: Type, n: String) {
		self.variables.insert(n, t);
	}
}



pub fn parse_namespace(namespace: &RefCell<Namespace>) -> ASTResult<()> {
	for child in namespace.borrow_mut().parsed_children.iter_mut() {
		let hack = RefCell::new(std::mem::take(child.1));
		parse_namespace(&hack)?;
		*child.1 = hack.into_inner();
	}

	for (_sym_name, (sym_type, sym_elem, _)) in &namespace.borrow().symbols {
		let mut scope = FnScope::new(namespace, sym_type.clone());

		let ret;
		if let InnerType::Function(fn_ret, args) = &sym_type.inner {
			ret = fn_ret.as_ref().clone();
			for arg in args.iter() {
				scope.add_variable(arg.0.as_ref().clone(), arg.1.clone().unwrap())
			}
			
		} else { 
			panic!()
		}

		
		if let Some(elem) = sym_elem {
			
			// Validate function block & get return type, make sure it matches the signature
			let void = Type::from_basic(Basic::VOID);
			let ret_type = elem.validate(&mut scope, &ret)?;
			
			if ret_type.is_none() && ret.inner != void.inner {
				// No returns in non-void function
				return Err((CMNError::ReturnTypeMismatch { expected: ret.clone(), got: void }, elem.token_data));
			} else if ret_type.is_some() && !ret_type.as_ref().unwrap().castable_to(&ret) {
				return Err((CMNError::ReturnTypeMismatch { expected: ret.clone(), got: ret_type.unwrap() }, elem.token_data));
			}
		}

	}
	Ok(())
}







impl ASTElem {
	// Recursively validate ASTNode types and check if blocks have matching return types
	pub fn validate(&self, scope: &mut FnScope, ret: &Type) -> ASTResult<Option<Type>> {
		let result = match &self.node {

			ASTNode::Block(elems) => {
				let mut subscope = FnScope::from_parent(scope);
				let mut last_ret = None;

				for elem in elems {
					let t = elem.validate(&mut subscope, ret)?;

					if let Some(t) = t {
						// Only compare against return type for control flow nodes
						if let ASTNode::ControlFlow(_) = elem.node {
							//if !t.coercable_to(ret) {
							//	return Err((CMNError::TypeMismatch(t, ret.clone()), elem.token_data))
							//}
							last_ret = Some(t);
						}
					}
				}
				Ok(last_ret)
			},
			
			ASTNode::Expression(e) => Ok(Some(e.borrow_mut().validate(scope, None, self.token_data)?)),
			
			ASTNode::Declaration(t, n, e) => {

				if let Some(expr) = e {
					expr.type_info.replace(Some(t.clone()));
					let expr_type = expr.get_type(scope)?;
					if expr_type != *t {
						if expr.get_expr().borrow().coercable_to(&expr_type, t, scope) {
							expr.wrap_expr_in_cast(Some(expr_type), t.clone());
						} else {
							return Err((CMNError::AssignTypeMismatch(expr_type, t.clone()), self.token_data));
						}
					}
				}

				scope.add_variable(t.clone(), n.to_string());

				Ok(None)	
			},

			ASTNode::ControlFlow(ctrl) => match ctrl.as_ref() {

				ControlFlow::If { cond, body, else_body } => {
					cond.type_info.replace(Some(Type::from_basic(Basic::BOOL)));
					let cond_type = cond.get_type(scope)?;
					let bool_t = Type::from_basic(Basic::BOOL);

					if !cond_type.castable_to(&bool_t) {
						return Err((CMNError::InvalidCast{ from: cond_type, to: bool_t}, self.token_data));
					}

					cond.wrap_expr_in_cast(Some(cond_type), bool_t);

					let t = body.validate(scope, ret)?;

					if let Some(else_body) = else_body {
						else_body.validate(scope, ret)?;
					}

					Ok(t)
				}

				ControlFlow::While { cond, body } => {
					cond.type_info.replace(Some(Type::from_basic(Basic::BOOL)));
					let cond_type = cond.get_type(scope)?;
					let bool_t = Type::from_basic(Basic::BOOL);

					if !cond_type.castable_to(&bool_t) {
						return Err((CMNError::InvalidCast{ from: cond_type, to: bool_t}, self.token_data));
					}

					cond.wrap_expr_in_cast(Some(cond_type), bool_t);

					let t = body.validate(scope, ret)?;
					Ok(t)
				} 

				ControlFlow::For { cond, body, init, iter } => {
					let mut subscope = FnScope::from_parent(&scope);	

					if let Some(init) = init { init.validate(&mut subscope, ret)?; }

					// Check if condition is coercable to bool
					if let Some(cond) = cond {
						let bool_t = Type::from_basic(Basic::BOOL);
						
						let cond_type = cond.get_type(&mut subscope)?;
						
						if !cond_type.castable_to(&bool_t) {
							return Err((CMNError::InvalidCast{ from: cond_type, to: bool_t }, cond.token_data));
						}
						
						cond.wrap_expr_in_cast(Some(cond_type), bool_t);
					}
					
					if let Some(iter) = iter { iter.validate(&mut subscope, ret)?; }

					let t = body.validate(&mut subscope, ret)?;
					if t.is_some() {
						Ok(t)
					} else {
						Ok(None)
					}
				}

				ControlFlow::Return { expr } => {
					if let Some(expr) = expr {
						let t = expr.validate(scope, ret)?;

						if let Some(t) = t {
							if t == *ret {
								Ok(Some(t))
							} else if expr.get_expr().borrow().coercable_to(&t, ret, scope) {
								expr.wrap_expr_in_cast(Some(t), ret.clone());
								Ok(Some(ret.clone()))
							} else {
								Err((CMNError::ReturnTypeMismatch { expected: ret.clone(), got: t }, self.token_data))
							}
						} else {
							Ok(None)
						}
					} else {
						Ok(Some(Type::from_basic(Basic::VOID))) // Return with no expression is of type void 
					}
				
				}
				
				_ => Ok(None)
			},
		};

		match result {
			Ok(ref r) => self.type_info.replace(r.clone()),
			Err(e) => return Err(e),
		};
		result
	}
}





impl Expr {
	pub fn create_cast(expr: Expr, from: Option<Type>, to: Type, meta: TokenData) -> Expr {
		Expr::Atom(Atom::Cast(Box::new(
			ASTElem { 
				node: ASTNode::Expression(RefCell::new(expr)), 
				type_info: RefCell::new(from), 
				token_data: meta
			}), 
			to.clone()
		), meta)
	}

	pub fn validate<'ctx>(&mut self, scope: &'ctx FnScope<'ctx>, goal_t: Option<&Type>, meta: TokenData) -> ASTResult<Type> {

		// Validate Atom or sub-expressions
		match self {

			Expr::Atom(a, _) => a.validate(scope, goal_t, meta),

			Expr::Cons(op, elems, meta) => {
				match op {
					// Special cases for member access and scope resolution
					Operator::MemberAccess => {
						let meta = meta.clone();
						self.get_lvalue_type(scope, meta).ok_or((CMNError::ExpectedIdentifier, meta))
					}

					// General case for unary & binary expressions
					_ => {
						let first = elems.get_mut(0).unwrap();
						let first_t = first.0.validate(scope, None, first.1)?;
						let mut second_t = None;

						if let Some(item) = elems.get_mut(1) {
							second_t = Some(item.0.validate(scope, None, item.1)?);

							if first_t != *second_t.as_ref().unwrap() {
								return Err((CMNError::ExprTypeMismatch(first_t, second_t.unwrap(), op.clone()), *meta))
							}
						}

						// Handle operators that change the expression's type here
						match op {
							Operator::Ref => Ok(first_t.ptr_type()),

							Operator::Deref => {
								match first_t.inner {
									InnerType::Pointer(t) => Ok(*t.clone()),
									_ => return Err((CMNError::NonPtrDeref, *meta)),
								}
							}

							_ => Ok(second_t.unwrap())
						}
					}
				}
			}
		}
	}

	// Check whether an Expr is coercable to a type

	pub fn coercable_to(&self, from: &Type, target: &Type, scope: &FnScope) -> bool {
		match self {
			Expr::Atom(a, _) => {
				match a {

					Atom::IntegerLit(_, t) | Atom::FloatLit(_, t) => {
						if t.is_some() {
							*target == Type::from_basic(t.unwrap())
						} else {
							target.is_numeric() 
						}
					},

					Atom::BoolLit(_) => target.is_boolean(),

					Atom::StringLit(_) => {
						if let InnerType::Pointer(other_p) = &target.inner {
							if let InnerType::Basic(other_b) = other_p.inner {
								if let Basic::CHAR = other_b {
									return true;
								} 
							}
						}

						false
					},
					
					Atom::Identifier(i) => scope.get_identifier_type(i).unwrap() == *target,
					Atom::FnCall { name, args: _ } => match scope.find_symbol(name).unwrap().1.inner {
						InnerType::Function(ret, _) => *ret == *target,
						_ => panic!(),
					},

					Atom::Cast(_, cast_t) => *target == *cast_t,
					Atom::ArrayLit(_) => todo!(),

					Atom::Dummy => true,
				}
			},

			Expr::Cons(_, _, _) => from == target,
		}
	}


	pub fn get_lvalue_type<'ctx>(&mut self, scope: &'ctx FnScope<'ctx>, meta: TokenData) -> Option<Type> {
		match self {
			Expr::Atom(a, _) => a.get_lvalue_type(scope),
			Expr::Cons(op, elems, _) => {
				// Only these operators can result in lvalues
				match op {

					Operator::Deref => {
						match elems[0].0.validate(scope, None, meta).unwrap().inner {
							InnerType::Pointer(t) => Some(*t),
							_ => None,
						}
					}

					Operator::MemberAccess => {
						if let Expr::Atom(Atom::Identifier(ref id), _) = elems[1].0 {
							let id = id.clone();
							match elems[0].0.validate(scope, None, meta).unwrap().inner {
								InnerType::Aggregate(t) => Some(t.members.iter().find(|mem| mem.0 == id.name).unwrap().1.0.clone()),
								_ => None,
							}
						} else {
							None
						}
					}

					_ => None,
				}
			},
		}
	}
}




impl Atom {
	pub fn validate<'ctx>(&mut self, scope: &'ctx FnScope<'ctx>, goal_t: Option<&Type>, meta: TokenData) -> ASTResult<Type> {
		match self {
			Atom::IntegerLit(_, t) =>
				if let Some(t) = t { 
					Ok(Type::from_basic(t.clone())) 
				} else {
					if goal_t.is_some() && goal_t.unwrap().is_integral() { 
						Ok(goal_t.unwrap().clone()) 
					} else { 
						Ok(Type::from_basic(Basic::I32)) 
					}
				},
			
			Atom::FloatLit(_, t) => if let Some(t) = t { 
				Ok(Type::from_basic(t.clone())) 
			} else {
				if goal_t.is_some() && goal_t.unwrap().is_floating_point() { 
					Ok(goal_t.unwrap().clone()) 
				} else { 
					Ok(Type::from_basic(Basic::F32)) 
				}
			},

			Atom::BoolLit(_) => Ok(Type::from_basic(Basic::BOOL)),
			Atom::StringLit(_) => Ok(Type::from_basic(Basic::STR)),

			Atom::Identifier(name) => scope.resolve_identifier(name).ok_or((CMNError::UndeclaredIdentifier(name.to_string()), meta)),
			
			Atom::Cast(a, t) => {
				if let ASTNode::Expression(expr) = &a.node {
					let a_t = expr.borrow_mut().validate(scope, None, meta)?;

					if a_t.castable_to(t) {
						if let Expr::Atom(a, _) = &mut *expr.borrow_mut() {
							a.check_cast(&a_t, t, scope, &meta)?;
						}

						a.type_info.replace(Some(t.clone()));
						Ok(t.clone())
					} else {
						Err((CMNError::InvalidCast{ from: a_t, to: t.clone()}, meta))
					}
				} else { 
					panic!(); 
				}
			},

			Atom::FnCall { name, args } => {
				
				if let Some(t) = scope.resolve_identifier(name) {
					if let InnerType::Function(ret, params) = t.inner {

						// Identifier is a function, check parameter types
						if args.len() == params.len() {

							for i in 0..args.len() {
								args[i].type_info.replace(Some(*params[i].0.clone()));
								let arg_type = args[i].get_expr().borrow_mut().validate(scope, None, meta)?;

								if !args[i].get_expr().borrow().coercable_to(&arg_type, params[i].0.as_ref(), scope) {
									return Err((CMNError::InvalidCoercion{ from: arg_type, to: params[i].0.as_ref().clone()}, args[i].token_data));
								}

								if arg_type != *params[i].0 {
									args[i].wrap_expr_in_cast(Some(arg_type), *params[i].0.clone());
								}
							}
							// All good, return function's return type
							Ok(*ret.clone())

						} else {
							Err((CMNError::ParamCountMismatch{expected: params.len(), got: args.len()}, meta))
						}
						
					} else {
						Err((CMNError::NotCallable(name.to_string()), meta)) // Trying to call a non-function
					}

				} else {
					Err((CMNError::UndeclaredIdentifier(name.to_string()), meta)) // Couldn't find symbol!
				}
			},

			Atom::ArrayLit(_) => todo!(),

			Atom::Dummy => panic!(),
		}
	}


	// Check if we should issue any warnings or errors when casting
	pub fn check_cast(&mut self, from: &Type, to: &Type, scope: &FnScope, meta: &TokenData) -> ASTResult<()> {
		match &from.inner {

			InnerType::Basic(b) => match b {

				Basic::STR => {
					if let Atom::StringLit(s) = self {
						if s.chars().last() != Some('\0') {
							s.push('\0');
							lexer::log_msg_at(meta.0, meta.1, CMNMessage::Warning(CMNWarning::CharPtrNoNull));
						}
					}

					Ok(())
				},

				_ => Ok(())
			},

			InnerType::Alias(_, t) => {
				self.check_cast(t.as_ref(), to, scope, meta)
			},
			
			InnerType::Aggregate(_) => todo!(),
			InnerType::Pointer(_) => todo!(),
			InnerType::Function(_, _) => todo!(),
			InnerType::Unresolved(_) => todo!(),
		}
	}



	pub fn get_lvalue_type<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> Option<Type> {
		match self {
			Atom::Identifier(id) => match scope.find_symbol(id){
				Some((_, t)) => Some(t),
				None => None,
			},
			_ => None,
		}
	}
}
