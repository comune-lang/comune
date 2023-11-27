use std::{
	collections::{HashMap, HashSet},
	fmt::{Debug, Display},
	hash::Hash,
	path::PathBuf,
	sync::{Arc, RwLock},
};

use crate::{
	errors::{ComuneErrCode, ComuneError},
	lexer::SrcSpan,
	parser::ComuneResult,
};

use super::{
	expression::Expr,
	traits::{ImplSolver, TraitInterface, TraitRef},
	types::{Basic, FnPrototype, Generics, Type, TypeDef}, semantic::ty::resolve_type,
};

#[derive(Clone, Hash, PartialEq, Eq, Debug)]
pub struct RawName<T: Clone + Hash + PartialEq + Eq + Debug + Display> {
	data: T,
}

impl<T> RawName<T>
where
	T: Clone + Hash + PartialEq + Eq + Debug + Display + AsRef<str>
{
	pub fn as_str(&self) -> &str {
		self.data.as_ref()
	}
}

impl<T> Display for RawName<T>
where
	T: Clone + Hash + PartialEq + Eq + Debug + Display
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.data)
	}
}

impl<T> From<&str> for RawName<T>
where
	T: Clone + Hash + PartialEq + Eq + Debug + Display + for<'a> From<&'a str>
{
	fn from(value: &str) -> Self {
		Self {
			data: value.into(),
		}
	}
}

impl<T> From<String> for RawName<T>
where
	T: Clone + Hash + PartialEq + Eq + Debug + Display + From<String>
{
	fn from(value: String) -> Self {
		Self {
			data: value.into()
		}
	}
}

// String plays nicer with debuggers
#[cfg(debug_assertions)]
pub type Name = RawName<String>;
#[cfg(not(debug_assertions))]
pub type Name = RawName<Arc<str>>;

pub type TokenIndex = usize;


#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum ModuleImportKind {
	Child(Name),
	Language(Name),
	Extern(Identifier),
}

#[derive(Debug, Clone)]
pub struct ModuleImport {
	pub interface: Arc<ModuleInterface>,
	pub import_kind: ModuleImportKind,
	pub path: PathBuf,
}

// The full module dependency system is complex, as the compiler is
// designed to have as few parallelization bottlenecks as possible.
// Rust's concurrency features may have driven me a bit mad with power.

// Struct representing a possibly-typechecked module interface. This
// stage of AST construction does not parse any function or
// expression bodies, only the prototypes of namespace items.
// This is quick to construct, and downstream modules depend on
// this stage for expression parsing.
#[derive(Default, Debug)]
pub struct ModuleInterface {
	pub name: Identifier,
	pub children: HashMap<Identifier, ModuleItemInterface>,
	pub import_names: HashSet<ModuleImportKind>,
	pub imported: HashMap<Name, ModuleImport>,
	pub impl_solver: ImplSolver,
	pub is_typed: bool,
}

// Struct representing a module's implementation.
#[derive(Default, Debug)]
pub struct ModuleImpl {
	pub fn_impls: HashMap<Arc<FnPrototype>, ModuleASTElem>,
}

// I HATE RWLOCKS I HATE RWLOCKS I HATE RWLOCKS I HATE RWLOCKS I
#[derive(Clone, Debug)]
pub enum ModuleItemInterface {
	Type(Arc<RwLock<TypeDef>>),
	Trait(Arc<RwLock<TraitInterface>>),
	Functions(Arc<RwLock<Vec<Arc<FnPrototype>>>>),
	Variable(Arc<RwLock<Type>>),
	Alias(Identifier),
	TypeAlias(Arc<RwLock<(Type, Generics)>>),
}

impl ModuleImpl {
	pub fn new() -> Self {
		ModuleImpl {
			fn_impls: HashMap::new(),
		}
	}
}

impl ModuleImportKind {
	pub fn get_import_identifier(&self, parent: &Identifier) -> Identifier {
		match self {
			ModuleImportKind::Child(name) => Identifier::from_parent(parent, name.clone()),
			ModuleImportKind::Language(name) => Identifier::from_name(name.clone(), true),
			ModuleImportKind::Extern(name) => name.clone(),
		}
	}
}

impl ModuleInterface {
	pub fn new(name: Identifier) -> Self {
		ModuleInterface {
			name,
			children: HashMap::new(),
			import_names: HashSet::new(),
			imported: HashMap::new(),
			impl_solver: ImplSolver::new(),
			is_typed: false,
		}
	}

	pub fn get_external_interface(&self, require_typed: bool) -> Self {
		let result = ModuleInterface {
			name: self.name.clone(),
			children: self.children.clone(),
			import_names: HashSet::new(),

			imported: self
				.imported
				.iter()
				.filter(|import| matches!(import.1.import_kind, ModuleImportKind::Child(_)))
				.map(|(k, v)| (k.clone(), v.clone()))
				.collect(),

			impl_solver: self.impl_solver.clone(),
			is_typed: self.is_typed,
		};

		if require_typed {
			for (_, import) in &result.imported {
				assert!(import.interface.is_typed);
			}
		}

		result
	}

	pub fn get_item<'a>(
		&'a self,
		id: &Identifier,
	) -> Option<(Identifier, &'a ModuleItemInterface)> {
		assert!(id.absolute, "argument to get_item should be absolute!");

		match self.children.get(id) {
			Some(ModuleItemInterface::Alias(alias)) => {
				let mut alias = alias.clone();
				alias.absolute = true;
				self.get_item(&alias)
			}

			Some(item) => Some((id.clone(), item)),

			None => {
				if let Some(import) = self.imported.get(&id.path[0]) {
					if id.path.len() > 1 {
						let mut id_sub = id.clone();
						id_sub.path.remove(0);

						return import.interface.get_item(&id_sub);
					}
				}

				None
			}
		}
	}

	pub fn resolve_type(&self, id: &Identifier, scope: &Identifier) -> Option<Type> {		
		if !id.is_scoped() {
			if let Some(basic) = Basic::get_basic_type(id.name().as_str()) {
				return Some(Type::Basic(basic));
			}

			if id.name().as_str() == "never" {
				return Some(Type::Never);
			}
		}

		if id.qualifier.0.is_some() {
			let qualif = id.qualifier.0.as_ref().map(|t| t.as_ref());

			let qualif = if let Some(Type::Unresolved { name, scope, .. }) = qualif {
				self.resolve_type(name, scope)?
			} else if let Some(ty @ Type::TypeRef { .. }) = qualif {
				ty.clone()
			} else {
				todo!()
			};

			let Type::TypeRef { def, .. } = qualif else {
				todo!()
			};

			let mut current_subty = def.upgrade().unwrap();

			for name in &id.path {
				let subty_guard = current_subty.read().unwrap();

				if let Some((_, subty)) = subty_guard
					.variants
					.iter()
					.find(|(variant, ..)| variant == name)
				{
					let subty = subty.clone();
					drop(subty_guard);
					current_subty = subty;
				} else {
					return None;
				}
			}

			return Some(Type::TypeRef {
				def: Arc::downgrade(&current_subty),
				args: vec![],
			});
		}

		let mut found = None;

		if !id.absolute {
			let mut scope_unwind = scope.clone();

			scope_unwind.qualifier = (None, None);

			loop {
				let mut scope_combined = scope_unwind.clone();
				scope_combined.path.append(&mut id.clone().path);

				if let Some(item) = self.children.get(&scope_combined) {
					found = Some((scope_combined, item));
					break;
				}

				if scope_unwind.path.is_empty() {
					break;
				}

				scope_unwind.path.pop();
			}
		} else if let Some(item) = self.children.get(id) {
			found = Some((id.clone(), item));
		}

		match found {
			Some((_, ModuleItemInterface::Type(ty))) => Some(Type::TypeRef {
				def: Arc::downgrade(ty),
				args: vec![],
			}),

			Some((_, ModuleItemInterface::Alias(alias))) => {
				self.resolve_type(alias, &Identifier::new(true))
			}

			Some((_, ModuleItemInterface::TypeAlias(alias))) => {
				let mut alias = alias.read().unwrap().clone();
				
				let Ok(()) = resolve_type(&mut alias.0, self, &alias.1) else {
					return None
				};

				Some(alias.0)
			}

			_ => {
				let id_root = Identifier::from_name(id.path[0].clone(), true);

				if let Some(child) = self.children.get(&id_root) {
					match child {
						ModuleItemInterface::Alias(alias) => {
							let mut alias_full = alias.clone();

							alias_full.path.extend(&mut id.path[1..].iter().cloned());

							self.resolve_type(&alias_full, &Identifier::new(true))
						}

						ModuleItemInterface::Type(ty) => {
							let mut current_subty = ty.clone();

							for name in &id.path[1..] {
								let subty_guard = current_subty.read().unwrap();

								if let Some((_, subty)) = subty_guard
									.variants
									.iter()
									.find(|(variant, ..)| variant == name)
								{
									let subty = subty.clone();
									drop(subty_guard);
									current_subty = subty;
								} else {
									return None;
								}
							}

							Some(Type::TypeRef {
								def: Arc::downgrade(&current_subty),
								args: vec![],
							})
						}

						_ => None,
					}
				} else if let Some(imported) = self.imported.get(&id.path[0]) {
					let mut id_sub = id.clone();
					id_sub.path.remove(0);

					imported
						.interface
						.resolve_type(&id_sub, &Identifier::new(true))
				} else {
					None
				}
			}
		}
	}

	pub fn with_item<Ret>(
		&self,
		id: &Identifier,
		scope: &Identifier,
		mut closure: impl FnMut(&ModuleItemInterface, &Identifier) -> Ret,
	) -> Option<Ret> {
		if !id.absolute {
			let mut scope_unwind = scope.clone();

			// We "unwind" the scope, iterating through parent scopes and looking for a match
			while !scope_unwind.path.is_empty() {
				let mut scope_combined = scope_unwind.clone();
				scope_combined.path.append(&mut id.clone().path);

				if let Some(found_item) = self.children.get(&scope_combined) {
					if let ModuleItemInterface::Alias(alias) = found_item {
						return self.with_item(alias, scope, closure);
					} else {
						return Some(closure(found_item, &scope_combined));
					}
				}

				scope_unwind.path.remove(scope_unwind.path.len() - 1);
			}

			// Didn't find it, fall back to absolute lookup below
		}

		let mut id = id.clone();
		id.absolute = true;

		if let Some(absolute_lookup) = self.children.get(&id) {
			// Found a match for the absolute path in this namespace!

			if let ModuleItemInterface::Alias(alias) = absolute_lookup {
				self.with_item(alias, scope, closure)
			} else {
				Some(closure(absolute_lookup, &id))
			}
		} else if let Some(imported) = self
			.imported
			.iter()
			.find(|(import_name, _)| &id.path[0] == *import_name)
		{
			// Found an imported namespace that's a prefix of `id`!
			// TODO: Figure out how this works for submodules
			let mut id_relative = id.clone();
			id_relative.path.remove(0);

			imported.1.interface.with_item(&id_relative, scope, closure)
		} else {
			// Nada
			None
		}
	}
}

#[derive(Default, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier {
	pub qualifier: (Option<Box<Type>>, Option<Box<TraitRef>>),
	pub path: Vec<Name>,
	pub absolute: bool,
}

impl Identifier {
	pub fn new(absolute: bool) -> Self {
		Identifier {
			qualifier: (None, None),
			path: vec![],
			absolute,
		}
	}

	pub fn from_name(name: Name, absolute: bool) -> Self {
		Identifier {
			qualifier: (None, None),
			path: vec![name],
			absolute,
		}
	}

	pub fn from_parent(parent: &Identifier, name: Name) -> Self {
		let mut result = parent.clone();
		result.path.push(name);
		result
	}

	pub fn name(&self) -> &Name {
		self.path.last().unwrap()
	}

	pub fn is_scoped(&self) -> bool {
		self.path.len() > 1
	}

	pub fn is_qualified(&self) -> bool {
		self.is_scoped() || self.qualifier.0.is_some() || self.qualifier.1.is_some()
	}

	pub fn expect_scopeless(&self) -> ComuneResult<&Name> {
		if self.path.len() == 1 && !self.absolute && matches!(&self.qualifier, (None, None)) {
			Ok(self.path.last().unwrap())
		} else {
			Err(ComuneError::new(
				ComuneErrCode::ExpectedIdentifier,
				SrcSpan::new(),
			)) // TODO: Give appropriate error
		}
	}
}

impl Display for Identifier {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self.qualifier {
			(Some(ty), None) => write!(f, "{ty}::")?,

			(Some(ty), Some(tr)) => {
				write!(f, "<")?;

				write!(f, "{ty} as {tr}")?;

				write!(f, ">::")?;
			}

			(None, Some(_)) => todo!(),

			(None, None) => {}
		};

		let mut iter = self.path.iter();

		write!(f, "{}", iter.next().unwrap())?;

		for scope in iter {
			write!(f, "::")?;
			write!(f, "{scope}")?;
		}

		Ok(())
	}
}

#[derive(Clone, Debug, PartialEq)]
pub enum ModuleASTElem {
	Parsed(Expr),
	Unparsed(TokenIndex),
	NoElem,
}