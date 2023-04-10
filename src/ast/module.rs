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
	types::{Basic, FnPrototype, Type, TypeDef},
};

// String plays nicer with debuggers
#[cfg(debug_assertions)]
pub type Name = String;
#[cfg(not(debug_assertions))]
pub type Name = Arc<str>;

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
	pub path: Identifier,
	pub children: HashMap<Identifier, ModuleItemInterface>,
	pub import_names: HashSet<ModuleImportKind>,
	pub imported: HashMap<Name, ModuleImport>,
	pub impl_solver: ImplSolver,
	pub is_typed: bool,
}

// Struct representing a module's implementation.
// Using Vec because Arc<RwLock<T>> is not Hash for T: Hash, and
// i do not want to start doing newtype bullshit right now
// The Identifier here is the function's scope, for name resolution
#[derive(Default, Debug)]
pub struct ModuleImpl {
	pub fn_impls: Vec<(Arc<RwLock<FnPrototype>>, ModuleASTElem)>,
}

// I HATE RWLOCKS I HATE RWLOCKS I HATE RWLOCKS I HATE RWLOCKS I
#[derive(Clone, Debug)]
pub enum ModuleItemInterface {
	Type(Arc<RwLock<TypeDef>>),
	Trait(Arc<RwLock<TraitInterface>>),
	Functions(Vec<Arc<RwLock<FnPrototype>>>),
	Variable(Type),
	Alias(Identifier),
	TypeAlias(Arc<RwLock<Type>>),
}

#[derive(Clone, Debug)]
pub enum ModuleItemImpl {
	Function(Arc<RwLock<FnPrototype>>, ModuleASTElem),
	Variable(ModuleASTElem),
}

impl ModuleImpl {
	pub fn new() -> Self {
		ModuleImpl { fn_impls: vec![] }
	}
}

impl ModuleInterface {
	pub fn new(path: Identifier) -> Self {
		ModuleInterface {
			path,
			children: HashMap::new(),
			import_names: HashSet::from([ModuleImportKind::Language("core".into())]),
			imported: HashMap::new(),
			impl_solver: ImplSolver::new(),
			is_typed: false,
		}
	}

	pub fn get_external_interface(&self, require_typed: bool) -> Self {
		let result = ModuleInterface {
			path: self.path.clone(),
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
		if !id.is_qualified() {
			if let Some(basic) = Basic::get_basic_type(id.name()) {
				return Some(Type::Basic(basic));
			}
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

			Some((_, ModuleItemInterface::TypeAlias(alias))) => Some(alias.read().unwrap().clone()),

			_ => {
				if let Some(imported) = self.imported.get(&id.path[0]) {
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
	pub qualifier: (Option<Box<Type>>, Option<Box<ItemRef<TraitRef>>>),
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

	pub fn is_qualified(&self) -> bool {
		self.path.len() > 1
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
		let mut result = String::new();

		match &self.qualifier {
			(Some(ty), None) => result.push_str(&format!("{ty}::")),

			(Some(ty), Some(tr)) => {
				result.push('<');

				match &**tr {
					ItemRef::Resolved(tr) => {
						result.push_str(&format!("{ty} as {}", tr.name));
					}

					ItemRef::Unresolved { name, .. } => {
						result.push_str(&format!("{ty} as \"{name}\""));
					}
				}

				result.push_str(">::");
			}

			(None, Some(_)) => todo!(),

			(None, None) => {}
		}

		for scope in &self.path {
			result.push_str(scope);
			if scope != self.path.last().unwrap() {
				result.push_str("::");
			}
		}

		write!(f, "{result}")
	}
}

#[derive(Clone, Debug, PartialEq)]
pub enum ModuleASTElem {
	Parsed(Expr),
	Unparsed(TokenIndex),
	NoElem,
}

// This is old and unwieldy as hell and I gotta get around to removing it

#[derive(Clone)]
pub enum ItemRef<T: Clone> {
	Unresolved {
		name: Identifier,
		scope: Arc<Identifier>,
		generic_args: Vec<Type>,
	},
	Resolved(T),
}

impl<T: Clone> Eq for ItemRef<T> where T: PartialEq + Eq {}

impl<T: Clone> PartialEq for ItemRef<T>
where
	T: PartialEq,
{
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(
				Self::Unresolved {
					name: l0,
					scope: l1,
					generic_args: l2,
				},
				Self::Unresolved {
					name: r0,
					scope: r1,
					generic_args: r2,
				},
			) => l0 == r0 && l1 == r1 && l2 == r2,
			(Self::Resolved(l0), Self::Resolved(r0)) => l0 == r0,
			_ => false,
		}
	}
}

impl<T: Clone> Hash for ItemRef<T>
where
	T: Hash,
{
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		match self {
			Self::Unresolved {
				name,
				scope,
				generic_args: type_args,
			} => {
				name.hash(state);
				scope.hash(state);
				type_args.hash(state);
			}

			Self::Resolved(t) => t.hash(state),
		}
	}
}

impl<T: Clone> Debug for ItemRef<T>
where
	T: Debug,
{
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Unresolved {
				name: arg0,
				scope: arg1,
				generic_args: arg2,
			} => f
				.debug_tuple("Unresolved")
				.field(arg0)
				.field(arg1)
				.field(arg2)
				.finish(),
			Self::Resolved(arg0) => f.debug_tuple("Resolved").field(arg0).finish(),
		}
	}
}
