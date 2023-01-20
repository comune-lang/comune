use std::{
	cell::RefCell,
	collections::{HashMap, HashSet},
	fmt::{Debug, Display},
	hash::Hash,
	sync::{Arc, RwLock},
};

use crate::{
	errors::{CMNError, CMNErrorCode},
	parser::ParseResult,
};

use super::{
	expression::Expr,
	traits::{TraitDef, TraitRef, TraitSolver},
	types::{Basic, FnDef, Type, TypeDef, TypeRef},
	Attribute,
};

// String plays nicer with debuggers
#[cfg(debug_assertions)]
pub type Name = String;
#[cfg(not(debug_assertions))]
pub type Name = Arc<str>;

#[derive(Default, Debug, Clone, PartialEq, Eq, Hash)]
pub struct Identifier {
	pub qualifier: (Option<Box<Type>>, Option<Box<ItemRef<TraitRef>>>),
	pub path: Vec<Name>,
	pub absolute: bool,
}

unsafe impl Send for Identifier {} // Because of the fuckin RefCells deep in the TraitRef
unsafe impl Sync for Identifier {}

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

	pub fn expect_scopeless(&self) -> ParseResult<&Name> {
		if self.path.len() == 1 && !self.absolute {
			Ok(self.path.last().unwrap())
		} else {
			Err(CMNError::new(CMNErrorCode::ExpectedIdentifier)) // TODO: Give appropriate error
		}
	}
}

impl Display for Identifier {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut result = String::new();

		if !self.absolute {
			result.push('~');
		}

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
pub enum NamespaceASTElem {
	Parsed(Expr),
	Unparsed(usize), // Token index
	NoElem,
}

pub type FnOverloadList = Vec<(Arc<RwLock<FnDef>>, RefCell<NamespaceASTElem>)>;

#[derive(Clone, Debug)]
pub enum NamespaceItem {
	Type(Arc<RwLock<TypeDef>>),
	Trait(Arc<RwLock<TraitDef>>),
	// Plural in order to support function overloads
	Functions(FnOverloadList),
	Variable(Type, RefCell<NamespaceASTElem>),
	Alias(Identifier),
}

pub type NamespaceEntry = (NamespaceItem, Vec<Attribute>, Option<String>); // Option<String> is the item's mangled name

#[derive(Default, Clone, Debug)]
pub struct Namespace {
	pub path: Identifier,
	pub referenced_modules: HashSet<Identifier>,
	pub imported: HashMap<Identifier, Namespace>,
	pub children: HashMap<Identifier, NamespaceEntry>,
	//pub impls: HashMap<Identifier, HashMap<Name, FnOverloadList>>, // Impls defined in this namespace
	//pub trait_impls: HashMap<Identifier, HashMap<Identifier, Impl>>,
	pub trait_solver: TraitSolver,
}

#[derive(Clone)]
pub enum ItemRef<T: Clone> {
	Unresolved { name: Identifier, scope: Identifier, type_args: Vec<Type> },
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
					type_args: l2,
				},
				Self::Unresolved {
					name: r0,
					scope: r1,
					type_args: r2,
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
			Self::Unresolved { name, scope, type_args } => {
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
				type_args: arg2,
			} => f.debug_tuple("Unresolved").field(arg0).field(arg1).field(arg2).finish(),
			Self::Resolved(arg0) => f.debug_tuple("Resolved").field(arg0).finish(),
		}
	}
}

impl Namespace {
	pub fn new(path: Identifier) -> Self {
		Namespace {
			// Initialize root namespace with basic types
			path,
			children: HashMap::new(),
			referenced_modules: HashSet::new(),
			imported: HashMap::new(),
			trait_solver: TraitSolver::new(),
		}
	}

	pub fn get_interface(&self) -> Self {
		self.clone() // TODO: Actually implement
	}

	pub fn get_item(&self, id: &Identifier) -> Option<&NamespaceItem> {
		assert!(id.absolute, "argument to get_item should be absolute!");

		match self.children.get(id) {
			Some((NamespaceItem::Alias(alias), ..)) => self.get_item(alias),

			Some((item, ..)) => Some(item),

			None => {
				if let Some(import) = self
					.imported
					.get(&Identifier::from_name(id.path[0].clone(), true))
				{
					if id.path.len() > 1 {
						let mut id_sub = id.clone();
						id_sub.path.remove(0);

						return import.get_item(&id_sub);
					}
				}

				None
			}
		}
	}

	pub fn resolve_type(
		&self,
		id: &Identifier,
		scope: &Identifier,
		type_args: &Vec<(Name, Type)>,
	) -> Option<Type> {
		if !id.is_qualified() && type_args.is_empty() {
			if let Some(basic) = Basic::get_basic_type(id.name()) {
				return Some(Type::Basic(basic));
			}
		}

		let mut found = None;

		if !id.absolute {
			let mut scope_unwind = scope.clone();

			loop {
				let mut scope_combined = scope_unwind.clone();
				scope_combined.path.append(&mut id.clone().path);

				if let Some((item, ..)) = self.children.get(&scope_combined) {
					found = Some((scope_combined, item));
					break;
				}

				scope_unwind.path.pop();

				if scope_unwind.path.is_empty() {
					break;
				}
			}
		} else if let Some((item, ..)) = self.children.get(id) {
			found = Some((id.clone(), item));
		}

		match found {
			Some((id, NamespaceItem::Type(ty))) => {
				Some(Type::TypeRef(ItemRef::Resolved(TypeRef {
					def: Arc::downgrade(ty),
					name: id,
					args: vec![],
				})))
			}

			Some((_, NamespaceItem::Alias(alias))) => {
				self.resolve_type(alias, &Identifier::new(true), type_args)
			}

			_ => {
				if let Some(imported) = self
					.imported
					.get(&Identifier::from_name(id.path[0].clone(), true))
				{
					let mut id_sub = id.clone();
					id_sub.path.remove(0);

					imported.resolve_type(&id_sub, &Identifier::new(true), type_args)
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
		mut closure: impl FnMut(&NamespaceEntry, &Identifier) -> Ret,
	) -> Option<Ret> {
		if !id.absolute {
			let mut scope_unwind = scope.clone();

			// We "unwind" the scope, iterating through parent scopes and looking for a match
			while !scope_unwind.path.is_empty() {
				let mut scope_combined = scope_unwind.clone();
				scope_combined.path.append(&mut id.clone().path);

				if let Some(found_item) = self.children.get(&scope_combined) {
					if let (NamespaceItem::Alias(alias), ..) = found_item {
						return self.with_item(alias, scope, closure);
					} else {
						return Some(closure(found_item, &scope_combined));
					}
				}

				scope_unwind.path.remove(scope_unwind.path.len() - 2);
			}

			// Didn't find it, fall back to absolute lookup below
		}

		let mut id = id.clone();
		id.absolute = true;

		if let Some(absolute_lookup) = self.children.get(&id) {
			// Found a match for the absolute path in this namespace!

			if let (NamespaceItem::Alias(alias), ..) = absolute_lookup {
				self.with_item(alias, scope, closure)
			} else {
				Some(closure(absolute_lookup, &id))
			}
		} else if let Some(imported) = self.imported.iter().find(|(item, _imported)| {
			id.path.len() > item.path.len() && &id.path[0..item.path.len()] == item.path.as_slice()
		}) {
			// Found an imported namespace that's a prefix of `id`!
			// TODO: Figure out how this works for submodules
			let mut id_relative = id.clone();
			id_relative.path = id_relative.path[imported.0.path.len()..].to_vec();

			imported.1.with_item(&id_relative, scope, closure)
		} else {
			// Nada
			None
		}
	}
}

impl Display for Namespace {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		for (name, (item, _, _)) in &self.children {
			match item {
				NamespaceItem::Alias(id) => writeln!(f, "\t[alias] {}", id)?,
				NamespaceItem::Type(t) => writeln!(f, "\t[type] {}: {}", name, t.read().unwrap())?,
				NamespaceItem::Trait(t) => {
					writeln!(f, "\t[trait] {}: {:?}", name, t.read().unwrap())?
				}

				NamespaceItem::Functions(fs) => {
					for (t, _) in fs {
						writeln!(f, "\t[func] {}: {}", name, t.read().unwrap())?
					}
				}

				NamespaceItem::Variable(_, _) => todo!(),
			}
		}
		Ok(())
	}
}
