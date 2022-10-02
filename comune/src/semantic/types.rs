use std::cell::RefCell;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ptr;
use std::sync::{Arc, RwLock, Weak};

use super::namespace::{Identifier, Namespace, NamespaceEntry, NamespaceItem};
use crate::constexpr::ConstExpr;
use crate::parser::ASTResult;
use crate::semantic::FnScope;

pub type BoxedType = Box<Type>;
pub type FnParamList = Vec<(Type, Option<String>)>;

pub trait Typed {
	fn get_type<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> ASTResult<Type>;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Basic {
	INTEGRAL { signed: bool, size_bytes: u32 },
	SIZEINT { signed: bool },
	FLOAT { size_bytes: u32 },
	CHAR,
	BOOL,
	VOID,
	STR,
}

#[derive(Clone)]
pub enum Type {
	Basic(Basic),                               // Fundamental type
	Pointer(BoxedType),                         // Pointer-to-<BoxedType>
	Array(BoxedType, RefCell<Vec<ConstExpr>>),  // N-dimensional array with constant expression for size
	Unresolved(Identifier),                     // Unresolved type (during parsing phase)
	TypeRef(Weak<RwLock<TypeDef>>, Identifier), // Reference to type definition, plus Identifier for serialization
}

#[derive(Debug)]
pub enum TypeDef {
	Function(Type, Vec<(Type, Option<String>)>), // Return type + parameter types
	Algebraic(Box<AlgebraicType>),               // Data type for structs & enums
	                                             // TODO: Add Class TypeDef
}

// The internal representation of algebraic types, like structs, enums, and (shocker) struct enums
//
// Algebraics (strums?) can contain member variables, inner type aliases, variants (aka subtype definitions), etc...
// Hence we give them the same data structure as Namespaces, a list of `String`s and `NamespaceEntry`s
// However, since declaration order *is* meaningful in strums, we store them as a Vec, rather than a HashMap
#[derive(Clone, Debug)]
pub struct AlgebraicType {
	pub items: Vec<(String, NamespaceEntry, Visibility)>,
	pub layout: DataLayout,
}

#[derive(Clone, Debug)]
pub enum Visibility {
	Public,
	Private,
	Protected,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DataLayout {
	Declared,  // Layout is exactly as declared
	Optimized, // Layout may be shuffled to minimize padding
	Packed,    // Layout is packed in declaration order with no padding (inner alignment is 1 byte)
}

impl AlgebraicType {
	pub fn new() -> Self {
		AlgebraicType {
			items: vec![],
			layout: DataLayout::Declared,
		}
	}

	pub fn get_member(&self, name: &str) -> Option<(usize, &Type)> {
		let mut index = 0;

		for item in &self.items {
			if let NamespaceItem::Variable(t, _) = &item.1 .0 {
				if &item.0 == name {
					return Some((index, t));
				} else {
					index += 1;
				}
			}
		}
		None
	}

	pub fn with_item<Ret>(
		&self,
		name: &Identifier,
		parent: &Namespace,
		root: &Namespace,
		mut closure: impl FnMut(&NamespaceEntry, &Identifier) -> Ret,
	) -> Option<Ret> {
		if name.path.scopes.is_empty() {
			if let Some(item) = self.items.iter().find(|item| item.0 == name.name) {
				// It's one of this namespace's children!

				if let NamespaceItem::Alias(id) = &item.1 .0 {
					// It's an alias, so look up the actual item
					return parent.with_item(&id, root, closure);
				} else {
					// Generate absolute identifier
					let id = Identifier {
						name: name.name.clone(),
						path: parent.path.clone(),
						mem_idx: 0,
						resolved: None,
					};

					return Some(closure(&item.1, &id));
				}
			}
		} else {
			if let Some(item) = self.items.iter().find(|item| item.0 == name.path.scopes[0]) {
				match &item.1 .0 {
					NamespaceItem::Type(ty) => match &*ty.read().unwrap() {
						TypeDef::Algebraic(alg) => {
							let mut name_clone = name.clone();
							name_clone.path.scopes.remove(0);

							return alg.with_item(&name_clone, parent, root, closure);
						}

						_ => panic!(),
					},

					_ => panic!(), // TODO: Proper error
				}
			}
		}

		None
	}
}

impl Basic {
	pub fn get_basic_type(name: &str) -> Option<Self> {
		match name {
			"i64" => Some(Basic::INTEGRAL {
				signed: true,
				size_bytes: 8,
			}),
			"i32" | "int" => Some(Basic::INTEGRAL {
				signed: true,
				size_bytes: 4,
			}),
			"i16" => Some(Basic::INTEGRAL {
				signed: true,
				size_bytes: 2,
			}),
			"i8" => Some(Basic::INTEGRAL {
				signed: true,
				size_bytes: 1,
			}),

			"u64" => Some(Basic::INTEGRAL {
				signed: false,
				size_bytes: 8,
			}),
			"u32" | "uint" => Some(Basic::INTEGRAL {
				signed: false,
				size_bytes: 4,
			}),
			"u16" => Some(Basic::INTEGRAL {
				signed: false,
				size_bytes: 2,
			}),
			"u8" => Some(Basic::INTEGRAL {
				signed: false,
				size_bytes: 1,
			}),

			"isize" => Some(Basic::SIZEINT { signed: false }),
			"usize" => Some(Basic::SIZEINT { signed: false }),

			"f64" | "double" => Some(Basic::FLOAT { size_bytes: 8 }),
			"f32" | "float" => Some(Basic::FLOAT { size_bytes: 4 }),

			"char" => Some(Basic::CHAR),
			"str" => Some(Basic::STR),
			"bool" => Some(Basic::BOOL),
			"void" => Some(Basic::VOID),

			_ => None,
		}
	}

	pub fn as_str(&self) -> &'static str {
		match self {
			Basic::INTEGRAL { signed, size_bytes } => match size_bytes {
				8 => {
					if *signed {
						"i64"
					} else {
						"u64"
					}
				}
				4 => {
					if *signed {
						"i32"
					} else {
						"u32"
					}
				}
				2 => {
					if *signed {
						"i16"
					} else {
						"u16"
					}
				}
				1 => {
					if *signed {
						"i8"
					} else {
						"u8"
					}
				}
				_ => panic!(),
			},

			Basic::FLOAT { size_bytes } => {
				if *size_bytes == 8 {
					"f64"
				} else {
					"f32"
				}
			}
			Basic::SIZEINT { signed } => {
				if *signed {
					"isize"
				} else {
					"usize"
				}
			}

			Basic::CHAR => "char",
			Basic::STR => "str",
			Basic::BOOL => "bool",
			Basic::VOID => "void",
		}
	}

	pub fn is_numeric(&self) -> bool {
		self.is_integral() || self.is_floating_point()
	}

	pub fn is_integral(&self) -> bool {
		matches!(self, Basic::INTEGRAL { .. } | Basic::SIZEINT { .. })
	}

	pub fn is_signed(&self) -> bool {
		if let Basic::INTEGRAL { signed, .. } | Basic::SIZEINT { signed } = self {
			*signed
		} else {
			false
		}
	}

	pub fn is_boolean(&self) -> bool {
		matches!(self, Basic::BOOL)
	}

	pub fn is_floating_point(&self) -> bool {
		matches!(self, Basic::FLOAT { .. })
	}
}

impl Type {
	pub fn ptr_type(&self) -> Self {
		Type::Pointer(Box::new(self.clone()))
	}

	// Name mangling
	pub fn serialize(&self) -> String {
		let mut result = String::new();

		match &self {
			Type::Basic(b) => {
				// TODO: Shorten
				result.push_str(b.as_str());
			}

			Type::Array(t, _) => {
				result.push_str(&t.serialize());
				result.push_str("[]");
			}

			Type::Pointer(_) => {
				result.push_str("*");
			}

			Type::TypeRef(t, _) => {
				result.push_str(&t.upgrade().unwrap().as_ref().read().unwrap().serialize())
			}

			Type::Unresolved(_) => {
				panic!("Attempt to serialize an unresolved type!");
			}
		}
		// TODO: Generics

		result
	}

	pub fn castable_to(&self, target: &Type) -> bool {
		if *self == *target {
			true
		} else {
			if self.is_numeric() {
				return target.is_numeric() || target.is_boolean();
			}

			return false;
		}
	}

	// Convenience
	pub fn is_numeric(&self) -> bool {
		if let Type::Basic(b) = self {
			b.is_numeric()
		} else {
			false
		}
	}

	pub fn is_integral(&self) -> bool {
		if let Type::Basic(b) = self {
			b.is_integral()
		} else {
			false
		}
	}

	pub fn is_boolean(&self) -> bool {
		if let Type::Basic(b) = self {
			b.is_boolean()
		} else {
			false
		}
	}

	pub fn is_floating_point(&self) -> bool {
		if let Type::Basic(b) = self {
			b.is_floating_point()
		} else {
			false
		}
	}

	pub fn is_signed(&self) -> bool {
		if let Type::Basic(b) = self {
			b.is_signed()
		} else {
			false
		}
	}
}

impl TypeDef {
	pub fn serialize(&self) -> String {
		let mut result = String::new();
		match &self {
			TypeDef::Algebraic(a) => {
				for t in &a.items {
					match &t.1 .0 {
						NamespaceItem::Variable(t, _) => result.push_str(&t.serialize()),
						_ => todo!(),
					}
				}
			}

			TypeDef::Function(ret, args) => {
				result.push_str("?");
				for arg in args {
					result.push_str(&arg.0.serialize());
				}
				result.push_str("!");
				result.push_str(&ret.serialize());
			}
		}
		result
	}
}

impl Display for Basic {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.as_str())
	}
}

impl PartialEq for Type {
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(Self::Basic(l0), Self::Basic(r0)) => l0 == r0,
			(Self::Pointer(l0), Self::Pointer(r0)) => l0 == r0,
			(Self::Unresolved(l0), Self::Unresolved(r0)) => l0 == r0,
			(Self::TypeRef(l0, l1), Self::TypeRef(r0, r1)) => {
				Arc::ptr_eq(&l0.upgrade().unwrap(), &r0.upgrade().unwrap()) && l1 == r1
			}
			_ => false,
		}
	}
}

impl Eq for Type {}

impl Hash for Type {
	fn hash<H: Hasher>(&self, state: &mut H) {
		match self {
			Type::Basic(b) => b.hash(state),
			Type::Pointer(t) => {
				t.hash(state);
				"*".hash(state)
			}
			Type::Array(t, _s) => {
				t.hash(state);
				"+".hash(state)
			}
			Type::Unresolved(id) => id.hash(state),
			Type::TypeRef(r, _) => ptr::hash(r.upgrade().unwrap().as_ref(), state),
		}
	}
}

impl Display for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self {
			Type::Basic(t) => {
				write!(f, "{}", t)?;
			}

			Type::Pointer(t) => {
				write!(f, "{}*", t)?;
			}

			Type::Array(t, _s) => {
				write!(f, "{}[]", t)?;
			}

			Type::Unresolved(t) => {
				write!(f, "unresolved type \"{}\"", t)?;
			}

			Type::TypeRef(_, id) => {
				write!(f, "{}", id)?;
			}
		}

		Ok(())
	}
}

impl Display for TypeDef {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self {
			TypeDef::Algebraic(agg) => {
				write!(f, "{}", agg)?;
			}

			TypeDef::Function(ret, params) => {
				write!(f, "{}(", ret)?;
				for param in params {
					write!(f, "{}, ", param.0)?;
				}
				write!(f, ")")?;
			}
		}
		Ok(())
	}
}

impl Display for AlgebraicType {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut members = self.items.iter();

		write!(f, "Struct {{{:?}", members.next().unwrap().1 .0)?;

		for mem in members {
			write!(f, ", {:?}", mem.1 .0)?;
		}
		write!(f, "}}")
	}
}

impl Hash for AlgebraicType {
	fn hash<H: Hasher>(&self, state: &mut H) {
		// We hash based on Type only, so two aggregates with the same layout have the same Hash
		// Hashing is only relevant for LLVM codegen, so semantic analysis will already have happened
		//self.members.iter().map(|item| &item.1.0).collect::<Vec<&Type>>().hash(state);
		//self.variants.iter().map(|item| &item.1.0).collect::<Vec<&Box<AlgebraicType>>>().hash(state);
		//self.methods.iter().map(|item| &item.1.0).collect::<Vec<&Type>>().hash(state);
		for item in &self.items {
			match &item.1 .0 {
				NamespaceItem::Variable(t, _) => t.hash(state),
				_ => todo!(),
			}
		}
	}
}

impl std::fmt::Debug for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Basic(arg0) => f.debug_tuple("Basic").field(arg0).finish(),
			Self::Pointer(_) => f.debug_tuple("Pointer").finish(),
			Self::Array(t, _) => f.debug_tuple("Array").field(t).finish(),
			Self::Unresolved(arg0) => f.debug_tuple("Unresolved").field(arg0).finish(),
			Self::TypeRef(arg0, _) => f.debug_tuple("TypeRef").field(arg0).finish(),
		}
	}
}
