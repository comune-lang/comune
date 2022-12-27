use std::collections::HashSet;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ptr;
use std::sync::{Arc, RwLock, Weak};

use super::namespace::{Identifier, ItemRef, Name};
use super::traits::TraitRef;
use crate::constexpr::ConstExpr;

pub type BoxedType = Box<Type>;
pub type TypeParam = Vec<ItemRef<TraitRef>>; // Generic type parameter, with trait bounds
pub type TypeParamList = Vec<(Name, TypeParam)>;

#[derive(Clone)]
pub enum Type {
	Basic(Basic),                                  // Fundamental type
	Pointer(BoxedType),                            // Pointer-to-<BoxedType>
	Array(BoxedType, Arc<RwLock<Vec<ConstExpr>>>), // N-dimensional array with constant expression for size
	TypeRef(ItemRef<TypeRef>),                     // Reference to user-defined type
	TypeParam(usize),                              // Reference to an in-scope type parameter
	Tuple(TupleKind, Vec<Type>),                   // Sum/product tuple
	Never, // Return type of a function that never returns, coerces to anything
}

#[derive(Debug, Clone)]
pub struct FnParamList {
	pub params: Vec<(Type, Option<Name>)>,
	pub variadic: bool,
}

#[derive(Debug, Clone)]
pub struct FnDef {
	pub ret: Type,
	pub params: FnParamList,
	pub type_params: TypeParamList,
}

//#[derive(Debug, Clone, Hash)]
//pub enum TupleType {
//	Product(Vec<Type>),
//	Sum(Vec<Type>),
//}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum TupleKind {
	Product,
	Sum,
}
// The internal representation of algebraic types, like structs, enums, and (shocker) struct enums
//
// Algebraics (strums?) can contain member variables, inner type aliases, variants (aka subtype definitions), etc...
// Hence we give them the same data structure as Namespaces, a list of `String`s and `NamespaceEntry`s
// However, since declaration order *is* meaningful in strums, we store them as a Vec, rather than a HashMap
#[derive(Debug, Clone)]
pub struct AlgebraicDef {
	pub members: Vec<(Name, Type, Visibility)>,
	pub variants: Vec<(Name, AlgebraicDef)>,
	pub layout: DataLayout,
	pub params: TypeParamList,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Basic {
	Integral { signed: bool, size_bytes: u32 },
	PtrSizeInt { signed: bool },
	Float { size_bytes: u32 },
	Char,
	Bool,
	Void,
	Str,
}
#[derive(Clone)]
pub struct TypeRef {
	pub def: Weak<RwLock<TypeDef>>,
	pub name: Identifier,
	pub args: Vec<(Name, Type)>,
}

#[derive(Debug)]
pub enum TypeDef {
	Algebraic(AlgebraicDef),
	Class, // TODO: Implement classes
}

#[derive(Clone, Debug)]
pub enum Visibility {
	Public,
	Private,
	Protected,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum DataLayout {
	Declared,  // Layout is exactly as declared
	Optimized, // Layout may be shuffled to minimize padding
	Packed,    // Layout is packed in declaration order with no padding (inner alignment is 1 byte)
}

// Don't mutate TypeDefs through TypeRef or so help me god
unsafe impl Send for Type {}

impl AlgebraicDef {
	pub fn new() -> Self {
		AlgebraicDef {
			layout: DataLayout::Declared,
			members: vec![],
			variants: vec![],
			params: vec![],
		}
	}

	pub fn get_member(
		&self,
		name: &Name,
		type_args: Option<&Vec<(Name, Type)>>,
	) -> Option<(usize, Type)> {
		let mut index = 0;

		for (member_name, ty, _) in &self.members {
			if member_name == name {
				if let Some(type_args) = type_args {
					return Some((index, ty.get_concrete_type(type_args)));
				}
				return Some((index, ty.clone()));
			} else {
				index += 1;
			}
		}
		None
	}
}

impl Basic {
	pub fn get_basic_type(name: &str) -> Option<Self> {
		match name {
			"i64" => Some(Basic::Integral {
				signed: true,
				size_bytes: 8,
			}),
			"i32" | "int" => Some(Basic::Integral {
				signed: true,
				size_bytes: 4,
			}),
			"i16" => Some(Basic::Integral {
				signed: true,
				size_bytes: 2,
			}),
			"i8" => Some(Basic::Integral {
				signed: true,
				size_bytes: 1,
			}),
			"u64" => Some(Basic::Integral {
				signed: false,
				size_bytes: 8,
			}),
			"u32" | "uint" => Some(Basic::Integral {
				signed: false,
				size_bytes: 4,
			}),
			"u16" => Some(Basic::Integral {
				signed: false,
				size_bytes: 2,
			}),
			"u8" => Some(Basic::Integral {
				signed: false,
				size_bytes: 1,
			}),

			"isize" => Some(Basic::PtrSizeInt { signed: false }),
			"usize" => Some(Basic::PtrSizeInt { signed: false }),

			"f64" | "double" => Some(Basic::Float { size_bytes: 8 }),
			"f32" | "float" => Some(Basic::Float { size_bytes: 4 }),

			"char" => Some(Basic::Char),
			"str" => Some(Basic::Str),
			"bool" => Some(Basic::Bool),
			"void" => Some(Basic::Void),

			_ => None,
		}
	}

	pub fn as_str(&self) -> &'static str {
		match self {
			Basic::Integral { signed, size_bytes } => match size_bytes {
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

			Basic::Float { size_bytes } => {
				if *size_bytes == 8 {
					"f64"
				} else {
					"f32"
				}
			}
			Basic::PtrSizeInt { signed } => {
				if *signed {
					"isize"
				} else {
					"usize"
				}
			}

			Basic::Char => "char",
			Basic::Str => "str",
			Basic::Bool => "bool",
			Basic::Void => "void",
		}
	}

	pub fn is_numeric(&self) -> bool {
		self.is_integral() || self.is_floating_point()
	}

	pub fn is_integral(&self) -> bool {
		matches!(self, Basic::Integral { .. } | Basic::PtrSizeInt { .. })
	}

	pub fn is_signed(&self) -> bool {
		if let Basic::Integral { signed, .. } | Basic::PtrSizeInt { signed } = self {
			*signed
		} else {
			false
		}
	}

	pub fn is_boolean(&self) -> bool {
		matches!(self, Basic::Bool)
	}

	pub fn is_floating_point(&self) -> bool {
		matches!(self, Basic::Float { .. })
	}
}

impl Type {
	pub fn get_concrete_type(&self, type_args: &Vec<(Name, Type)>) -> Type {
		match self {
			Type::Basic(b) => Type::Basic(*b),
			Type::Pointer(ptr) => Type::Pointer(Box::new(ptr.get_concrete_type(type_args))),
			Type::Array(arr_ty, size) => {
				Type::Array(Box::new(arr_ty.get_concrete_type(type_args)), size.clone())
			}
			Type::TypeRef(ty) => Type::TypeRef(ty.clone()),
			Type::TypeParam(param) => type_args[*param].1.clone(),
			Type::Never => Type::Never,

			Type::Tuple(kind, types) => Type::Tuple(
				*kind,
				types
					.iter()
					.map(|ty| ty.get_concrete_type(type_args))
					.collect(),
			),
		}
	}

	pub fn ptr_type(&self) -> Self {
		Type::Pointer(Box::new(self.clone()))
	}

	pub fn castable_to(&self, target: &Type) -> bool {
		if self == target || self == &Type::Never {
			true
		} else if self.is_numeric() {
			target.is_numeric() || target.is_boolean()
		} else if matches!(self, Type::Pointer(_)) && matches!(target, Type::Pointer(_)) {
			true
		} else {
			false
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

	pub fn is_floating_point(&self) -> bool {
		if let Type::Basic(b) = self {
			b.is_floating_point()
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

	pub fn is_subtype_of(&self, other: &Type) -> bool {
		if self == other {
			true
		} else {
			match other {
				Type::Tuple(TupleKind::Sum, types) => {
					for ty in types {
						if self.is_subtype_of(ty) {
							return true;
						}
					}

					false
				}
				_ => false,
			}
		}
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
			(Self::TypeRef(l0), Self::TypeRef(r0)) => l0 == r0,
			(Self::TypeParam(l0), Self::TypeParam(r0)) => l0 == r0,
			(Self::Array(l0, _l1), Self::Array(r0, _r1)) => l0 == r0 && todo!(),
			(Self::Tuple(l0, l1), Self::Tuple(r0, r1)) => l0 == r0 && l1 == r1,
			(Self::Never, Self::Never) => true,
			_ => false,
		}
	}
}

impl Eq for Type {}

impl PartialEq for TypeRef {
	fn eq(&self, other: &Self) -> bool {
		Arc::ptr_eq(&self.def.upgrade().unwrap(), &other.def.upgrade().unwrap())
			&& self.name == other.name
			&& self.args == other.args
	}
}

impl Eq for TypeRef {}

impl Hash for TypeRef {
	fn hash<H: Hasher>(&self, state: &mut H) {
		ptr::hash(self.def.upgrade().unwrap().as_ref(), state);
		for (name, arg) in &self.args {
			name.hash(state);
			arg.hash(state);
		}
	}
}

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

			Type::TypeRef(ItemRef::Unresolved { name, scope }) => {
				name.hash(state);
				scope.hash(state)
			}

			Type::TypeRef(ItemRef::Resolved(ty)) => ty.hash(state),

			Type::TypeParam(name) => name.hash(state),

			Type::Never => "!".hash(state),

			Type::Tuple(kind, types) => {
				kind.hash(state);
				types.hash(state)
			}
		}
	}
}

impl Display for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self {
			Type::Basic(t) => write!(f, "{t}"),

			Type::Pointer(t) => write!(f, "{t}*"),

			Type::Array(t, _s) => write!(f, "{}[]", t),

			Type::TypeRef(ItemRef::Unresolved { name, .. }) => {
				write!(f, "unresolved type \"{name}\"")
			}

			Type::TypeRef(ItemRef::Resolved(TypeRef { name, args, .. })) => {
				if args.is_empty() {
					write!(f, "{name}")
				} else {
					let mut iter = args.iter();

					write!(f, "{name}<{}", iter.next().unwrap().0)?;

					for (arg, _) in iter {
						write!(f, ", {arg}")?;
					}

					write!(f, ">")
				}
			}

			Type::TypeParam(t) => write!(f, "<{t}>"),

			Type::Never => write!(f, "never"),

			Type::Tuple(kind, types) => {
				if types.is_empty() {
					write!(f, "()")
				} else {
					let mut iter = types.iter();

					write!(f, "({}", iter.next().unwrap())?;

					for ty in iter {
						if matches!(kind, TupleKind::Product) {
							write!(f, ", {ty}")?;
						} else {
							write!(f, " | {ty}")?;
						}
					}

					write!(f, ")")
				}
			}
		}
	}
}

impl Display for TypeDef {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self {
			TypeDef::Algebraic(agg) => {
				write!(f, "{}", agg)?;
			}
			TypeDef::Class => todo!(),
		}
		Ok(())
	}
}

impl Display for FnDef {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}(", self.ret)?;

		for param in &self.params.params {
			write!(f, "{}, ", param.0)?;
		}

		write!(f, ")")
	}
}

impl Display for AlgebraicDef {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut members = self.members.iter();

		write!(f, "Struct {{{:?}", members.next().unwrap().1)?;

		for mem in members {
			write!(f, ", {:?}", mem.1)?;
		}
		write!(f, "}}")
	}
}

impl Hash for AlgebraicDef {
	fn hash<H: Hasher>(&self, state: &mut H) {
		// We hash based on Type only, so two aggregates with the same layout have the same Hash
		// Hashing is only relevant for LLVM codegen, so semantic analysis will already have happened
		for (_, ty, _) in &self.members {
			ty.hash(state)
		}
	}
}

impl std::fmt::Debug for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Type::Basic(arg0) => f.debug_tuple("Basic").field(arg0).finish(),
			Type::Pointer(_) => f.debug_tuple("Pointer").finish(),
			Type::Array(t, _) => f.debug_tuple("Array").field(t).finish(),
			Type::TypeRef(ItemRef::Unresolved {
				name: arg0,
				scope: arg1,
			}) => f.debug_tuple("Unresolved").field(arg0).field(arg1).finish(),
			Type::TypeRef(ItemRef::Resolved(TypeRef { def: arg0, .. })) => {
				f.debug_tuple("TypeRef").field(arg0).finish()
			}
			Type::TypeParam(arg0) => f.debug_tuple("TypeParam").field(arg0).finish(),
			Type::Never => f.debug_tuple("Never").finish(),
			Type::Tuple(kind, types) => f.debug_tuple("Tuple").field(kind).field(types).finish(),
		}
	}
}