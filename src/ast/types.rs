use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ptr;
use std::sync::{Arc, RwLock, Weak};

use super::module::{Identifier, ItemRef, Name};
use super::traits::TraitRef;
use super::Attribute;
use crate::constexpr::ConstExpr;
use crate::lexer::SrcSpan;

pub type TypeParam = Vec<ItemRef<TraitRef>>; // Generic type parameter, with trait bounds
pub type GenericParamList = Vec<(Name, TypeParam, Option<Type>)>;

#[derive(Clone)]
pub enum Type {
	Basic(Basic), // Fundamental type
	Pointer {
		pointee: Box<Type>,
		mutable: bool,
	}, // Pointer-to-<BoxedType>
	Array(Box<Type>, Arc<RwLock<ConstExpr>>), // Aarray with constant expression for size

	TypeRef {
		// Reference to user-defined type
		def: Weak<RwLock<TypeDef>>,
		args: Vec<Type>,
	},

	Unresolved {
		// Unresolved typename
		name: Identifier,
		scope: Arc<Identifier>,
		type_args: Vec<Type>,
		span: SrcSpan,
	},

	TypeParam(usize),            // Reference to an in-scope type parameter
	Tuple(TupleKind, Vec<Type>), // Sum/product tuple
	Function(Box<Type>, Vec<(BindingProps, Type)>), // Type of a function signature
	Never,                       // Return type of a function that never returns, coerces to anything
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

#[derive(Debug, Clone)]
pub struct TypeDef {
	pub def: TypeDefKind,
	pub name: Identifier,
}

#[derive(Debug, Clone)]
pub enum TypeDefKind {
	Algebraic(AlgebraicDef),
	Class, // TODO: Implement classes
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BindingProps {
	pub is_ref: bool,
	pub is_mut: bool,
	pub is_unsafe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnParamList {
	pub params: Vec<(Type, Option<Name>, BindingProps)>,
	pub variadic: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FnPrototype {
	pub path: Identifier,
	pub ret: Type,
	pub params: FnParamList,
	pub type_params: GenericParamList,
	pub attributes: Vec<Attribute>,
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum TupleKind {
	Product,
	Sum,
	Newtype,
	Empty,
}

// The internal representation of algebraic types, like structs, enums, and (shocker) struct enums
//
// Algebraics (strums?) can contain member variables, inner type aliases, variants (aka subtype definitions), etc...
// Hence we give them the same data structure as Namespaces, a list of `String`s and `NamespaceEntry`s
// However, since declaration order *is* meaningful in strums, we store them as a Vec, rather than a HashMap
#[derive(Debug, Clone)]
pub struct AlgebraicDef {
	pub members: Vec<(Name, Type, Visibility)>,
	pub variants: Vec<(Name, Vec<Type>)>,
	pub layout: DataLayout,
	pub params: GenericParamList,
	pub attributes: Vec<Attribute>,
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

impl AlgebraicDef {
	pub fn new() -> Self {
		AlgebraicDef {
			layout: DataLayout::Declared,
			members: vec![],
			variants: vec![],
			params: vec![],
			attributes: vec![],
		}
	}

	pub fn get_member(&self, name: &Name, type_args: Option<&Vec<Type>>) -> Option<(usize, Type)> {
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
	pub fn get_concrete_type(&self, type_args: &Vec<Type>) -> Type {
		match self {
			Type::Basic(b) => Type::Basic(*b),

			Type::Pointer { pointee, mutable } => Type::Pointer {
				pointee: Box::new(pointee.get_concrete_type(type_args)),
				mutable: *mutable,
			},

			Type::Array(arr_ty, size) => {
				Type::Array(Box::new(arr_ty.get_concrete_type(type_args)), size.clone())
			}

			Type::TypeRef { def, args } => Type::TypeRef {
				def: def.clone(),
				args: args
					.iter()
					.map(|ty| ty.get_concrete_type(type_args))
					.collect(),
			},

			Type::TypeParam(param) => 
				if let Some(concrete) = type_args.get(*param) {
					if concrete == self {
						concrete.clone()
					} else {
						concrete.get_concrete_type(type_args)
					}
				} else {
					Type::TypeParam(*param)
				}

			Type::Never => Type::Never,

			Type::Tuple(kind, types) => Type::Tuple(
				*kind,
				types
					.iter()
					.map(|ty| ty.get_concrete_type(type_args))
					.collect(),
			),

			Type::Function(ret, args) => Type::Function(
				Box::new(ret.get_concrete_type(type_args)),
				args.iter()
					.map(|(props, arg)| (*props, arg.get_concrete_type(type_args)))
					.collect(),
			),

			Type::Unresolved { .. } => unreachable!(),
		}
	}

	// Check if self fits a generic type, without evaluating trait bounds
	pub fn fits_generic(&self, generic_ty: &Type) -> bool {
		if let Type::TypeParam(_) = generic_ty {
			true
		} else {
			match self {
				Type::Tuple(kind, types) => {
					let Type::Tuple(gen_kind, gen_types) = generic_ty else {
						return false;
					};

					if gen_kind != kind {
						return false;
					}

					if gen_types.len() != types.len() {
						return false;
					}

					for (ty, gen_ty) in types.iter().zip(gen_types.iter()) {
						if !ty.fits_generic(gen_ty) {
							return false;
						}
					}

					true
				}

				Type::Pointer { pointee, mutable } => {
					if let Type::Pointer {
						pointee: gen_pointee,
						mutable: gen_mutable,
					} = generic_ty
					{
						mutable == gen_mutable && pointee.fits_generic(gen_pointee)
					} else {
						false
					}
				}

				Type::TypeRef {
					def: ty_def,
					args: ty_args,
				} => {
					if let Type::TypeRef {
						def: gen_def,
						args: gen_args,
					} = generic_ty
					{
						if !Arc::ptr_eq(&ty_def.upgrade().unwrap(), &gen_def.upgrade().unwrap()) {
							return false;
						}

						if ty_args.len() != gen_args.len() {
							return false;
						}

						for (lhs, rhs) in ty_args.iter().zip(gen_args) {
							if !lhs.fits_generic(rhs) {
								return false;
							}
						}

						true
					} else {
						false
					}
				}

				Type::Unresolved { .. } => unreachable!(), // Unresolved TypeRef, REALLY shouldn't happen

				Type::Array(_, _) => todo!(),

				_ => self == generic_ty,
			}
		}
	}

	pub fn ptr_type(&self, mutable: bool) -> Self {
		Type::Pointer {
			pointee: Box::new(self.clone()),
			mutable,
		}
	}

	pub fn castable_to(&self, target: &Type) -> bool {
		if self == target || self == &Type::Never {
			true
		} else if self.is_numeric() {
			target.is_numeric() || target.is_boolean()
		} else if let (
			Type::Pointer { mutable, .. },
			Type::Pointer {
				mutable: target_mutable,
				..
			},
		) = (self, target)
		{
			// If self is a `T mut*`, it can be cast to a `T*`
			// but if self is a `T*`, it can't be cast to a `T mut*`
			*mutable || !target_mutable
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

	pub fn is_signed(&self) -> bool {
		if let Type::Basic(b) = self {
			b.is_signed()
		} else {
			false
		}
	}

	pub fn get_discriminant_type(&self) -> Option<Basic> {
		match self {
			Type::Tuple(TupleKind::Sum, _) => Some(Basic::Integral {
				signed: false,
				size_bytes: 4,
			}),

			_ => None,
		}
	}

	pub fn is_void(&self) -> bool {
		self == &Type::Basic(Basic::Void)
	}

	pub fn get_ir_typename(&self) -> String {
		let Type::TypeRef { def, args } = self else { panic!() };

		let mut typename = def.upgrade().unwrap().read().unwrap().name.to_string();

		if !args.is_empty() {
			typename.push('<');

			let mut iter = args.iter();

			typename.push_str(&iter.next().unwrap().to_string());

			for param in iter {
				typename.push_str(&param.to_string())
			}

			typename.push('>');
		}

		typename
	}
}

impl PartialEq for Type {
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(Self::Basic(l0), Self::Basic(r0)) => l0 == r0,
			(
				Self::Pointer {
					pointee: l0,
					mutable: l1,
				},
				Self::Pointer {
					pointee: r0,
					mutable: r1,
				},
			) => l0 == r0 && l1 == r1,
			(Self::TypeParam(l0), Self::TypeParam(r0)) => l0 == r0,
			(Self::Array(l0, _l1), Self::Array(r0, _r1)) => l0 == r0,
			(Self::Tuple(l0, l1), Self::Tuple(r0, r1)) => l0 == r0 && l1 == r1,
			(Self::Never, Self::Never) => true,
			(Self::Function(l0, l1), Self::Function(r0, r1)) => l0 == r0 && l1 == r1,

			(Self::TypeRef { def: l0, args: l1 }, Self::TypeRef { def: r0, args: r1 }) => {
				Arc::ptr_eq(&l0.upgrade().unwrap(), &r0.upgrade().unwrap()) && l1 == r1
			}

			(Self::Unresolved { .. }, _) | (_, Self::Unresolved { .. }) => panic!(),

			_ => false,
		}
	}
}

impl Eq for Type {}

impl Hash for AlgebraicDef {
	fn hash<H: Hasher>(&self, state: &mut H) {
		// We hash based on Type only, so two aggregates with the same layout have the same Hash
		// Hashing is only relevant for LLVM codegen, so semantic analysis will already have happened
		for (_, ty, _) in &self.members {
			ty.hash(state)
		}
	}
}

impl Hash for Type {
	fn hash<H: Hasher>(&self, state: &mut H) {
		match self {
			Type::Basic(b) => b.hash(state),
			Type::Pointer { pointee, mutable } => {
				pointee.hash(state);
				mutable.hash(state);
				"*".hash(state)
			}
			Type::Array(t, _s) => {
				t.hash(state);
				"+".hash(state)
			}

			Type::Unresolved {
				name,
				scope,
				type_args,
				span: _,
			} => {
				name.hash(state);
				scope.hash(state);
				type_args.hash(state);
			}

			Type::TypeRef { def, args } => {
				ptr::hash(def.upgrade().unwrap().as_ref(), state);
				args.hash(state);
			}

			Type::TypeParam(name) => name.hash(state),

			Type::Never => "!".hash(state),

			Type::Tuple(kind, types) => {
				kind.hash(state);
				types.hash(state)
			}

			Type::Function(ret, args) => {
				ret.hash(state);
				args.hash(state)
			}
		}
	}
}

impl Display for Basic {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.as_str())
	}
}

impl Display for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self {
			Type::Basic(t) => write!(f, "{t}"),

			Type::Pointer { pointee, mutable } => {
				if *mutable {
					write!(f, "{pointee} mut*")
				} else {
					write!(f, "{pointee}*")
				}
			}

			Type::Array(t, _s) => write!(f, "{}[]", t),

			Type::Unresolved {
				name, type_args, ..
			} => {
				write!(f, "\"{name}\"")?;

				if !type_args.is_empty() {
					let mut iter = type_args.iter();

					write!(f, "<{}", iter.next().unwrap())?;

					for arg in iter {
						write!(f, ", {arg}")?;
					}

					write!(f, ">")?;
				}
				Ok(())
			}

			Type::TypeRef { def, args } => {
				write!(f, "{}", def.upgrade().unwrap().read().unwrap().name)?;

				if !args.is_empty() {
					let mut iter = args.iter();

					write!(f, "<{}", iter.next().unwrap())?;

					for arg in iter {
						write!(f, ", {arg}")?;
					}

					write!(f, ">")?;
				}

				Ok(())
			}

			Type::TypeParam(t) => write!(f, "${t}"),

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
			Type::Function(ret, args) => {
				write!(f, "{ret}")?;

				if !args.is_empty() {
					let mut iter = args.iter();

					write!(f, "({}", iter.next().unwrap().1)?;

					for (_, arg) in iter {
						write!(f, ", {arg}")?;
					}

					write!(f, ")")
				} else {
					write!(f, "()")
				}
			}
		}
	}
}

impl Display for TypeDef {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self.def {
			TypeDefKind::Algebraic(agg) => {
				write!(f, "{}", agg)?;
			}
			TypeDefKind::Class => todo!(),
		}
		Ok(())
	}
}

impl Display for FnPrototype {
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
		if self.members.is_empty() {
			write!(f, "{{ }};\n\n")
		} else {
			let mut members = self.members.iter();

			let (ty, name, vis) = members.next().unwrap();

			write!(f, "{{\n\t{vis} {ty} {name};\n")?;

			for (ty, name, vis) in members {
				write!(f, "\t{vis} {ty} {name};\n")?;
			}
			write!(f, "}};\n\n")
		}
	}
}

impl Display for Visibility {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			match self {
				Visibility::Private => "private",
				Visibility::Protected => "protected",
				Visibility::Public => "public",
			}
		)
	}
}

impl Display for BindingProps {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if self.is_unsafe {
			write!(f, " unsafe")?;
		}
		if self.is_mut {
			write!(f, " mut")?;
		}
		if self.is_ref {
			write!(f, "&")?;
		}
		Ok(())
	}
}

impl std::fmt::Debug for Type {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Type::Basic(arg0) => f.debug_tuple("Basic").field(arg0).finish(),
			Type::Pointer { .. } => f.debug_tuple("Pointer").finish(),
			Type::Array(t, _) => f.debug_tuple("Array").field(t).finish(),
			Type::Unresolved {
				name: arg0,
				scope: arg1,
				type_args: arg2,
				span: _
			} => f
				.debug_tuple("Unresolved")
				.field(arg0)
				.field(arg1)
				.field(arg2)
				.finish(),
			Type::TypeRef { def: arg0, .. } => f.debug_tuple("TypeRef").field(arg0).finish(),
			Type::TypeParam(arg0) => f.debug_tuple("TypeParam").field(arg0).finish(),
			Type::Never => f.debug_tuple("Never").finish(),
			Type::Tuple(kind, types) => f.debug_tuple("Tuple").field(kind).field(types).finish(),
			Type::Function(ret, args) => f.debug_tuple("Function").field(ret).field(args).finish(),
		}
	}
}
