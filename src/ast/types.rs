use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, RwLock, Weak};
use std::{mem, ptr};

use super::module::{Identifier, ItemRef, Name};
use super::traits::TraitRef;
use super::{write_arg_list, Attribute};
use crate::constexpr::ConstExpr;
use crate::lexer::SrcSpan;

pub type GenericArgs = Vec<GenericArg>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Generics {
	pub params: Vec<(Name, GenericParam)>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenericParam {
	Type {
		bounds: Vec<ItemRef<TraitRef>>,
		arg: Option<Type>,
	},
	// TODO: const generics
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum GenericArg {
	Type(Type),
}

impl Generics {
	pub fn new() -> Self {
		Generics { params: vec![] }
	}

	pub fn from_params(params: Vec<(Name, GenericParam)>) -> Self {
		Generics { params }
	}

	pub fn fill_with(&mut self, args: &[GenericArg]) {
		for ((_, param), arg) in self.params.iter_mut().zip(args) {
			param.fill_with(arg);
		}
	}

	pub fn get_as_arg_list(&self) -> Vec<GenericArg> {
		self.params
			.iter()
			.enumerate()
			.map(|(i, (_, param))| match param {
				GenericParam::Type { arg: None, .. } => GenericArg::Type(Type::TypeParam(i)),
				GenericParam::Type { arg: Some(ty), .. } => GenericArg::Type(ty.clone()),
			})
			.collect()
	}

	// Take base_generics's parameters and add them to the start of self's
	// Used for i.e. combining the generics from a method and its surrounding `impl` block
	pub fn add_base_generics(&mut self, mut base_generics: Generics) {
		mem::swap(&mut base_generics.params, &mut self.params);
		self.params.append(&mut base_generics.params);
	}

	pub fn insert_self_type(&mut self) {
		self.params
			.push(("Self".into(), GenericParam::blank_type()))
	}

	#[allow(dead_code)]
	pub fn get(&self, name: &str) -> Option<&GenericParam> {
		self.params
			.iter()
			.rev()
			.find(|(n, _)| <Name as AsRef<str>>::as_ref(n) == name)
			.map(|(_, u)| u)
	}

	pub fn get_mut(&mut self, name: &str) -> Option<&mut GenericParam> {
		self.params
			.iter_mut()
			.rev()
			.find(|(n, _)| <Name as AsRef<str>>::as_ref(n) == name)
			.map(|(_, u)| u)
	}

	pub fn is_empty(&self) -> bool {
		self.params.is_empty()
	}

	pub fn non_defaulted_count(&self) -> usize {
		self.params
			.iter()
			.filter(|(_, param)| !param.is_filled())
			.count()
	}
}

impl GenericParam {
	pub fn fill_with(&mut self, gen_arg: &GenericArg) {
		match (self, gen_arg) {
			(GenericParam::Type { arg, .. }, GenericArg::Type(ty)) => {
				*arg = Some(ty.clone());
			}
		}
	}

	pub fn is_filled(&self) -> bool {
		matches!(self, GenericParam::Type { arg: Some(_), .. })
	}

	pub fn blank_type() -> Self {
		GenericParam::Type {
			bounds: vec![],
			arg: None,
		}
	}

	#[allow(dead_code)]
	pub fn get_type_arg(&self) -> &Option<Type> {
		let GenericParam::Type { arg, .. } = self;
		arg
	}

	pub fn get_type_arg_mut(&mut self) -> &mut Option<Type> {
		let GenericParam::Type { arg, .. } = self;
		arg
	}
}

impl GenericArg {
	pub fn get_concrete_arg(&self, args: &[GenericArg]) -> GenericArg {
		match self {
			GenericArg::Type(ty) => GenericArg::Type(ty.get_concrete_type(args)),
		}
	}

	pub fn fits_generic(&self, arg: &GenericArg) -> bool {
		match (self, arg) {
			(GenericArg::Type(self_ty), GenericArg::Type(arg_ty)) => self_ty.fits_generic(arg_ty),
		}
	}

	pub fn get_type_arg(&self) -> &Type {
		match self {
			GenericArg::Type(ty) => ty,
		}
	}
}

#[derive(Debug, Clone)]
pub enum Type {
	Basic(Basic),

	Pointer {
		// Raw pointer type
		pointee: Box<Type>,
		mutable: bool,
	},

	Array(Box<Type>, Arc<RwLock<ConstExpr>>), // Aarray with constant expression for size

	// View type, dynamically sized
	// Note: mutability is determined by the binding
	Slice(Box<Type>),

	TypeRef {
		// Reference to user-defined type
		def: Weak<RwLock<TypeDef>>,
		args: GenericArgs,
	},

	Unresolved {
		// Unresolved typename
		name: Identifier,
		scope: Arc<Identifier>,
		generic_args: GenericArgs,
		span: SrcSpan,
	},

	TypeParam(usize),            // Reference to an in-scope type parameter
	Tuple(TupleKind, Vec<Type>), // Sum/product tuple
	Function(Box<Type>, Vec<(BindingProps, Type)>), // Type of a function signature
	Never,                       // The type of expressions that diverge, coerces to anything
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Basic {
	Integral { signed: bool, size: IntSize },
	Float { size: FloatSize },
	Bool,
	Void,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IntSize {
	I8,
	I16,
	I32,
	I64,
	IAddr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum FloatSize {
	F32,
	F64,
}

#[derive(Debug, Clone)]
pub struct TypeDef {
	pub name: Identifier,

	pub members: Vec<(Name, Type, Visibility)>,
	pub variants: Vec<(Name, Arc<RwLock<TypeDef>>)>,
	pub layout: DataLayout,
	pub generics: Generics,
	pub attributes: Vec<Attribute>,

	pub init: Vec<Arc<FnPrototype>>,    // Zero or more constructors
	pub drop: Option<Arc<FnPrototype>>, // Zero or one destructor
}

#[derive(Default, Debug, Clone, Copy)]
pub struct BindingProps {
	pub is_ref: bool,
	pub is_mut: bool,
	pub is_new: bool,
	pub span: SrcSpan,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FnParamList {
	pub params: Vec<(Type, Option<Name>, BindingProps)>,
	pub variadic: bool,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct FnPrototype {
	pub path: Identifier,
	pub ret: (BindingProps, Type),
	pub params: FnParamList,
	pub generics: Generics,
	pub attributes: Vec<Attribute>,
	pub is_unsafe: bool,
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum TupleKind {
	Product,
	Sum,
	Newtype,
	Empty,
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

impl TypeDef {
	pub fn new() -> Self {
		TypeDef {
			name: Identifier::new(true),
			layout: DataLayout::Declared,
			members: vec![],
			variants: vec![],
			generics: Generics::new(),
			attributes: vec![],
			init: vec![],
			drop: None,
		}
	}

	pub fn get_member(&self, name: &Name, generic_args: &[GenericArg]) -> Option<(usize, Type)> {
		let mut index = 0;

		for (member_name, ty, _) in &self.members {
			if member_name == name {
				return Some((index, ty.get_concrete_type(generic_args)));
			} else {
				index += 1;
			}
		}
		None
	}
}

impl BindingProps {
	pub fn value() -> Self {
		BindingProps {
			is_ref: false,
			is_mut: false,
			is_new: false,
			span: SrcSpan::new(),
		}
	}

	pub fn reference() -> Self {
		BindingProps {
			is_ref: true,
			is_mut: false,
			is_new: false,
			span: SrcSpan::new(),
		}
	}

	pub fn mut_value() -> Self {
		BindingProps {
			is_ref: false,
			is_mut: true,
			is_new: false,
			span: SrcSpan::new(),
		}
	}

	pub fn mut_reference() -> Self {
		BindingProps {
			is_ref: true,
			is_mut: true,
			is_new: false,
			span: SrcSpan::new(),
		}
	}
}

impl Basic {
	pub fn get_basic_type(name: &str) -> Option<Self> {
		match name {
			"i64" => Some(Basic::Integral {
				signed: true,
				size: IntSize::I64,
			}),
			"i32" | "int" => Some(Basic::Integral {
				signed: true,
				size: IntSize::I32,
			}),
			"i16" => Some(Basic::Integral {
				signed: true,
				size: IntSize::I16,
			}),
			"i8" => Some(Basic::Integral {
				signed: true,
				size: IntSize::I8,
			}),
			"u64" => Some(Basic::Integral {
				signed: false,
				size: IntSize::I64,
			}),
			"u32" | "uint" => Some(Basic::Integral {
				signed: false,
				size: IntSize::I32,
			}),
			"u16" => Some(Basic::Integral {
				signed: false,
				size: IntSize::I16,
			}),
			"u8" => Some(Basic::Integral {
				signed: false,
				size: IntSize::I8,
			}),

			"isize" => Some(Basic::Integral {
				signed: true,
				size: IntSize::IAddr,
			}),
			"usize" => Some(Basic::Integral {
				signed: false,
				size: IntSize::IAddr,
			}),

			"f64" | "double" => Some(Basic::Float {
				size: FloatSize::F64,
			}),
			"f32" | "float" => Some(Basic::Float {
				size: FloatSize::F32,
			}),

			"bool" => Some(Basic::Bool),
			"void" => Some(Basic::Void),

			_ => None,
		}
	}

	pub fn as_str(&self) -> &'static str {
		match self {
			Basic::Integral { signed: true, size } => match size {
				IntSize::IAddr => "isize",
				IntSize::I64 => "i64",
				IntSize::I32 => "i32",
				IntSize::I16 => "i16",
				IntSize::I8 => "i8",
			},

			Basic::Integral {
				signed: false,
				size,
			} => match size {
				IntSize::IAddr => "usize",
				IntSize::I64 => "u64",
				IntSize::I32 => "u32",
				IntSize::I16 => "u16",
				IntSize::I8 => "u8",
			},

			Basic::Float {
				size: FloatSize::F64,
			} => "f64",
			Basic::Float {
				size: FloatSize::F32,
			} => "f32",

			Basic::Bool => "bool",
			Basic::Void => "void",
		}
	}

	pub fn is_numeric(&self) -> bool {
		self.is_integral() || self.is_floating_point()
	}

	pub fn is_integral(&self) -> bool {
		matches!(self, Basic::Integral { .. })
	}

	pub fn is_signed(&self) -> bool {
		matches!(self, Basic::Integral { signed: true, .. })
	}

	pub fn is_boolean(&self) -> bool {
		matches!(self, Basic::Bool)
	}

	pub fn is_floating_point(&self) -> bool {
		matches!(self, Basic::Float { .. })
	}
}

impl Type {
	pub fn get_concrete_type(&self, args: &[GenericArg]) -> Type {
		match self {
			Type::Basic(b) => Type::Basic(*b),

			Type::Pointer { pointee, mutable } => Type::Pointer {
				pointee: Box::new(pointee.get_concrete_type(args)),
				mutable: *mutable,
			},

			Type::Array(arr_ty, size) => {
				Type::Array(Box::new(arr_ty.get_concrete_type(args)), size.clone())
			}

			Type::Slice(slicee) => Type::Slice(Box::new(slicee.get_concrete_type(args))),

			Type::TypeRef { def, args: ty_args } => {
				let ty_args_concrete = ty_args.iter().map(|ty| ty.get_concrete_arg(args)).collect();

				Type::TypeRef {
					def: def.clone(),
					args: ty_args_concrete,
				}
			}

			Type::TypeParam(param) => {
				if let Some(GenericArg::Type(concrete)) = &args.get(*param) {
					concrete.clone()
				} else {
					Type::TypeParam(*param)
				}
			}

			Type::Never => Type::Never,

			Type::Tuple(kind, types) => Type::Tuple(
				*kind,
				types.iter().map(|ty| ty.get_concrete_type(args)).collect(),
			),

			Type::Function(ret, fn_args) => Type::Function(
				Box::new(ret.get_concrete_type(args)),
				fn_args
					.iter()
					.map(|(props, arg)| (*props, arg.get_concrete_type(args)))
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

	pub fn needs_drop(&self) -> bool {
		match self {
			Type::TypeRef { def, .. } => {
				let def = def.upgrade().unwrap();
				let def = def.read().unwrap();

				if def.drop.is_some() {
					return true;
				}

				def.members.iter().any(|(_, ty, _)| ty.needs_drop())
			}

			Type::Array(arr_ty, _) => arr_ty.needs_drop(),

			Type::TypeParam(_) => true, // Can't be sure, conservative estimate

			Type::Tuple(_, types) => types.iter().any(|ty| ty.needs_drop()),

			_ => false,
		}
	}

	pub fn get_field_type(&self, field: usize) -> Type {
		let Type::TypeRef { def, args } = self else {
			panic!()
		};

		let def = def.upgrade().unwrap();
		let def = def.read().unwrap();

		def.members[field].1.get_concrete_type(args)
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
		} else if matches!(self, Type::Pointer { .. }) && target.is_boolean() {
			true
		} else {
			false
		}
	}

	pub fn get_variant_index(&self, variant: &Type) -> Option<usize> {
		match self {
			Type::TypeRef { def, .. } => {
				let def = def.upgrade().unwrap();
				let def = def.read().unwrap();
				
				let Type::TypeRef { def: variant_def, .. } = variant else {
					return None
				};

				def.variants.iter().position(|(_, var)| Arc::ptr_eq(var, &variant_def.upgrade().unwrap()))
			}

			Type::Tuple(TupleKind::Sum, types) => types.iter().position(|ty| ty == variant),

			_ => None
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
						if self == ty {
							return true;
						}
					}

					false
				}

				Type::TypeRef { def, args } => {
					let Type::TypeRef { def: self_def, args: self_args } = self else {
						return false
					};

					if args != self_args {
						return false;
					}

					let def = def.upgrade().unwrap();
					let def = def.read().unwrap();

					def.variants
						.iter()
						.any(|(_, variant)| Arc::ptr_eq(variant, &self_def.upgrade().unwrap()))
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
				size: IntSize::I32,
			}),

			Type::TypeRef { def, .. } => {
				if !def.upgrade().unwrap().read().unwrap().variants.is_empty() {
					Some(Basic::Integral { 
						signed: false, 
						size: IntSize::I32 
					})
				} else {
					None
				}
			}

			_ => None,
		}
	}

	pub fn is_void(&self) -> bool {
		self == &Type::Basic(Basic::Void)
	}

	pub fn is_void_or_never(&self) -> bool {
		matches!(self, Type::Basic(Basic::Void) | Type::Never)
	}

	pub fn get_ir_typename(&self) -> String {
		let Type::TypeRef { def, args } = self else { panic!() };

		let mut typename = def.upgrade().unwrap().read().unwrap().name.to_string();

		if !args.is_empty() {
			typename.push('<');

			let mut iter = args.iter();

			typename.push_str(&iter.next().unwrap().to_string());

			for param in iter {
				typename.push_str(", ");
				typename.push_str(&param.to_string())
			}

			typename.push('>');
		}

		typename
	}

	#[allow(dead_code)]
	pub fn i8_type(signed: bool) -> Self {
		Type::Basic(Basic::Integral {
			signed,
			size: IntSize::I8,
		})
	}

	#[allow(dead_code)]
	pub fn i16_type(signed: bool) -> Self {
		Type::Basic(Basic::Integral {
			signed,
			size: IntSize::I16,
		})
	}

	#[allow(dead_code)]
	pub fn i32_type(signed: bool) -> Self {
		Type::Basic(Basic::Integral {
			signed,
			size: IntSize::I32,
		})
	}

	#[allow(dead_code)]
	pub fn i64_type(signed: bool) -> Self {
		Type::Basic(Basic::Integral {
			signed,
			size: IntSize::I64,
		})
	}

	#[allow(dead_code)]
	pub fn isize_type(signed: bool) -> Self {
		Type::Basic(Basic::Integral {
			signed,
			size: IntSize::IAddr,
		})
	}

	pub fn f32_type() -> Self {
		Type::Basic(Basic::Float {
			size: FloatSize::F32,
		})
	}

	pub fn f64_type() -> Self {
		Type::Basic(Basic::Float {
			size: FloatSize::F64,
		})
	}

	pub fn bool_type() -> Self {
		Type::Basic(Basic::Bool)
	}

	pub fn void_type() -> Self {
		Type::Basic(Basic::Void)
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

			(
				Self::Unresolved {
					name: l0,
					scope: l1,
					generic_args: l2,
					..
				},
				Self::Unresolved {
					name: r0,
					scope: r1,
					generic_args: r2,
					..
				},
			) => l0 == r0 && l1 == r1 && l2 == r2,

			(Self::Slice(l0), Self::Slice(r0)) => l0 == r0,

			_ => {
				if std::mem::discriminant(self) == std::mem::discriminant(other) {
					panic!("unimplemented PartialEq variant for Type!")
				} else {
					false
				}
			}
		}
	}
}

impl Eq for Type {}

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

			Type::Slice(slicee) => {
				slicee.hash(state);
				"[]".hash(state)
			}

			Type::Unresolved {
				name,
				scope,
				generic_args,
				span: _,
			} => {
				name.hash(state);
				scope.hash(state);
				generic_args.hash(state);
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

impl PartialEq for BindingProps {
	fn eq(&self, other: &Self) -> bool {
		(self.is_mut, self.is_ref, self.is_new) == (other.is_mut, other.is_ref, other.is_new)
	}
}

impl Eq for BindingProps {}

impl Hash for BindingProps {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.is_mut.hash(state);
		self.is_ref.hash(state);
		self.is_new.hash(state);
	}
}

impl Display for GenericArg {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			GenericArg::Type(ty) => write!(f, "{ty}"),
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
		match self {
			Type::Basic(t) => write!(f, "{t}"),

			Type::Pointer { pointee, mutable } => {
				if *mutable {
					write!(f, "{pointee} mut*")
				} else {
					write!(f, "{pointee}*")
				}
			}

			Type::Array(t, _) => write!(f, "{t}[]"), // TODO: ConstExpr serialization

			Type::Slice(slicee) => write!(f, "{slicee}[dyn]"),

			Type::Unresolved {
				name, generic_args, ..
			} => {
				write!(f, "\"{name}\"")?;

				if !generic_args.is_empty() {
					write_arg_list!(f, generic_args, "<", ">");
				}

				Ok(())
			}

			Type::TypeRef { def, args } => {
				write!(f, "{}", def.upgrade().unwrap().read().unwrap().name)?;

				if !args.is_empty() {
					write_arg_list!(f, args, "<", ">");
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
					let first = iter.next().unwrap();

					write!(f, "({}{}", first.1, first.0)?;

					for (props, arg) in iter {
						write!(f, ", {arg}{props}")?;
					}

					write!(f, ")")
				} else {
					write!(f, "()")
				}
			}
		}
	}
}

impl Display for FnPrototype {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}{} {}", self.ret.1, self.ret.0, self.path).unwrap();

		if !self.generics.is_empty() {
			let mut iter = self.generics.params.iter();
			let first = iter.next().unwrap();

			write!(f, "<{}{}", first.0, first.1).unwrap();

			for (name, param) in iter {
				write!(f, ", {name}{param}").unwrap();
			}

			write!(f, ">").unwrap();
		}

		if !self.params.params.is_empty() {
			let mut iter = self.params.params.iter();
			let first = iter.next().unwrap();

			write!(f, "({}{}", first.0, first.2).unwrap();

			for (param, _, props) in iter {
				write!(f, ", {param}{props}").unwrap();
			}

			if self.params.variadic {
				write!(f, ", ...").unwrap();
			}

			write!(f, ")").unwrap();
		} else {
			write!(f, "()").unwrap();
		}

		Ok(())
	}
}

impl Display for TypeDef {
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

impl Display for GenericParam {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			GenericParam::Type { bounds, arg } => {
				if !bounds.is_empty() {
					let mut iter = bounds.iter();

					write!(f, ": {}", iter.next().unwrap())?;

					for bound in iter {
						write!(f, " + {bound}")?;
					}
				}

				if let Some(arg) = arg {
					write!(f, " = {arg}")?;
				}

				Ok(())
			}
		}
	}
}

impl Display for ItemRef<TraitRef> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			ItemRef::Resolved(tr) => write!(f, "{}", tr.name),
			ItemRef::Unresolved { name, .. } => write!(f, "`{name}`"),
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
		if self.is_new {
			write!(f, " new")?;
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
