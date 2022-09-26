use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::ptr;
use std::sync::{RwLock, Weak, Arc};
use std::fmt::Display;

use once_cell::sync::OnceCell;

use super::namespace::{Identifier, NamespaceASTElem};
use crate::constexpr::ConstExpr;
use crate::semantic::{Attribute, FnScope};
use crate::parser::ASTResult;

pub type BoxedType = Box<Type>;
pub type FnParamList = Vec<(Type, Option<String>)>;

pub(crate) static PTR_SIZE_BYTES: OnceCell<u32> = OnceCell::new();


pub trait Typed {
	fn get_type<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> ASTResult<Type>;
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Basic {
	INTEGRAL{signed: bool, size_bytes: u32},
	SIZEINT{signed: bool},
	FLOAT{size_bytes: u32},
	CHAR,
	BOOL,
	VOID,
	STR,
}


#[derive(Clone)]
pub enum Type {
	Basic(Basic),											// Fundamental type
	Pointer(BoxedType),										// Pointer-to-<BoxedType>
	Tuple(Vec<Type>),										// Simple set of values of different types
	Array(BoxedType, RefCell<Vec<ConstExpr>>),				// N-dimensional array with constant expression for size
	Unresolved(Identifier),									// Unresolved type (during parsing phase)
	TypeRef(Weak<RwLock<TypeDef>>, Identifier)				// Reference to type definition, plus Identifier for serialization
}


#[derive(Debug)]
pub enum TypeDef {
	Function(Type, Vec<(Type, Option<String>)>),			// Return type + parameter types
	Algebraic(Box<AlgebraicType>),							// Data type for structs & enums
	// TODO: Add Class TypeDef
}


// Metatype that represents a generic algebraic type.
// This is the internal representation of both structs and enums, as they can contain each other.
#[derive(Clone, Debug)]
pub struct AlgebraicType {
	pub members: Vec<(String, (Type, RefCell<NamespaceASTElem>, Vec<Attribute>, Visibility))>,
	pub variants: Vec<(String, (Box<AlgebraicType>, Vec<Attribute>))>,
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
	Declared,			// Layout is exactly as declared
	Optimized,			// Layout may be shuffled to minimize padding
	Packed,				// Layout is packed in declaration order with no padding (no alignment)
}


impl AlgebraicType {
	pub fn new() -> Self {
		AlgebraicType { 
			members: vec![],
			variants: vec![],
			layout: DataLayout::Declared,
		}
	}
}


impl Basic {
	pub fn get_basic_type(name: &str) -> Option<Self> {
		match name {

			"i64" 			=>	Some(Basic::INTEGRAL { signed: true, size_bytes: 8 }),
			"i32" | "int"	=>	Some(Basic::INTEGRAL { signed: true, size_bytes: 4 }),
			"i16" 			=>	Some(Basic::INTEGRAL { signed: true, size_bytes: 2 }),
			"i8" 			=>	Some(Basic::INTEGRAL { signed: true, size_bytes: 1 }),

			"u64" 			=>	Some(Basic::INTEGRAL { signed: false, size_bytes: 8 }),
			"u32" | "uint"	=>	Some(Basic::INTEGRAL { signed: false, size_bytes: 4 }),
			"u16" 			=>	Some(Basic::INTEGRAL { signed: false, size_bytes: 2 }),
			"u8" 			=>	Some(Basic::INTEGRAL { signed: false, size_bytes: 1 }),

			"isize" 		=>	Some(Basic::SIZEINT { signed: false }),
			"usize" 		=>	Some(Basic::SIZEINT { signed: false }),

			"f64" | "double"	=>	Some(Basic::FLOAT { size_bytes: 8 }),
			"f32" | "float"		=>	Some(Basic::FLOAT { size_bytes: 4 }),

			"char" =>	Some(Basic::CHAR),
			"str" =>	Some(Basic::STR),
			"bool" =>	Some(Basic::BOOL),
			"void" =>	Some(Basic::VOID),
			
			_ => None,
		}
	}

	pub fn as_str(&self) -> &'static str {
		match self {
			Basic::INTEGRAL { signed, size_bytes } => match size_bytes {
				8 => if *signed { "i64" } else { "u64" },
				4 => if *signed { "i32" } else { "u32" },
				2 => if *signed { "i16" } else { "u16" },
				1 => if *signed { "i8" }  else { "u8" },
				_ => panic!()
			}

			Basic::FLOAT { size_bytes } =>	if *size_bytes == 8 { "f64" } 	else { "f32" },
			Basic::SIZEINT { signed } => 	if *signed			{ "isize" }	else { "usize" },

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
		matches!(self, Basic::INTEGRAL { .. })
	}

	pub fn is_signed(&self) -> bool {
		if let Basic::INTEGRAL { signed, .. } = self { 
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
			},

			Type::Array(t, _) => {
				result.push_str(&t.serialize());
				result.push_str("[]");
			}

			Type::Tuple(types) => {
				result.push_str("(");
				for t in types {
					result.push_str(&t.serialize());
				}
				result.push_str(")");
			}
			
			Type::Pointer(_) => {
				result.push_str("*");
			},

			Type::TypeRef(t, _) => result.push_str(&t.upgrade().unwrap().as_ref().read().unwrap().serialize()),

			Type::Unresolved(_) => { panic!("Attempt to serialize an unresolved type!"); },
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
		if let Type::Basic(b) = self { b.is_numeric() } else { false }
	}

	pub fn is_integral(&self) -> bool {
		if let Type::Basic(b) = self { b.is_integral() } else { false }
	}

	pub fn is_boolean(&self) -> bool {
		if let Type::Basic(b) = self { b.is_boolean() } else { false }
	}

	pub fn is_floating_point(&self) -> bool {
		if let Type::Basic(b) = self { b.is_floating_point() } else { false }
	}

	pub fn is_signed(&self) -> bool {
		if let Type::Basic(b) = self { b.is_signed() } else { false }
	}


	pub fn get_size_bytes(&self) -> u32 {
		let ptr_size = *PTR_SIZE_BYTES.get().unwrap();

		match &self {
			Type::Basic(b) => match b {
				Basic::FLOAT { size_bytes } | Basic::INTEGRAL { size_bytes, .. } => *size_bytes,

				Basic::SIZEINT { .. } => ptr_size,
				Basic::STR => ptr_size + ptr_size, // sizeof(char*) + sizeof(usize)

				Basic::CHAR => 1,
				Basic::BOOL => 1,
				Basic::VOID => 0,
				
			},

			Type::Pointer(_) => ptr_size,

			Type::TypeRef(t_ref, _) => t_ref.upgrade().unwrap().as_ref().read().unwrap().get_size_bytes(),
			
			_ => 0,
		}
	}
}


impl TypeDef {
	pub fn serialize(&self) -> String {
		let mut result = String::new();
		match &self {						
			TypeDef::Algebraic(a) => {
				for t in &a.members {
					result.push_str(&t.1.0.serialize());
				}
			},

			TypeDef::Function(ret, args) => {
				result.push_str("?");
				for arg in args {
					result.push_str(&arg.0.serialize());
				}
				result.push_str("!");
				result.push_str(&ret.serialize());
			},
		}
		result
	}

	// This is naive and often inaccurate; maybe query LLVM for the type size somehow?
	pub fn get_size_bytes(&self) -> u32 {
		let ptr_size = *PTR_SIZE_BYTES.get().unwrap() as u32;

		match &self {
			TypeDef::Algebraic(ts) => {
				let mut result = 0;

				for t in ts.members.iter() {
					result += t.1.0.get_size_bytes();
				}
				result
			},
			
			_ => 0,
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
            (Self::Unresolved(l0), Self::Unresolved(r0)) => l0 == r0,
            (Self::TypeRef(l0, l1), Self::TypeRef(r0, r1)) => Arc::ptr_eq(&l0.upgrade().unwrap(), &r0.upgrade().unwrap()) && l1 == r1,
			_ => false,
        }
    }
}


impl Eq for Type {}


impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Type::Basic(b) => b.hash(state),
            Type::Pointer(t) => { t.hash(state); "*".hash(state) },
			Type::Array(t, _s) => { t.hash(state);  "+".hash(state) },
			Type::Tuple(types) => { "(".hash(state); for t in types { t.hash(state); } ")".hash(state) }
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
			},

			Type::Pointer(t) => {
				write!(f, "{}*", t)?;
			},

			Type::Array(t, _s) => {
				write!(f, "{}[]", t)?;
			}

			Type::Tuple(types) => {
				if types.is_empty() {
					write!(f, "()")?;
				} else {
					let mut iter = types.iter();
					write!(f, "({}", iter.next().unwrap())?;
					for t in iter {
						write!(f, ", {}", t)?;
					}
					write!(f, ")")?;
				}
			}

			Type::Unresolved(t) => {
				write!(f, "unresolved type \"{}\"", t)?;
			},

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
			},
			
			TypeDef::Function(ret, params) => {
				write!(f, "{}(", ret)?;
				for param in params {
					write!(f, "{}, ", param.0)?;
				}
				write!(f, ")")?;
			},
		}
		Ok(())
	}
}


impl Display for AlgebraicType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut members = self.members.iter();
		write!(f, "Struct {{{}", members.next().unwrap().1.0)?;
		for mem in members {
			write!(f, ", {}", mem.1.0)?;
		}
		write!(f, "}}")
    }
}

impl Hash for AlgebraicType {
    fn hash<H: Hasher>(&self, state: &mut H) {
		// We hash based on Type only, so two aggregates with the same layout have the same Hash
		// Hashing is only relevant for LLVM codegen, so semantic analysis will already have happened
        self.members.iter().map(|item| &item.1.0).collect::<Vec<&Type>>().hash(state);
        self.variants.iter().map(|item| &item.1.0).collect::<Vec<&Box<AlgebraicType>>>().hash(state);
        //self.methods.iter().map(|item| &item.1.0).collect::<Vec<&Type>>().hash(state);
    }
}


impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Basic(arg0) => f.debug_tuple("Basic").field(arg0).finish(),
            Self::Pointer(_) => f.debug_tuple("Pointer").finish(),
            Self::Array(t, _) => f.debug_tuple("Array").field(t).finish(),
            Self::Tuple(types) => f.debug_tuple("Tuples").field(types).finish(),
            Self::Unresolved(arg0) => f.debug_tuple("Unresolved").field(arg0).finish(),
            Self::TypeRef(arg0, _) => f.debug_tuple("TypeRef").field(arg0).finish(),
        }
    }
}