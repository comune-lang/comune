use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::ptr;
use std::rc::Rc;
use std::{fmt::Display, collections::HashMap};

use once_cell::sync::OnceCell;

use super::namespace::{Identifier, NamespaceASTElem};
use super::semantic::Attribute;
use super::{semantic::FnScope, ASTResult};

pub type BoxedType = Box<Type>;
pub type FnParamList = Vec<(Type, Option<String>)>;

pub(crate) static PTR_SIZE_BYTES: OnceCell<u32> = OnceCell::new();


pub trait Typed {
	fn get_type<'ctx>(&self, scope: &'ctx FnScope<'ctx>) -> ASTResult<Type>;
}


#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Basic {
	I64,
	U64,
	I32,
	U32,
	I16,
	U16,
	I8,
	U8,
	CHAR,
	F64,
	F32,
	ISIZE,
	USIZE,
	BOOL,
	VOID,
	STR,
}


impl Basic {
	pub fn get_basic_type(name: &str) -> Option<Self> {
		match name {
			// Concrete names
			"i64" =>	Some(Basic::I64),
			"u64" =>	Some(Basic::U64),
			"i32" =>	Some(Basic::I32),
			"u32" =>	Some(Basic::U32),
			"i16" =>	Some(Basic::I16),
			"u16" =>	Some(Basic::U16),
			"i8" =>		Some(Basic::I8),
			"u8" =>		Some(Basic::U8),
			"char" =>	Some(Basic::CHAR),
			"str" =>	Some(Basic::STR),
			"f64" =>	Some(Basic::F64),
			"f32" =>	Some(Basic::F32),
			"isize" =>	Some(Basic::ISIZE),
			"usize" =>	Some(Basic::USIZE),
			"bool" =>	Some(Basic::BOOL),
			"void" =>	Some(Basic::VOID),
			
			// Friendly names
			"int" =>		Some(Basic::I32),
			"uint" =>		Some(Basic::U32),
			"float" =>		Some(Basic::F32),
			"double" =>		Some(Basic::F64),
			
			_ => None,
		}
	}

	pub fn as_str(&self) -> &'static str {
		match self {
			Basic::I64 => "i64",
			Basic::U64 => "u64",
			Basic::I32 => "i32",
			Basic::U32 => "u32",
			Basic::I16 => "i16",
			Basic::U16 => "u16",
			Basic::I8 => "i8",
			Basic::U8 => "u8",
			Basic::CHAR => "char",
			Basic::STR => "str",
			Basic::F64 => "f64",
			Basic::F32 => "f32",
			Basic::ISIZE => "isize",
			Basic::USIZE => "usize",
			Basic::BOOL => "bool",
			Basic::VOID => "void",
		}
	}

	
	pub fn is_numeric(&self) -> bool {
		self.is_integral() || self.is_floating_point()
	}


	pub fn is_integral(&self) -> bool {
		match self {
			Basic::ISIZE | Basic::USIZE | 
			Basic::I64 | Basic::U64 | 
			Basic::I32 | Basic::U32 | 
			Basic::I16 | Basic::U16 | 
			Basic::I8 | Basic::U8 => 
				true,
			
			_ => 
				false
		}
	}

	pub fn is_signed(&self) -> bool {
		match self {
			Basic::ISIZE | Basic::I64 | Basic::I32 | Basic::I16 | Basic::I8 => 
				true,
			_ => 
				false
		}
	}


	pub fn is_boolean(&self) -> bool {
		match self {
			Basic::BOOL => true,
			_ => false,
		}
	}


	pub fn is_floating_point(&self) -> bool {
		match self {
			Basic::F32 | Basic::F64 => 
				true,
			
			_ => 
				false
		}
	}
}


impl Display for Basic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}


#[derive(Clone)]
pub enum Type {
	Basic(Basic),											// Fundamental type
	Pointer(BoxedType),										// Pointer-to-<BoxedType>
	Unresolved(Identifier),									// Unresolved type (during parsing phase)
	TypeRef(Rc<RefCell<TypeDef>>)							// Reference to type definition
}


#[derive(Debug, PartialEq)]
pub enum TypeDef {
	Function(Type, Vec<(Type, Option<String>)>),			// Return type + parameter types
	Aggregate(Box<AggregateType>),							// Guess.
	Alias(String, Type)										// Identifier + referenced type
}


impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Basic(l0), Self::Basic(r0)) => l0 == r0,
            (Self::Pointer(l0), Self::Pointer(r0)) => l0 == r0,
            (Self::Unresolved(l0), Self::Unresolved(r0)) => l0 == r0,
            (Self::TypeRef(l0), Self::TypeRef(r0)) => Rc::ptr_eq(l0, r0),
			_ => false,
        }
    }
}

impl Eq for Type {}

impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Type::Basic(b) => b.hash(state),
            Type::Pointer(t) => t.hash(state),
            Type::Unresolved(id) => id.hash(state),
            Type::TypeRef(r) => ptr::hash(r.as_ref(), state),
        }
    }
}



impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self {
			Type::Basic(t) => {
				write!(f, "{}", t)?;
			},

			Type::Pointer(_) => {
				write!(f, "ptr")?;
			},

			Type::Unresolved(t) => {
				write!(f, "\"{}\"", t)?;
			},

			Type::TypeRef(t) => {
				t.as_ref().borrow().fmt(f)?;
			}
		}

		Ok(())
    }
}


impl Display for TypeDef {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match &self {
			TypeDef::Alias(a, t) => {
				write!(f, "{} ({})", a, t)?;
			},

			TypeDef::Aggregate(agg) => {
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

			
			Type::Pointer(_) => {
				result.push_str("*");
			},

			Type::TypeRef(t) => result.push_str(&t.as_ref().borrow().serialize()),

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


	pub fn get_size_bytes(&self) -> usize {
		let ptr_size = *PTR_SIZE_BYTES.get().unwrap() as usize;

		match &self {
			Type::Basic(b) => match b {
				Basic::I64 | Basic::U64 | Basic::F64 => 8,
				Basic::I32 | Basic::U32 | Basic::F32 | Basic::CHAR => 4, // Chars in a string are variable-width, lone char is 4 bytes
				Basic::I16 | Basic::U16 => 2,
				Basic::I8 | Basic::U8 => 1,

				// TODO: Actually implement based on target ptr size
				Basic::ISIZE | Basic::USIZE => ptr_size,
				Basic::STR => ptr_size + ptr_size, // sizeof(char*) + sizeof(usize)

				Basic::BOOL => 1,
				Basic::VOID => 0,
				
			},

			Type::Pointer(_) => ptr_size,

			Type::TypeRef(t_ref) => t_ref.as_ref().borrow().get_size_bytes(),
			
			_ => 0,
		}
	}
}


impl TypeDef {
	pub fn serialize(&self) -> String {
		let mut result = String::new();
		match &self {
			// TODO: Consider if aliased types are equivalent at the ABI stage?
			TypeDef::Alias(_, t) => return t.serialize(),
						
			TypeDef::Aggregate(a) => {
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

	pub fn get_size_bytes(&self) -> usize {
		let ptr_size = *PTR_SIZE_BYTES.get().unwrap() as u32;

		match &self {
			TypeDef::Alias(_, t) => t.get_size_bytes(),

			TypeDef::Aggregate(ts) => {
				let mut result: usize = 0;

				for t in ts.members.iter() {
					result += t.1.0.get_size_bytes();
				}
				result
			},
			
			_ => 0,
		}
	}
}



#[derive(Clone, Debug, PartialEq)]
pub struct AggregateType {
	pub members: Vec<(String, (Type, RefCell<NamespaceASTElem>, Vec<Attribute>, Visibility))>,
	pub methods: HashMap<String, (Type, RefCell<NamespaceASTElem>, Vec<Attribute>)>,
	pub constructors: Vec<Type>,
	pub destructor: Option<Type>,
	pub inherits: Vec<Type>,
}


#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Visibility {
	Public,
	Private,
	Protected,
}


impl AggregateType {
	pub fn new() -> Self {
		AggregateType { 
			members: vec![],
			methods: HashMap::new(),
			constructors: vec![],
			destructor: None,
			inherits: vec![],
		}
	}
}

impl Display for AggregateType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		let mut members = self.members.iter();
		write!(f, "Struct {{{}", members.next().unwrap().1.0)?;
		for mem in members {
			write!(f, ", {}", mem.1.0)?;
		}
		write!(f, "}}")
    }
}

impl Hash for AggregateType {
    fn hash<H: Hasher>(&self, state: &mut H) {
		// We hash based on Type only, so two aggregates with the same layout have the same Hash
		// Hashing is only relevant for LLVM codegen, so semantic analysis will already have happened
        self.members.iter().map(|item| &item.1.0).collect::<Vec<&Type>>().hash(state);
        self.methods.iter().map(|item| &item.1.0).collect::<Vec<&Type>>().hash(state);
        self.constructors.hash(state);
        self.destructor.hash(state);
        self.inherits.hash(state);
    }
}


impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Basic(arg0) => f.debug_tuple("Basic").field(arg0).finish(),
            Self::Pointer(_) => f.debug_tuple("Pointer").finish(),
            Self::Unresolved(arg0) => f.debug_tuple("Unresolved").field(arg0).finish(),
            Self::TypeRef(arg0) => f.debug_tuple("TypeRef").field(arg0).finish(),
        }
    }
}