#![allow(dead_code)]

use std::{collections::HashMap, ffi::CString, hash::Hash};

use crate::ast::{
	expression::Operator,
	namespace::{Identifier, Name},
	types::{Basic, BindingProps, DataLayout, TupleKind, TypeParam},
	Attribute, TokenData,
};

pub mod analyze;
pub mod builder;
pub mod monoize;
pub mod serialize;

// Bunch of type aliases to make code more readable
type CIRFnMap = HashMap<CIRFnPrototype, CIRFunction>;
type BlockIndex = usize;
type StmtIndex = usize;
type VarIndex = usize;
type FieldIndex = usize;
type TypeName = String;
type TypeParamIndex = usize;
type FuncID = CIRFnPrototype;

pub type CIRTypeParamList = Vec<(Name, TypeParam, Option<CIRType>)>;

// An LValue is an expression that results in a memory location.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LValue {
	pub local: VarIndex,
	pub projection: Vec<PlaceElem>,
}

// A PlaceELem describes an element of an LValue expression, such as a deref or member access operation.
#[derive(Clone, Debug)]
pub enum PlaceElem {
	Deref,
	Field(FieldIndex),
	Index(CIRType, Operand),
}

impl PartialEq for PlaceElem {
	fn eq(&self, other: &Self) -> bool {
		match self {
			PlaceElem::Deref => matches!(other, PlaceElem::Deref),
			PlaceElem::Field(idx) => {
				if let PlaceElem::Field(other_idx) = other {
					idx == other_idx
				} else {
					false
				}
			}
			PlaceElem::Index(..) => matches!(other, PlaceElem::Index(..)),
		}
	}
}

impl Eq for PlaceElem {}

impl Hash for PlaceElem {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		match self {
			PlaceElem::Deref => "deref".hash(state),
			PlaceElem::Field(idx) => idx.hash(state),
			PlaceElem::Index(..) => "index".hash(state),
		}
	}
}

// An RValue is an expression that results in a value.
// All LValues are also usable as RValues, using Operand::LValue(LValue).
#[derive(Clone, Debug)]
pub enum RValue {
	Atom(CIRType, Option<Operator>, Operand),
	Cons(CIRType, [(CIRType, Operand); 2], Operator),
	Cast {
		from: CIRType,
		to: CIRType,
		val: Operand,
	},
}

// An Operand represents a single element of a CIR expression.
// This may either be a constant, an undef value, or an lvalue access.
// Crucially, operands do not have side effects. Yes, past Ash, I'm talking to you.
#[derive(Clone, Debug)]
pub enum Operand {
	IntegerLit(i128),
	FloatLit(f64),
	StringLit(String),
	CStringLit(CString),
	BoolLit(bool),
	LValue(LValue),
	Undef,
}

// A CIRType represents a non-unique instance of a comune type.
// Not to be confused with CIRTypeDefs, which are unique descriptions of i.e. struct definitions.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub enum CIRType {
	Basic(Basic),
	Pointer(Box<CIRType>),
	Array(Box<CIRType>, Vec<i128>),
	Reference(Box<CIRType>),
	TypeRef(TypeName, Vec<CIRType>), // TypeRef with zero or more type parameters
	TypeParam(TypeParamIndex),
	Tuple(TupleKind, Vec<CIRType>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CIRTypeDef {
	Algebraic {
		members: Vec<CIRType>,
		variants: Vec<CIRTypeDef>,
		layout: DataLayout,
		members_map: HashMap<Name, usize>,
		variants_map: HashMap<Name, usize>,
		type_params: CIRTypeParamList,
	},

	Class {},
}

#[derive(Debug, Clone)]
pub enum CIRStmt {
	Expression(RValue, TokenData),
	Assignment((LValue, TokenData), (RValue, TokenData)),
	Jump(BlockIndex),
	Switch(Operand, Vec<(CIRType, Operand, BlockIndex)>, BlockIndex),
	Return(Option<(Operand, TokenData)>),
	FnCall {
		id: FuncID,
		args: Vec<LValue>,
		type_args: Vec<CIRType>,
		result: Option<LValue>,
		next: BlockIndex,
		except: Option<BlockIndex>,
	},
}

#[derive(Debug, Clone)]
pub struct CIRBlock {
	pub items: Vec<CIRStmt>,
	pub preds: Vec<BlockIndex>,
	pub succs: Vec<BlockIndex>,
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct CIRFnPrototype {
	pub name: Identifier,
	pub ret: CIRType,
	pub params: Vec<(BindingProps, CIRType)>,
	pub type_params: CIRTypeParamList,
}

#[derive(Clone)]
pub struct CIRFunction {
	// In cIR, variables are referenced by an index, not a name.
	// (They may still have a name for pretty-printing, though.)
	pub variables: Vec<(CIRType, BindingProps, Option<Name>)>,
	pub blocks: Vec<CIRBlock>,
	pub ret: CIRType,
	pub arg_count: usize,
	pub type_params: CIRTypeParamList,
	pub attributes: Vec<Attribute>,
	pub is_extern: bool,
	pub is_variadic: bool,
	pub mangled_name: Option<String>,
}

pub struct CIRModule {
	pub types: HashMap<String, CIRTypeDef>,
	pub globals: HashMap<Identifier, (CIRType, RValue)>,
	pub functions: CIRFnMap,
}

impl CIRType {
	pub fn is_integral(&self) -> bool {
		if let CIRType::Basic(b) = self {
			b.is_integral()
		} else {
			false
		}
	}

	pub fn is_floating_point(&self) -> bool {
		if let CIRType::Basic(b) = self {
			b.is_floating_point()
		} else {
			false
		}
	}

	pub fn is_boolean(&self) -> bool {
		if let CIRType::Basic(b) = self {
			b.is_boolean()
		} else {
			false
		}
	}

	pub fn is_signed(&self) -> bool {
		if let CIRType::Basic(b) = self {
			b.is_signed()
		} else {
			false
		}
	}

	pub fn get_discriminant_type(&self) -> Option<Basic> {
		match self {
			CIRType::Tuple(TupleKind::Sum, _) => Some(Basic::Integral {
				signed: false,
				size_bytes: 4,
			}),

			_ => None,
		}
	}
}

impl RValue {
	pub fn const_bool(value: bool) -> Self {
		RValue::Atom(CIRType::Basic(Basic::Bool), None, Operand::BoolLit(value))
	}

	pub fn get_type(&self) -> &CIRType {
		match self {
			RValue::Atom(ty, _, _) | RValue::Cons(ty, _, _) => ty,
			RValue::Cast { to, .. } => to,
		}
	}
}
