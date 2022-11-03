#![allow(dead_code)]

use std::{collections::HashMap, hash::Hash, sync::RwLock};

use crate::semantic::{
	ast::TokenData,
	expression::Operator,
	namespace::{Identifier, Name},
	types::{Basic, DataLayout, TypeParam, TypeParamList},
	Attribute,
};

pub mod analyze;
pub mod builder;
pub mod monoize;
pub mod serialize;

// Bunch of type aliases to make code more readable
type CIRFnMap = HashMap<Identifier, (CIRFunction, Option<String>)>;
type CIRBlock = Vec<CIRStmt>;
type BlockIndex = usize;
type StmtIndex = usize;
type VarIndex = usize;
type FieldIndex = usize;
type TypeName = String;
type TypeParamIndex = usize;

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
	Index(RValue),
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
			PlaceElem::Index(_) => matches!(other, PlaceElem::Index(_)),
		}
	}
}

impl Eq for PlaceElem {}

impl Hash for PlaceElem {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		match self {
			PlaceElem::Deref => "deref".hash(state),
			PlaceElem::Field(idx) => idx.hash(state),
			PlaceElem::Index(_) => "index".hash(state),
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
#[derive(Debug)]
pub enum Operand {
	FnCall(Identifier, Vec<RValue>, RwLock<Option<String>>), // Fully-qualified name + args + mangled name
	IntegerLit(i128),
	FloatLit(f64),
	StringLit(String),
	BoolLit(bool),
	LValue(LValue),
	Undef,
}

impl Clone for Operand {
	fn clone(&self) -> Self {
		match self {
			Operand::FnCall(id, rval, name) => Operand::FnCall(
				id.clone(),
				rval.clone(),
				RwLock::new(name.read().unwrap().clone()),
			),
			Operand::IntegerLit(lit) => Operand::IntegerLit(*lit),
			Operand::FloatLit(lit) => Operand::FloatLit(*lit),
			Operand::StringLit(lit) => Operand::StringLit(lit.clone()),
			Operand::BoolLit(lit) => Operand::BoolLit(*lit),
			Operand::LValue(lval) => Operand::LValue(lval.clone()),
			Operand::Undef => Operand::Undef,
		}
	}
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CIRTypeDef {
	Algebraic {
		members: Vec<CIRType>,
		variants: Vec<CIRTypeDef>,
		layout: DataLayout,
		members_map: HashMap<Name, usize>,
		variants_map: HashMap<Name, usize>,
		type_params: TypeParamList,
	},

	Class {},
}

#[derive(Debug)]
pub enum CIRStmt {
	Expression(RValue, TokenData),
	Assignment((LValue, TokenData), (RValue, TokenData)),
	Jump(BlockIndex),
	Branch(RValue, BlockIndex, BlockIndex),
	Return(Option<(RValue, TokenData)>),
}

pub struct CIRFunction {
	// In cIR, variables are referenced by an index, not a name.
	// (They may still have a name for pretty-printing, though.)
	pub variables: Vec<(CIRType, Option<Name>)>,
	pub blocks: Vec<CIRBlock>,
	pub ret: CIRType,
	pub arg_count: usize,
	pub attributes: Vec<Attribute>,
	pub is_extern: bool,
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
}
