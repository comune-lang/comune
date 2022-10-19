#![allow(dead_code)]

use std::{cell::RefCell, collections::HashMap};

use crate::semantic::{
	expression::Operator,
	namespace::Identifier,
	types::{Basic, DataLayout},
	Attribute,
};

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
type TypeIndex = usize;

// An LValue is an expression that results in a memory location.
#[derive(Clone, Debug)]
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
#[derive(Clone, Debug)]
pub enum Operand {
	FnCall(Identifier, Vec<RValue>, RefCell<Option<String>>), // Fully-qualified name + args + mangled name
	IntegerLit(i128),
	FloatLit(f64),
	StringLit(String),
	BoolLit(bool),
	LValue(LValue),
	Undef,
}

// A CIRType represents a non-unique instance of a comune type.
// Not to be confused with CIRTypeDefs, which are unique descriptions of i.e. struct definitions.
#[derive(Clone, Debug, Hash)]
pub enum CIRType {
	Basic(Basic),
	Pointer(Box<CIRType>),
	Array(Box<CIRType>, Vec<i128>),
	Reference(Box<CIRType>),
	TypeRef(TypeIndex),
}

#[derive(Debug)]
pub enum CIRTypeDef {
	Algebraic {
		members: Vec<CIRType>,
		variants: Vec<CIRTypeDef>,
		layout: DataLayout,

		members_map: HashMap<String, usize>,
		variants_map: HashMap<String, usize>,
	},

	Class {},
}

#[derive(Debug)]
pub enum CIRStmt {
	Expression(RValue),
	Assignment(LValue, RValue),
	Jump(BlockIndex),
	Branch(RValue, BlockIndex, BlockIndex),
	Return(Option<RValue>),
}

pub struct CIRFunction {
	// In cIR, variables are referenced by an index, not a name.
	// (They may still have a name for pretty-printing, though.)
	pub variables: Vec<(CIRType, Option<String>)>,
	pub blocks: Vec<CIRBlock>,
	pub ret: CIRType,
	pub arg_count: usize,
	pub attributes: Vec<Attribute>,
	pub is_extern: bool,
}

pub struct CIRModule {
	pub types: Vec<CIRTypeDef>,
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
