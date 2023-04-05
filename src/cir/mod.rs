#![allow(dead_code)]

use std::{
	collections::HashMap,
	ffi::CString,
	hash::Hash,
	sync::{Arc, RwLock},
};

use crate::{
	ast::{
		expression::Operator,
		module::{Identifier, Name},
		types::{Basic, BindingProps, Type, TypeDef, TypeParam},
		Attribute,
	},
	lexer::SrcSpan,
};

pub mod analyze;
pub mod builder;
pub mod monoize;
pub mod serialize;

// Bunch of type aliases to make code more readable
type CIRFnMap = HashMap<CIRFnPrototype, CIRFunction>;
type CIRTyMap = HashMap<TypeName, Arc<RwLock<TypeDef>>>;
type BlockIndex = usize;
type StmtIndex = usize;
type VarIndex = usize;
type FieldIndex = usize;
type TypeName = String;
type TypeParamIndex = usize;
type FuncID = CIRFnPrototype;

pub type CIRTypeParamList = Vec<(Name, TypeParam, Option<Type>)>;

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
	Offset(Type, Operand, Operator),
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
			PlaceElem::Offset(..) => matches!(other, PlaceElem::Offset(..)),
		}
	}
}

impl Eq for PlaceElem {}

impl Hash for PlaceElem {
	fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
		match self {
			PlaceElem::Deref => "deref".hash(state),
			PlaceElem::Field(idx) => idx.hash(state),
			PlaceElem::Offset(..) => "index".hash(state),
		}
	}
}

// An RValue is an expression that results in a value.
// All LValues are also usable as RValues, using Operand::LValue(LValue).
#[derive(Clone, Debug)]
pub enum RValue {
	Atom(Type, Option<Operator>, Operand, SrcSpan),
	Cons(Type, [(Type, Operand); 2], Operator, SrcSpan),
	Cast {
		from: Type,
		to: Type,
		val: Operand,
		span: SrcSpan,
	},
}

// An Operand represents a single element of a CIR expression.
// This may either be a constant, an undef value, or an lvalue access.
// Crucially, operands do not have side effects. Yes, past Ash, I'm talking to you.
#[derive(Clone, Debug)]
pub enum Operand {
	IntegerLit(i128, SrcSpan),
	FloatLit(f64, SrcSpan),
	StringLit(String, SrcSpan),
	CStringLit(CString, SrcSpan),
	BoolLit(bool, SrcSpan),
	LValue(LValue, SrcSpan),
	Undef,
}

#[derive(Debug, Clone)]
pub enum CIRCallId {
	Direct(FuncID, SrcSpan),
	Indirect {
		local: LValue,
		ret: Type,
		args: Vec<(BindingProps, Type)>,
		span: SrcSpan,
	},
}

#[derive(Debug, Clone)]
pub enum CIRStmt {
	Expression(RValue),
	Assignment((LValue, SrcSpan), RValue),
	Jump(BlockIndex),
	Switch(Operand, Vec<(Type, Operand, BlockIndex)>, BlockIndex),
	Return(Option<Operand>),
	FnCall {
		id: CIRCallId,
		args: Vec<(LValue, SrcSpan)>,
		type_args: Vec<Type>,
		result: Option<LValue>,
		next: BlockIndex,
		except: Option<BlockIndex>,
	},
	StorageLive(VarIndex),
	StorageDead(VarIndex),
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
	pub ret: Type,
	pub params: Vec<(BindingProps, Type)>,
	pub type_params: CIRTypeParamList,
}

#[derive(Clone)]
pub struct CIRFunction {
	// In cIR, variables are referenced by an index, not a name.
	// (They may still have a name for pretty-printing, though.)
	pub variables: Vec<(Type, BindingProps, Option<Name>)>,
	pub blocks: Vec<CIRBlock>,
	pub ret: Type,
	pub arg_count: usize,
	pub type_params: CIRTypeParamList,
	pub attributes: Vec<Attribute>,
	pub is_extern: bool,
	pub is_variadic: bool,
	pub mangled_name: Option<String>,
}

pub struct CIRModule {
	pub types: HashMap<String, Arc<RwLock<TypeDef>>>,
	pub globals: HashMap<Identifier, (Type, RValue)>,
	pub functions: CIRFnMap,
}

impl RValue {
	pub fn const_bool(value: bool) -> Self {
		RValue::Atom(
			Type::Basic(Basic::Bool),
			None,
			Operand::BoolLit(value, SrcSpan::new()),
			SrcSpan::new(),
		)
	}

	pub fn get_type(&self) -> &Type {
		match self {
			RValue::Atom(ty, ..) | RValue::Cons(ty, ..) => ty,
			RValue::Cast { to, .. } => to,
		}
	}
}

impl CIRFunction {
	pub fn get_variable_name(&self, local: VarIndex) -> Identifier {
		Identifier::from_name(
			self.variables[local]
				.2
				.as_ref()
				.unwrap_or(&format!("(temporary variable _{})", local).into())
				.clone(),
			false,
		)
	}

	pub fn get_extern(&self) -> CIRFunction {
		CIRFunction {
			variables: self.variables[0..self.arg_count].to_vec(),
			blocks: vec![],
			ret: self.ret.clone(),
			arg_count: self.arg_count,
			type_params: self.type_params.clone(),
			attributes: self.attributes.clone(),
			is_extern: true,
			is_variadic: self.is_variadic,
			mangled_name: self.mangled_name.clone(),
		}
	}
}
