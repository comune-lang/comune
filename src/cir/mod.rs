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
		traits::ImplSolver,
		types::{Basic, BindingProps, FnPrototype, GenericArgs, Generics, Type, TypeDef},
		Attribute,
	},
	lexer::{SrcSpan, Token},
};

pub mod analyze;
pub mod builder;
pub mod monoize;
pub mod serialize;

// Bunch of type aliases to make code more readable
type CIRFnMap = HashMap<Arc<FnPrototype>, CIRFunction>;
type CIRTyMap = HashMap<TypeName, Arc<RwLock<TypeDef>>>;
type BlockIndex = usize;
type StmtIndex = usize;
type VarIndex = usize;
type FieldIndex = usize;
type TypeName = String;
type FuncID = Arc<FnPrototype>;

// An LValue is an expression that results in a memory location.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LValue {
	pub local: VarIndex,
	pub projection: Vec<PlaceElem>,
	pub props: BindingProps,
}

impl LValue {
	pub fn new(local: VarIndex) -> Self {
		LValue {
			local,
			projection: vec![],
			props: BindingProps::default(),
		}
	}
	
	pub fn with_props(local: VarIndex, props: BindingProps) -> Self {
		LValue {
			local,
			projection: vec![],
			props
		}
	}
}

// A PlaceELem describes an element of an LValue expression, such as a deref or member access operation.
#[derive(Clone, Debug)]
pub enum PlaceElem {
	Deref,
	Field(FieldIndex),
	Index(Type, Operand, Operator),
	SumDisc, // sum type/enum discriminant field
	SumData(Type), // sum type/enum data field
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
			PlaceElem::SumDisc => matches!(other, PlaceElem::SumDisc),
			PlaceElem::SumData(ty) => {
				if let PlaceElem::SumData(other) = other {
					ty == other
				} else {
					false
				}
			}
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
			PlaceElem::SumData(ty) => { "sum_data".hash(state); ty.hash(state) }
			PlaceElem::SumDisc => "sum_disc".hash(state),
		};

		".".hash(state)
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
#[derive(Clone, Debug)]
pub enum Operand {
	// Literals
	IntegerLit(i128, SrcSpan),
	FloatLit(f64, SrcSpan),
	StringLit(String, SrcSpan),
	CStringLit(CString, SrcSpan),
	BoolLit(bool, SrcSpan),

	// LValue use
	LValueUse(LValue, BindingProps),

	// Undefined value. Reading from this is UB, must be reassigned first
	Undef,
}

#[derive(Debug, Clone)]
pub enum CIRCallId {
	Direct(FuncID, SrcSpan),
	Indirect {
		local: LValue,
		ret: Type,
		args: Vec<(Type, Option<Name>, BindingProps)>,
		span: SrcSpan,
	},
}

#[derive(Debug, Clone)]
pub enum CIRStmt {
	// Assignment to a variable. Non-terminator.
	Assignment(LValue, RValue),

	// Reference initialization. Non-terminator.
	RefInit(VarIndex, LValue),
	
	// Initialize a reference to a global variable or function.
	GlobalAccess {
		local: VarIndex,
		symbol: Identifier
	},

	// Unconditional jump to the block at BlockIndex. Terminator.
	Jump(BlockIndex),

	// Generalized version of a conditional jump. Terminator.
	//
	// Reads the value from the first Operand, and matches it
	// against the others. The final BlockIndex denotes the
	// `else` case; where to jump if no arms were matched.
	Switch(Operand, Vec<(Type, Operand, BlockIndex)>, BlockIndex),

	// Return statement. Terminator.
	Return,

	// Non-throwing fn call. Non-terminator.
	Call {
		id: CIRCallId,
		args: Vec<(LValue, Type, BindingProps)>,
		generic_args: GenericArgs,
		result: Option<LValue>,
	},

	// Throwing fn call. Terminator.
	#[allow(dead_code)]
	Invoke {
		id: CIRCallId,
		args: Vec<(LValue, Type, BindingProps)>,
		generic_args: GenericArgs,
		result: Option<LValue>,
		next: BlockIndex,
		except: BlockIndex,
	},

	// Defines the start of a variable's lifetime. Non-terminator.
	//
	// NOTE: Must dominate *all* Assignments to the VarIndex.
	StorageLive(VarIndex),

	// Defines the end of a variable's lifetime. Non-terminator.
	StorageDead(VarIndex),

	// Defines an implicit or explicit destructor call. Terminator.
	//
	// NOTE: Unlike StorageDead, DropShim is a terminator, as
	// it is used to build the destructor code for a variable,
	// which may involve non-trivial CFG construction.
	DropShim {
		var: LValue,
		next: BlockIndex,
	},

	// Defines an unreachable point in the IR. Terminator.
	// Reaching this statement is UB, so care must be taken
	// when writing codegen involving it (usually around Never types)
	Unreachable,
}

#[derive(Debug, Clone)]
pub struct CIRBlock {
	pub items: Vec<CIRStmt>,
	pub preds: Vec<BlockIndex>,
	pub succs: Vec<BlockIndex>,
}

#[derive(Clone)]
pub struct CIRFunction {
	// In cIR, variables are referenced by an index, not a name.
	// (They may still have a name for pretty-printing, though.)
	pub variables: Vec<(Type, BindingProps, Option<Name>)>,
	pub blocks: Vec<CIRBlock>,
	pub ret: (BindingProps, Type),
	pub arg_count: usize,
	pub generics: Generics,
	pub attributes: Vec<Attribute>,
	pub is_extern: bool,
	pub is_variadic: bool,
}

pub struct CIRModule {
	pub types: HashMap<String, Arc<RwLock<TypeDef>>>,
	pub globals: HashMap<Identifier, (Type, RValue)>,
	pub functions: CIRFnMap,
	pub impl_solver: ImplSolver,
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

	pub fn undef(ty: Type) -> Self {
		RValue::Atom(
			ty,
			None,
			Operand::Undef,
			SrcSpan::new()
		)
	}

	pub fn lvalue_use(ty: Type, lval: LValue, props: BindingProps) -> Self {
		RValue::Atom(
			ty,
			None,
			Operand::LValueUse(lval, props),
			SrcSpan::new()
		)
	}

	pub fn get_type(&self) -> &Type {
		match self {
			RValue::Atom(ty, ..) | RValue::Cons(ty, ..) => ty,
			RValue::Cast { to, .. } => to,
		}
	}
}

impl CIRBlock {
	fn new() -> Self {
		CIRBlock { items: vec![], preds: vec![], succs: vec![] }
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

	pub fn get_lvalue_type(&self, lval: &LValue) -> Type {
		let mut ty = self.variables[lval.local].0.clone();

		for proj in &lval.projection {
			match proj {
				PlaceElem::Deref => {
					let Type::Pointer { pointee, .. } = ty else {
						panic!()
					};

					ty = *pointee;
				}

				PlaceElem::Index(..) => {
					let (Type::Array(sub, _) | Type::Slice(sub) | Type::Pointer { pointee: sub, .. }) = ty else {
						panic!()
					};

					ty = *sub;
				}

				PlaceElem::Field(field) => {
					ty = ty.get_field_type(*field);
				}

				PlaceElem::SumData(variant) => ty = variant.clone(),
				PlaceElem::SumDisc => ty = Type::i32_type(true),
			}
		}

		ty
	}

	pub fn get_return_lvalue(&self) -> Option<LValue> {
		if self.ret.1.is_void() {
			None
		} else {
			Some(LValue {
				local: self.arg_count,
				projection: vec![],
				props: self.ret.0,
			})
		}
	}

	pub fn is_lang_function(&self, lang_item: &str) -> bool {
		self.attributes.iter().any(|attr| {
			if &attr.name != "lang" { 
				return false 
			}
			
			let [arg0] = attr.args.as_slice() else {
				return false
			};

			let [Token::Name(name)] = arg0.as_slice() else {
				return false
			};

			name == lang_item
		})
	}
}
