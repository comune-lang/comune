
enum CIRExpr {
	Atom(Type, CIRAtom),
	Cons(Operator, [(Type, CIRAtom); 2]),
}


enum CIRAtom {
	FnCall(String, Vec<CIRExpr>)
}


enum CIRStmt {
	Expression(Type, CIRExpr),
	Assignment(Type, CIRExpr),
	Jump(usize),
}


type CIRBlock = Vec<CIRStmt>;


struct CIRFunction {
	pub blocks: Vec<CIRBlock>,
}