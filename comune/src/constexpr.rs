use crate::semantic::expression::Expr;


#[derive(Clone, Debug, PartialEq)]
pub enum ConstExpr {
	Expr(Expr),
	Result(ConstValue),
}

#[derive(Clone, Debug, PartialEq)]
pub enum ConstValue {

}