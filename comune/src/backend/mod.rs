use crate::parser::ast::ASTElem;

mod llvm;

trait Generator {
	fn generate(node: ASTElem);
}