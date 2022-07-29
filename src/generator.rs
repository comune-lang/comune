use crate::parser::ast::ASTNode;

trait Generator {
	fn generate(node: ASTNode);
}