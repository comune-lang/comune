use super::{types::Type, namespace::Name};


#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
	Binding(Option<Name>, Type),						// Binding pattern, matches any value. If None, it's a wildcard
	Destructure(Vec<(Option<Name>, Pattern)>, Type),	// Destructures an aggregate type into its constituents
	Or(Vec<Pattern>, Type),								// Combines two or more patterns
}

impl Pattern {
	pub fn get_type(&self) -> &Type {
		match self {
			Pattern::Binding(_, ty) | Pattern::Destructure(_, ty) | Pattern::Or(_, ty) => ty
		}
	}
}