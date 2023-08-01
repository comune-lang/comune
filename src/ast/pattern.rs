use super::{
	module::Name,
	types::{BindingProps, Type},
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Binding {
	pub name: Option<Name>,
	pub ty: Type,
	pub props: BindingProps,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
	// Binding pattern, matches any value. If `name` is None, it's a wildcard
	Binding(Binding),

	// Destructures an aggregate type into its constituents
	Destructure(Vec<Pattern>, Type),

	// Combines two or more patterns
	Or(Vec<Pattern>, Type),
}

impl Pattern {
	pub fn get_type(&self) -> &Type {
		match self {
			Pattern::Binding(Binding { ty, .. })
			| Pattern::Destructure(_, ty)
			| Pattern::Or(_, ty) => ty,
		}
	}

	pub fn get_bindings(&self) -> Vec<&Binding> {
		match self {
			Pattern::Binding(binding) => vec![binding],

			Pattern::Destructure(elems, _) => {
				let mut result = vec![];
				for elem_pat in elems {
					result.append(&mut elem_pat.get_bindings());
				}
				result
			}

			Pattern::Or(_, _) => todo!(),
		}
	}
}
