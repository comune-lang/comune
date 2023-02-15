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
	Binding(Binding), // Binding pattern, matches any value. If None, it's a wildcard
	Destructure(Vec<(Option<Name>, Pattern)>, Type), // Destructures an aggregate type into its constituents
	Or(Vec<Pattern>, Type),                          // Combines two or more patterns
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
				for (_, elem_pat) in elems {
					result.append(&mut elem_pat.get_bindings());
				}
				result
			}

			Pattern::Or(_, _) => todo!(),
		}
	}
}
