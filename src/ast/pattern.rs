use std::fmt::Display;

use crate::lexer::SrcSpan;

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
	Destructure {
		patterns: Vec<(Name, Pattern)>, 
		pattern_ty: Type,
		exhaustive: bool,
		span: SrcSpan,
	},

	// Combines two or more patterns
	Or(Vec<Pattern>, Type),
}

impl Pattern {
	pub fn get_type(&self) -> &Type {
		match self {
			Pattern::Binding(Binding { ty, .. })
			| Pattern::Destructure { pattern_ty: ty, .. }
			| Pattern::Or(_, ty) => ty,
		}
	}

	pub fn get_type_mut(&mut self) -> &mut Type {
		match self {
			Pattern::Binding(Binding { ty, .. })
			| Pattern::Destructure { pattern_ty: ty, .. }
			| Pattern::Or(_, ty) => ty,
		}
	}

	pub fn get_span(&self) -> SrcSpan {
		match self {
			Pattern::Binding(binding) => binding.props.span,
			
			Pattern::Destructure { span, .. } => *span,

			Pattern::Or(patterns, _) => match patterns.as_slice() {
				[l, .., r] => l.get_span().union(r.get_span()),
				[single] => single.get_span(),
				[] => SrcSpan::new(),	
			}
		}
	}

	pub fn get_bindings(&self) -> Vec<&Binding> {
		match self {
			Pattern::Binding(binding) => vec![binding],

			Pattern::Destructure { patterns, .. } => {
				let mut result = vec![];

				for elem_pat in patterns {
					result.append(&mut elem_pat.1.get_bindings());
				}

				result
			}

			Pattern::Or(_, _) => todo!(),
		}
	}
}

impl Display for Pattern {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Pattern::Binding(binding) => write!(f, "{binding}"),

			Pattern::Or(patterns, ty) => {
				write!(f, "{ty} (")?;
				
				for (i, pattern) in patterns.iter().enumerate() {
					if i != 0 {
						write!(f, ", ")?;
					}

					write!(f, "{pattern}")?;
				}

				write!(f, ")")
			}

			Pattern::Destructure { patterns, pattern_ty, exhaustive, .. } => {
				write!(f, "{pattern_ty} {{")?;

				for (i, (name, pattern)) in patterns.iter().enumerate() {
					if i != 0 { write!(f, ", ")? }

					write!(f, "{name}: {pattern}")?;
				}

				if !exhaustive {
					write!(f, ", ..")?;
				}

				write!(f, "}}")
			}
		}
	}
}

impl Display for Binding {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if let Some(name) = &self.name {
			write!(f, "{}{} {}", self.ty, self.props, name)
		} else {
			write!(f, "{}{} _", self.ty, self.props)
		}
	}
}