use super::types::Type;

struct PatternDecon {
	ctor: Constructor,
	fields: Vec<PatternDecon>,
	ty: Type,
}

enum Constructor {
	Single,
	Variant(usize),
	Opaque,
	Binding,
	Or,
}