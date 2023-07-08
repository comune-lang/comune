use std::{
	fmt::Write as _,
	fs::{self, File},
	io::{self, Read, Write},
	path::PathBuf,
	process::Command,
	sync::{mpsc::Sender, Arc},
};

use crate::{
	ast::{
		get_attribute,
		module::{Identifier, ModuleImportKind, ModuleInterface, ModuleItemInterface},
		types::{Basic, FloatSize, IntSize, TupleKind, Type, TypeDef},
	},
	driver::{await_imports_ready, get_module_out_path, CompilerState, ModuleState},
	errors::{CMNMessageLog, ComuneError},
	get_file_suffix,
};

pub fn compile_cpp_module(
	state: Arc<CompilerState>,
	src_path: PathBuf,
	module_name: &Identifier,
	error_sender: Sender<CMNMessageLog>,
	s: &rayon::Scope,
) -> Result<(), ComuneError> {
	let out_path = get_module_out_path(&state, &module_name);
	let processed_path = out_path.with_extension("cpp");

	let (cpp_source, deps) = preprocess_cpp_file(&state, &src_path).unwrap();

	// Temporarily write processed source to build dir

	let mut cpp_out = File::create(&processed_path).unwrap();
	cpp_out.write_all(cpp_source.as_bytes()).unwrap();

	// Generate C++ headers for comune dependencies
	let modules = deps
		.into_iter()
		.map(|module| {
			ModuleImportKind::Extern(Identifier::from_name(
				get_file_suffix(&module).unwrap(),
				false,
			))
		})
		.collect();

	let interfaces = await_imports_ready(&state, &src_path, module_name, modules, error_sender, s)?;

	for (name, interface) in interfaces {
		let header = generate_cpp_header(&state, &interface.interface).unwrap();
		let mut header_out = File::create(
			out_path
				.with_file_name(name.to_string())
				.with_extension("hpp"),
		)
		.unwrap();

		header_out.write_all(header.as_bytes()).unwrap();
	}

	// Invoke clang via CLI

	let mut output = Command::new("clang");

	output
		.arg(processed_path.clone())
		.arg("-c")
		.arg("-funsigned-char")
		.arg("-fdiagnostics-color=always")
		.arg("-I./libcomune/cpp/")
		.arg("--output")
		.arg(out_path.with_extension("o"));

	let output_result = output.output().expect("fatal: failed to invoke clang");

	io::stdout().write_all(&output_result.stdout).unwrap();
	io::stderr().write_all(&output_result.stderr).unwrap();

	if output_result.status.success() {
		// This just writes an empty comune interface for now,
		// leaving the C++ code not directly accessible from comune.
		// TODO: Implement a C++->comune interface, probably using libclang
		state.module_states.write().unwrap().insert(
			src_path,
			ModuleState::InterfaceComplete(Arc::new(ModuleInterface {
				is_typed: true, // hack to make some assertions pass
				..Default::default()
			})),
		);
	} else {
		state
			.module_states
			.write()
			.unwrap()
			.insert(src_path, ModuleState::ParsingFailed);
	}

	fs::remove_file(processed_path).unwrap();

	Ok(())
}

pub fn preprocess_cpp_file(
	_state: &Arc<CompilerState>,
	file: &PathBuf,
) -> io::Result<(String, Vec<PathBuf>)> {
	let mut file_in = String::new();

	File::open(file)?.read_to_string(&mut file_in)?;

	// Make input file buffer immutable
	let file_in = file_in;
	let mut result = String::with_capacity(file_in.len());
	let mut dependencies = vec![];

	for line in file_in.lines() {
		if line.starts_with("co_import") {
			let mut dep_path = file.clone();

			let left = line.find('"').unwrap() + 1;
			let right = line.rfind('.').unwrap();

			dep_path.set_file_name(String::from(&line[left..right]));
			dep_path.set_extension("co");

			dependencies.push(dep_path);

			result.push_str(
				&line
					.replace("co_import", "#include")
					.replace(".co\";", ".hpp\""),
			);
		} else {
			result.push_str(line);
		}
		result.push('\n');
	}

	Ok((result, dependencies))
}

// generate a C++ header file from a comune ModuleInterface
//
// this might be among the worst things i've ever written!
// if you can think of a less horrible approach to this
// problem, you are MORE than welcome to give it a shot
//
pub fn generate_cpp_header(
	_state: &Arc<CompilerState>,
	input: &ModuleInterface,
) -> Result<String, std::fmt::Error> {
	let mut result = String::from("#pragma once\n\n#include \"bridge/bridge.hpp\"\n\n");

	// Write type declarations first
	for (name, item) in &input.children {
		match item {
			ModuleItemInterface::Type(def) => {
				generate_cpp_type(name, &def.read().unwrap(), &mut result, true)?;
			}

			ModuleItemInterface::TypeAlias(aliased) => {
				write!(result, "typedef ")?;

				aliased.read().unwrap().cpp_format(&mut result)?;

				writeln!(result, " {name};\n")?;
			}

			_ => {}
		}
	}

	for (name, item) in &input.children {
		match item {
			ModuleItemInterface::Functions(fns) => {
				for func in &*fns.read().unwrap() {
					if get_attribute(&func.attributes, "no_mangle").is_some() {
						write!(result, "extern \"C\" ")?;
					}

					func.ret.1.cpp_format(&mut result)?;

					write!(result, " {name}")?;

					if !func.generics.is_empty() {
						let mut iter = func.generics.params.iter();

						write!(result, "<{}", iter.next().unwrap().0)?;

						for (param, ..) in iter {
							write!(result, ", {param}")?;
						}

						write!(result, ">")?;
					}

					write!(result, "(")?;

					if func.params.params.is_empty() {
						if func.params.variadic {
							write!(result, "...")?; // Is this even legal?? who knows
						}
					} else {
						let mut iter = func.params.params.iter();

						iter.next().unwrap().0.cpp_format(&mut result)?;

						for (param, ..) in iter {
							write!(result, ", ")?;
							param.cpp_format(&mut result)?;
						}

						if func.params.variadic {
							write!(result, ", ...")?;
						}
					}

					write!(result, ");\n\n")?;
				}
			}

			ModuleItemInterface::Type(_) | ModuleItemInterface::TypeAlias(_) => {}

			_ => {
				write!(result, "// (unimplemented: {name})\n\n")?;
			}
		}
	}

	Ok(result)
}

fn generate_cpp_type(
	name: &Identifier,
	def: &TypeDef,
	result: &mut impl std::fmt::Write,
	generate_body: bool,
) -> std::fmt::Result {
	// check if the typedef has type parameters

	if !def.generics.is_empty() {
		let mut iter = def.generics.params.iter();

		write!(result, "template<typename {}", iter.next().unwrap().0)?;

		for (param, ..) in iter {
			write!(result, ", typename {param}")?;
		}

		write!(result, "> ")?;
	}

	write!(result, "class {name}")?;

	if generate_body {
		writeln!(result, " {{")?;

		for (name, ty, _) in &def.members {
			write!(result, "\t")?;

			ty.cpp_format(result)?;

			writeln!(result, " {name};")?;
		}

		write!(result, "}}")?;
	}

	writeln!(result, ";\n")
}

impl Type {
	fn cpp_format(&self, f: &mut impl std::fmt::Write) -> std::fmt::Result {
		match self {
			Type::Basic(basic) => match basic {
				Basic::Bool => write!(f, "bool"),
				Basic::Float {
					size: FloatSize::F32,
				} => write!(f, "float"),
				Basic::Float {
					size: FloatSize::F64,
				} => write!(f, "double"),
				Basic::Void => write!(f, "void"),

				Basic::Integral { signed, size } => {
					write!(
						f,
						"{}int{}_t",
						if *signed { "" } else { "u" },
						match size {
							IntSize::IAddr => "ptr",
							IntSize::I64 => "64",
							IntSize::I32 => "32",
							IntSize::I16 => "16",
							IntSize::I8 => "8",
						},
					)
				}
			},

			Type::Unresolved {
				name, generic_args: type_args, ..
			} => {
				write!(f, "{name}")?;

				if !type_args.is_empty() {
					let mut iter = type_args.iter();

					write!(f, "<")?;
					iter.next().unwrap().get_type_arg().cpp_format(f)?;

					for arg in iter {
						write!(f, ", ")?;
						arg.get_type_arg().cpp_format(f)?;
					}

					write!(f, ">")?;
				}
				Ok(())
			}

			Type::Pointer { pointee, mutable } => {
				pointee.cpp_format(f)?;

				if *mutable {
					write!(f, "*")
				} else {
					write!(f, " const*")
				}
			}

			Type::Function(ret, args) => {
				ret.cpp_format(f)?;
				write!(f, "(*)(")?;

				if !args.is_empty() {
					let mut iter = args.iter();

					iter.next().unwrap().1.cpp_format(f)?;

					for (_, arg) in args {
						write!(f, ", ")?;
						arg.cpp_format(f)?;
					}
				}

				write!(f, ")")
			}

			Type::Tuple(TupleKind::Sum, types) => {
				write!(f, "union {{ ")?;

				for (i, ty) in types.iter().enumerate() {
					ty.cpp_format(f)?;
					write!(f, " _{i}; ")?;
				}

				write!(f, "}}")
			}

			_ => write!(f, "int /* <= TODO */"),
		}
	}
}
