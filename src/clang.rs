use std::{sync::{Arc, mpsc::Sender}, path::PathBuf, fs::{File, self}, fmt::Write as _, io::{Write, self, Read}, process::Command};

use crate::{driver::{ManagerState, get_module_out_path, ModuleState, await_imports_ready}, ast::{module::{Identifier, ModuleImportKind, ModuleInterface, ModuleItemInterface, ItemRef}, types::{Type, Basic, TypeDefKind}}, errors::{CMNMessageLog, ComuneError}, get_file_suffix};


pub fn compile_cpp_module(
	state: Arc<ManagerState>,
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
	let modules = 
		deps
		.into_iter()
		.map(|module| ModuleImportKind::Extern(
			Identifier::from_name(get_file_suffix(&module).unwrap(), false)
		))
		.collect();
	
	let interfaces = await_imports_ready(&state, &src_path, module_name, modules, error_sender, s)?;

	for (name, interface) in interfaces {
		let header = generate_cpp_header(&state, &interface).unwrap();
		let mut header_out = File::create(out_path.with_file_name(&name).with_extension("hpp")).unwrap();

		header_out.write_all(header.as_bytes()).unwrap();
	}

	// Invoke clang via CLI

	let mut output = Command::new("clang");

	output
		.arg(processed_path.clone())
		.arg("-c")
		.arg("-fdiagnostics-color=always")
		.arg("-I./libcomune/cpp/")
		.arg("--output")
		.arg(out_path.with_extension("o"));

	let output_result = output.output().expect("fatal: failed to invoke clang");
	
	if !output_result.status.success() {
		println!("");
		io::stdout().write_all(&output_result.stdout).unwrap();
		io::stderr().write_all(&output_result.stderr).unwrap();
		println!("");
	}

	// This just writes an empty comune interface for now, 
	// leaving the C++ code not directly accessible from comune.
	// TODO: Implement a C++->comune interface, probably using libclang
	state
		.module_states
		.write()
		.unwrap()
		.insert(src_path.clone(), ModuleState::InterfaceComplete(Arc::default()));
	
	fs::remove_file(processed_path).unwrap();

	Ok(())
}

pub fn preprocess_cpp_file(_state: &Arc<ManagerState>, file: &PathBuf) -> io::Result<(String, Vec<PathBuf>)> {
	let mut file_in = String::new();
	
	File::open(file)?.read_to_string(&mut file_in)?;
	
	// Make input file buffer immutable
	let file_in = file_in;
	let mut result = String::with_capacity(file_in.len());
	let mut dependencies = vec![];

	for line in file_in.lines() {
		if line.starts_with("#co_include") {
			let mut dep_path = file.clone();
			
			let left = line.find('"').unwrap() + 1;
			let right = line.rfind('.').unwrap();

			dep_path.set_file_name(String::from(&line[left..right]));
			dep_path.set_extension("co");

			dependencies.push(dep_path);

			result.push_str(&line.replace("#co_include", "#include").replace(".co", ".hpp"));
		} else {
			result.push_str(line);
		}
		result.push('\n');
	}
	
	Ok((result, dependencies))
}

pub fn generate_cpp_header(_state: &Arc<ManagerState>, input: &ModuleInterface) -> Result<String, std::fmt::Error> {
	let mut result = format!("#include \"bridge/bridge.hpp\"\n\n");

	// Write type declarations first
	for (name, item) in &input.children {
		match item {
			ModuleItemInterface::Type(def) => {
			
				match &def.read().unwrap().def {
					TypeDefKind::Algebraic(alg) => {
						if !alg.params.is_empty() {
							let mut iter = alg.params.iter();

							write!(result, "template<typename {}", iter.next().unwrap().0)?;
							
							for (param, ..) in iter {
								write!(result, ", typename {param}")?;
							}

							write!(result, "> ")?;
						}
					}
	
					_ => todo!()
				}

				writeln!(result, "class {name};")?;
			}

			ModuleItemInterface::TypeAlias(aliased) => {
				write!(result, "typedef ")?;
				
				aliased.read().unwrap().cpp_format(&mut result)?;
				
				writeln!(result, " {name};")?;
			}

			_ => {}
		}
	}

	for (name, item) in &input.children {
		match item {
			ModuleItemInterface::Functions(fns) => {
				for func in fns {
					let func = &*func.read().unwrap();
				
					func.ret.cpp_format(&mut result)?;
					write!(result, " {name}")?;
					
					if !func.type_params.is_empty() {
						let mut iter = func.type_params.iter();

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

			ModuleItemInterface::Type(_) => {}

			_ => {
				write!(result, "// (unimplemented: {name})\n\n")?;
			}
		}
	}

	Ok(result)
}

impl Type {
	fn cpp_format(&self, f: &mut impl std::fmt::Write) -> std::fmt::Result {
		match self {
			Type::Basic(basic) => {
				match basic {
					Basic::Bool => write!(f, "bool"),
					Basic::Char => write!(f, "uint32_t"),
					Basic::Float { size_bytes: 4 } => write!(f, "float"),
					Basic::Float { size_bytes: 8 } => write!(f, "double"),
					Basic::Float { size_bytes: _ } => panic!(),
					Basic::Void => write!(f, "void"),

					Basic::Integral { signed, size_bytes } => {
						write!(f, "{}int{}_t",
							if *signed {
								""
							} else {
								"u"
							},
							size_bytes * 8,
						)
					}
					
					Basic::PtrSizeInt { signed: true } => write!(f, "intptr_t"),
					Basic::PtrSizeInt { signed: false } => write!(f, "uintptr_t"),
					
					Basic::Str => todo!(),
				}
			}

			Type::TypeRef(ItemRef::Unresolved {
				name, type_args, ..
			}) => {
				write!(f, "{name}")?;
				
				if !type_args.is_empty() {
					let mut iter = type_args.iter();
				
					write!(f, "<")?;
					iter.next().unwrap().cpp_format(f)?;
					
					for arg in iter {
						write!(f, ", ")?;
						arg.cpp_format(f)?;
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

			_ => write!(f, "int /* <= TODO */"),
		}
	}
}