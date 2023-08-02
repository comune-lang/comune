<p align="center">
  <img width="700" src="https://media.discordapp.net/attachments/846781793834106902/1036645719827820684/comune-logo-background.png"><br><br>
</p>

# the comune programming language
**comune** is a general-purpose programming language, designed as a gradual successor to C++. it boasts many modern and powerful features, including static memory safety, an expression-based C-style syntax, type-checked generics, first-class support for sum types, a flexible pattern-matching system, and a highly parallelized compiler, while providing seamless C++ interop.

note: **comune is still heavily work-in-progress**, with many language features being partially implemented (if at all) and subject to change without notice. the compiler is suitable for experimentation and testing, but expect false errors, crashes, and miscompilation. 

# requirements

the compiler is currently implemented in Rust, with plans to self-host in the future.

what you'll need:

- Rust 1.65+ (stable)
- LLVM 12.0, 13.0, or 14.0 set up for development

# building
comune is a simple `cargo` project, though you are required to pass in a feature flag matching the version of LLVM installed on your system. for instance:

```$ cargo build --features=llvm12```

to get tools like rust-analyzer working in VS Code, pass in the same feature flag in the Workspace Settings.

on Windows, getting LLVM set up for development can be a veritable nightmare, so i recommend using WSL.

by default, the crate builds with the `concurrent` feature, which uses `rayon` for concurrent module compilation. this feature can optionally be disabled, which will remove the `rayon` dependency and use a single-threaded pipeline instead.

# running
to run the debug build, simply invoke `target/debug/comune` from the repo root. invoking the compiler with `--help` will provide a basic overview of the available command-line options. 

to compile anything, the compiler must know where to find the comune toolchain. this path is provided through the `COMUNE_TOOLCHAIN` environment variable, and when compiling from source, should just be the repository root.

the compiler takes a list of input files, as well as any modules they import, and compiles them into the specified output types (by default, an executable). the output types can be specified with `--emit`, and the valid options include:

- `bin` - an executable binary (the default if unspecified)
- `lib` - a static library
- `dylib` - a dynamic library
- `obj` - an object file
- `cir` - the initial cIR (comune Intermediate Representation), generated from the AST. this is not monomorphized, nor optimized (so it's pretty verbose), but it can be useful for debugging, and it's target-independent.
- `cirmono` - the monomorphized and optimized cIR, right before it goes into LLVM codegen. this is useful for diagnosing issues with cIR optimization and transformation passes, as well as monomorphization issues.
- `llraw` - the plain, unoptimized LLVM IR emitted by the compiler. i apologize for the state of this. useful for debugging LLVM codegen issues.
- `ll` - the optimized LLVM IR. in debug builds, this won't be very different from the `.ll_raw` stage, but it can still be useful for sanity-checking the IR as a whole - if code is being optimized away that shouldn't be, it's likely the IR codegen is invoking Undefined Behaviour.
- `none` - don't emit any build artifacts. this item is mutually exclusive with every other emit type. useful for i.e. running the compiler as a language server.

the compiler accepts any valid, non-empty list of these options, and emits them into the directory specified by `--out-dir` (by default the current working directory). for output types that involve invoking the linker (`bin`, `lib` and `dylib`), the output filename can be specified with `--output` or `-o`. the default is `a.out`.

# building the test code

the `test/src` folder contains basic comune code that tests various compiler features. to build this code after successfully compiling a debug build of the compiler, run the command `target/debug/comune test/src/main.co --out-dir=test/build` from the repository root. this will emit an executable `a.out` in the `test/build` directory, creating it if it does not exist. this executable can optionally be executed, in order to check for miscompilations due to compiler bugs.

additionally, the user may specify other output types to be emitted, as described above. these can be useful for debugging and verifying compiler behaviour.
