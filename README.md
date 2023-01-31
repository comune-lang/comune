<p align="center">
  <img width="700" src="https://media.discordapp.net/attachments/846781793834106902/1036645719827820684/comune-logo-background.png"><br><br>
</p>

# the comune programming language
**comune** is a general-purpose programming language, designed as a gradual successor to C++.

# requirements

the compiler is currently implemented in Rust, with plans to self-host in the future.

what you'll need:

- Rust 1.65+ (stable)
- LLVM 12.0, 13.0, or 14.0

# building
comune is a simple `cargo` project, though you are required to pass in a feature flag matching the version of LLVM installed on your system. for instance:

```$ cargo build --features=llvm12```

on Windows, getting LLVM set up for development can be a veritable nightmare, so i recommend using WSL.

to get rust-analyzer working in i.e. Visual Studio Code, pass in the same feature flag in the Workspace Settings.

# running
to run the debug build, simply invoke `target/debug/comune` from the repo root. invoking the compiler with `--help` will provide a basic overview of the available command-line options.

the compiler takes a list of input files, as well as any modules they import, and compiles them into the specified output types (by default, an executable). the output types can be specified with `--emit`, and the valid options include:

- `bin` - an executable binary (the default if unspecified)
- `lib` - a static library
- `dylib` - a dynamic library
- `obj` - an object file
- `cir` - the initial cIR (comune Intermediate Representation), generated from the AST. this is not monomorphized, nor optimized (so it's pretty verbose), but it can be useful for debugging, and it's target-independent.
- `cirmono` - the monomorphized and optimized cIR, right before it goes into LLVM codegen. this is useful for diagnosing issues with cIR optimization and transformation passes, as well as monomorphization issues.
- `llraw` - the plain, unoptimized LLVM IR emitted by the compiler. i apologize for the state of this. useful for debugging LLVM codegen issues.
- `ll` - the optimized LLVM IR. in debug builds, this won't be very different from the `.ll_raw` stage, but it can still be useful for sanity-checking the IR as a whole - if code is being optimized away that shouldn't be, it's likely the IR codegen is invoking Undefined Behaviour.

the compiler accepts any non-empty list of these options, and emits them into the directory specified by `--out-dir` (by default the current working directory). for output types that involve invoking the linker (`bin`, `lib` and `dylib`), the output filename can be specified with `--output` or `-o`. the default is `a.out`.
