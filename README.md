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

to get rust-analyzer working in i.e. Visual Studio Code, pass in the same feature flag in the Workspace Settings:

![VS Code screenshot, showing a rust-analyzer "Check On Save: Extra Args" setting, with the value "--features=llvm12".](https://media.discordapp.net/attachments/846781793834106902/1056940581185650768/image.png)

# running
the input and build directories are currently hard-coded  (this ought to be factored out into a proper build tool sometime soon), meaning you can compile files from `test/src` into `test/build` with a simple `target/debug/comune filename.co` from the repo root. this is pretty hacky, but it works for now.

the intermediate build files will be output into `test/build/modules`, with the final binary being saved to `test/build/filename`. for a given module, the intermediate files are as follows:

- `.cir` - the initial cIR (comune Intermediate Representation), generated from the AST. this is not monomorphized, nor optimized (so it's pretty verbose), but it can be useful for debugging, and it's target-independent.
- `.cir_mono` - the monomorphized and optimized cIR, right before it goes into LLVM codegen. this is useful for diagnosing issues with cIR optimization and transformation passes, as well as monomorphization issues.
- `.ll_raw` - the plain, unoptimized LLVM IR emitted by the compiler. i apologize for the state of this. useful for debugging LLVM codegen issues.
- `.ll` - the optimized LLVM IR. in debug builds, this won't be very different from the `.ll_raw` stage, but it can still be useful for sanity-checking the IR as a whole - if code is being optimized away that shouldn't be, it's likely the IR codegen is invoking Undefined Behaviour.

