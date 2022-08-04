# Motivation

**Comune is a programming language designed to be a successor to C++.**

I know, shocking, right? There's been many attempts to finally slay that godforsaken beast of a language over the years, to varying degrees of success. [Rust](https://www.rust-lang.org/) comes to mind as the current prime example, being a fantastic language with an amazing community and ecosystem which I frankly cannot recommend enough. **If at all possible, you should be using Rust.** You'll be doing yourself -and everyone using your software- a service. Hell, both the Comune compiler AND this book are written using Rust!

...However.

I wouldn't be writing this if I were content using Rust.

Rust is wonderful. Its design is ingenious, and although the learning curve is a little sharp at first, it's a joy to use once it clicks. But the ecosystem simply isn't there. C++ has the benefit of damn-near four decades of support. *Everything* is written in either C or C++, and while Rust has some support for C interop, the language's design is just too different to allow for easy high-level integration with C++ constructs. Speaking of: Rust's focus on safety and explicitness, in my opinion, prevent it from reaching the same level of expressiveness I use C++ for. 

So, with these things in mind, I started sketching up some design goals for my own little language:

- Expressive, familiar C-like syntax, with a focus on readability
- A large feature set for creating performant, high-level abstractions
- Competitive performance, using LLVM as the compiler backend
- *Seriously* improved error messages, especially concerning generics
- High-level integration with C++ constructs, allowing for gradual adoption
- A Rust-inspired "it just works" build system, with easy dependency management
- Memory safety: Not capital-S Safe, but safe-by-default
- Some additional nice features from Rust, if appropriate

In essence, we're taking C++, trimming the fat, sanding off the rough edges, and adding a bunch of QoL features from modern languages, particulary (you guessed it) Rust.

Without further ado, let's get into it!