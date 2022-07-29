# comune
the comune programming language

*comune* is a compiled, high-level programming language heavily inspired by (and compatible with) *C++*. 

## motivation
if you're a decently experienced C++ developer, and you're anything like me, you probably have a love/hate relationship with the language. 

the freedom it offers in terms of writing performant high-level abstractions is practically unparalleled, while still keeping the developer "close to the metal", so to speak.
its extensive feature set, combined with its great performance (if used well), are some of the primary reasons it's been a mainstay in systems and performance-sensitive programming for decades.

unfortunately, it also sucks ass.

C++ is weighed down by *decades* of backwards compatibility requirements. any non-trivial problem added to the Standard **at any point** is likely to be there to stay,
and attempts to improve the language are met with incredible pushback from the Committee and the culture around it. the language's problems can't ever be fixed, merely swept under the rug in favour of adding *even more* new features. we still have `vector<bool>`, for god's sake.

rinse and repeat for 40 years, and you get C++. the best programming language in the world, buried under 20 metric tons of shit.

using C++ is not hard. using it *well* is basically impossible. enter *comune*.

## what is comune?

it says it right at the top. come on, man.

anyway, comune is a personal project of mine to revamp the C++ language from the ground up, taking bits and pieces from other languages (particularly Rust) where appropriate.

maybe it's better to show you an example. behold:

```cpp
// main.cmn
using std::io::println;

int main() {
    println("Hello chat");
    return 0;
}
```

riveting, right?

in comune, the `using` statement serves a couple of purposes:
- importing module items with `using your_module_name_here::some_item;`
- creating type aliases with `using your_type_alias = whatever::long_type::you_might::need<i32>;`

the modules feature, like the rest of the build system, is highly influenced by Rust. module paths are deterministic, and compilation can be partially parallelized (gathering type information from imported modules is required before compiling). 

> note: several major language features (like modules) are still WIP, and the semantics and behaviour are seriously subject to change.

