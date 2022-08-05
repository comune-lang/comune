# Memory safety in Comune

One of Comune's main design goals is to provide a feature set that is "safe-by-default"; the default behaviour of language constructs and standard library features should never violate memory safety, and any code that does potentially subverts or overrides this default behaviour should be marked as such. 

In most use cases, using `unsafe` is not required. However, when a situation calls for it, unsafe features can give you more direct control over your code - at the expense of taking responsibility for its safety. The intent behind marking these features as `unsafe` is not necessarily to deter you from ever using them, but to ensure you know what you're getting into.