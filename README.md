# sml-compiler

A tutorial implementation of a compiler for a modified dialect (no module system) of Standard ML. I do not make any guarantees about the correctness of the compiler (although obviously I prefer it to be correct), as this is mostly meant as an educational exercise.

We take an approach similar to MLton, where we will be performing whole-program compilation and monomorphization

## Roadmap

- [X] Parser
- [X] Syntax checking
- [X] Elaboration and type reconstruction
- [X] Match compilation
- [ ] Monomorphization
- [ ] SSA transformation
- [ ] Optimization passes
- [ ] Native code generation


### Features

All of the core term language of Standard ML is supported. In addition, we support
type checking of flexible record patterns, and values subject to the value restriction
with the largest possible scope

```sml
fun extract {x, y, ...} = (x, y)

(* this is fine, extract will be given the type signature matching the record below *)
val (x, _) = extract {x = 10, y = 12, z = false}

```