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


### Compilation speeds

Current speeds as of 6/30/2020:

For a 10k line file:

Lexing and parsing takes ~10 ms
Elaboration and type reconstruction takes ~30ms

Moving to an arena allocator for the CoreML language takes us down to around ~35 ms for elaboration
