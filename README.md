# sml-compiler

This is a WIP compiler targeting the core term language of Standard ML '97 (i.e. no structures/signatures). The goal is to first get a source -> machine code pipeline working, then perhaps go back and add in the ML module system.

We take an approach similar to MLton, where we will be performing whole-program compilation and monomorphization
