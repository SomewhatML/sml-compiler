# sml-compiler

This is a WIP compiler targeting the core term language of Standard ML '97 (i.e. no structures/signatures). The goal is to first get a source -> machine code pipeline working, then perhaps go back and add in the ML module system.

We take an approach similar to MLton, where we will be performing whole-program compilation and monomorphization


Current speeds as of 6/30/2020:

For a 10k line file:

Lexing and parsing takes ~23 ms
Elaboration and type reconstruction takes ~45ms