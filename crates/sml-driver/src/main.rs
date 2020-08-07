use sml_core::elaborate::Context;
use sml_frontend::parser::Parser;
use sml_util::diagnostics::{Diagnostic, Level};
use sml_util::interner::*;
use sml_util::pretty_print::PrettyPrinter;
use std::io::prelude::*;
use std::time::Instant;

mod compiler;
mod config;
use config::ArgParse;

fn main() {
    let owned_arena = sml_core::arenas::OwnedCoreArena::new();
    let borrow = owned_arena.borrow();

    let ArgParse { builder, files } = ArgParse::parse(std::env::args());
    let mut compiler = builder.build(&borrow);
    if !files.is_empty() {
        for f in files {
            let file = std::fs::read_to_string(&f).unwrap();
            compiler.run(file);
        }
        for time in compiler.times {
            println!("{}", time);
        }
        return;
    }

    println!("SomewhatML (c) 2020");
    loop {
        let mut buffer = String::new();
        print!("repl: ");
        std::io::stdout().flush().unwrap();
        std::io::stdin().read_to_string(&mut buffer).unwrap();

        compiler.run(buffer);
    }
}
