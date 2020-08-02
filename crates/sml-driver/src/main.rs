use sml_core::elaborate::Context;
use sml_core::pretty_print::PrettyPrinter;
use sml_frontend::parser::Parser;
use sml_util::diagnostics::{Diagnostic, Level};
use sml_util::interner::*;
use std::io::prelude::*;
use std::time::Instant;

mod config;
use config::{ArgParse, CompilerBuilder};

fn report(verb: u8, diags: Vec<Diagnostic>, src: &str) {
    let mut warns = Vec::new();
    let mut errs = Vec::new();
    let mut bugs = Vec::new();

    for diag in diags {
        match diag.level {
            Level::Warn => warns.push(diag),
            Level::Error => errs.push(diag),
            Level::Bug => bugs.push(diag),
        }
    }

    if !warns.is_empty() || !errs.is_empty() {
        println!("{} warnings, {} errors", warns.len(), errs.len());
    }

    if !bugs.is_empty() {
        for diag in bugs {
            eprintln!("BUG {}", diag.report(verb, &src));
        }
        panic!("aborting due to internal compiler bugs!");
    }

    for diag in warns {
        eprintln!("{}", diag.report(verb, &src));
    }

    for diag in errs {
        eprintln!("{}", diag.report(verb, &src));
    }
}

pub struct Compiler<'a> {
    arena: &'a sml_core::arenas::CoreArena<'a>,
    elab: sml_core::elaborate::Context<'a>,
    interner: Interner,
    measure: bool,
    verbosity: u8,
    times: Vec<String>,
}

impl<'a> Compiler<'a> {
    fn measure<T, F: FnMut(&mut Compiler<'a>) -> T>(&mut self, name: &str, mut f: F) -> T {
        if self.measure {
            let start = Instant::now();
            let r = f(self);
            let stop = Instant::now().duration_since(start).as_micros();
            self.times.push(format!("Phase: {}, {} us", name, stop));
            r
        } else {
            f(self)
        }
    }

    fn run(&mut self, src: &str) {
        let (res, mut diags) = self.measure("parsing", |c| {
            let mut p = Parser::new(src, &mut c.interner);
            (p.parse_decl(), p.diags)
        });

        let sio = std::io::stdout();
        let mut out = sio.lock();
        match res {
            Ok(d) => {
                let mut check = sml_core::check::Check::default();
                self.measure("checking", |c| check.check_decl(&d));
                diags.extend(check.diags);

                let decls = self.measure("elaboration", |c| c.elab.elaborate_decl(&d));
                diags.extend(std::mem::replace(&mut self.elab.diags, Vec::new()));

                match self.verbosity {
                    0 => {}
                    1 => {
                        // Print only types
                        let mut pp = PrettyPrinter::new(&self.interner);
                        for decl in &decls {
                            use sml_core::{Decl, Rule};
                            match decl {
                                Decl::Val(Rule { pat, .. }) => {
                                    pp.text("val ").print(pat).text(": ").print(pat.ty).line();
                                }
                                Decl::Fun(_, binds) => {
                                    for (name, lam) in binds {
                                        pp.text("val ")
                                            .print(name)
                                            .text(": ")
                                            .print(self.arena.types.arrow(lam.ty, lam.body.ty))
                                            .line();
                                    }
                                }
                                _ => {}
                            }
                            pp.write(&mut out).unwrap();
                            out.flush().unwrap();
                        }
                    }
                    _ => {
                        let mut pp = PrettyPrinter::new(&self.interner);
                        for decl in &decls {
                            pp.print(decl);
                            pp.write(&mut out).unwrap();
                            out.flush().unwrap();
                        }
                    }
                }
                writeln!(out, "").unwrap();
                report(self.verbosity, diags, &src)
            }
            Err(e) => {
                diags.insert(0, e.to_diagnostic());
                report(self.verbosity, diags, &src)
            }
        }
    }
}

fn main() {
    let owned_arena = sml_core::arenas::OwnedCoreArena::new();
    let borrow = owned_arena.borrow();

    let args = std::env::args();
    if args.len() > 1 {
        let ArgParse { builder, files } = ArgParse::parse(args);
        let mut compiler = builder.build(&borrow);
        for f in files {
            let file = std::fs::read_to_string(&f).unwrap();
            compiler.run(&file);
        }
        for time in compiler.times {
            println!("{}", time);
        }
        return;
    }

    println!("SomewhatML (c) 2020");
    let mut compiler = CompilerBuilder::default().verbosity(2).build(&borrow);
    loop {
        let mut buffer = String::new();
        print!("repl: ");
        std::io::stdout().flush().unwrap();
        std::io::stdin().read_to_string(&mut buffer).unwrap();

        compiler.run(&buffer);
    }
}
