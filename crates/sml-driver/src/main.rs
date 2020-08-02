use sml_core::elaborate::Context;
use sml_core::pretty_print::PrettyPrinter;
use sml_frontend::parser::Parser;
use sml_util::diagnostics::{Diagnostic, Level};
use sml_util::interner::*;
use std::env;
use std::io::prelude::*;
use std::time::Instant;

pub struct Compiler<'a> {
    arena: &'a sml_core::arenas::CoreArena<'a>,
    interner: Interner,
    measure: bool,
    print_types: bool,
}

#[derive(Default)]
struct CompilerBuilder {
    measure: Option<bool>,
    print_types: Option<bool>,
}

impl CompilerBuilder {
    pub fn build<'a>(self, arena: &'a sml_core::arenas::CoreArena<'a>) -> Compiler<'a> {
        Compiler {
            arena,
            interner: Interner::with_capacity(4096),
            measure: self.measure.unwrap_or(false),
            print_types: self.print_types.unwrap_or(false),
        }
    }

    pub fn print_types(mut self, val: bool) -> Self {
        self.print_types = Some(val);
        self
    }

    pub fn measure(mut self, val: bool) -> Self {
        self.measure = Some(val);
        self
    }
}

fn report(diags: Vec<Diagnostic>, src: &str) {
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

    eprintln!("{} warnings, {} errors", warns.len(), errs.len());
    if !bugs.is_empty() {
        for diag in bugs {
            eprintln!("BUG {}", diag.report(&src));
        }
        panic!("aborting due to internal compiler bugs!");
    }

    for diag in warns {
        println!("{}", diag.report(&src));
    }

    for diag in errs {
        println!("{}", diag.report(&src));
    }
}

impl<'a> Compiler<'a> {
    fn run(&mut self, src: &str) {
        let mut p = Parser::new(src, &mut self.interner);
        let res = p.parse_decl();
        let mut diags = p.diags;

        match res {
            Ok(d) => {
                let (decls, diags) = sml_core::elaborate::check_and_elaborate(self.arena, &d);
                if self.print_types {
                    let mut buffer = String::new();
                    for decl in &decls {
                        let mut pp = PrettyPrinter::new(&self.interner, Box::new(&mut buffer));
                        use sml_core::pretty_print::Print;
                        use sml_core::{Decl, Rule};
                        use std::fmt::Write;

                        pp.test();
                        dbg!(&pp);
                        println!("{}", pp.run_command());

                        match decl {
                            Decl::Val(Rule { pat, .. }) => {
                                pat.print(&mut pp);
                                write!(pp, ": ");
                                pat.ty.print(&mut pp);
                            }
                            Decl::Fun(_, binds) => {
                                for (name, lam) in binds {
                                    pp.print_symbol(*name);
                                    write!(pp, ": ");

                                    lam.ty.print(&mut pp);
                                    write!(pp, " -> ");
                                    lam.body.ty.print(&mut pp);
                                }
                            }
                            _ => continue,
                        }
                        pp.newline();
                    }
                    println!("{}", buffer);
                }
                report(diags, &src)
            }
            Err(e) => {
                diags.insert(0, e.to_diagnostic());
                report(diags, &src)
            }
        }
    }
}

fn main() {
    let owned_arena = sml_core::arenas::OwnedCoreArena::new();
    let borrow = owned_arena.borrow();

    let args = env::args();
    if args.len() > 1 {
        for f in args.skip(1) {
            let file = std::fs::read_to_string(&f).unwrap();
            CompilerBuilder::default().build(&borrow).run(&file);
        }
        return;
    }

    println!("SomewhatML (c) 2020");
    loop {
        let mut buffer = String::new();
        print!("repl: ");
        std::io::stdout().flush().unwrap();
        std::io::stdin().read_to_string(&mut buffer).unwrap();

        CompilerBuilder::default()
            .print_types(true)
            .build(&borrow)
            .run(&buffer);
    }
}
