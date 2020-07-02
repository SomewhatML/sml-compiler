use sml_core::elaborate::Context;
use sml_frontend::parser::Parser;
use sml_util::interner::*;
use std::env;
use std::io::prelude::*;
use std::time::Instant;

fn main() {
    let args = env::args();
    if args.len() > 1 {
        for f in args.skip(1) {
            // println!("reading {}", f);
            let file = std::fs::read_to_string(&f).unwrap();
            let (res, diags, micros) = INTERNER.with(|i| {
                let x = &mut i.borrow_mut();
                let mut p = Parser::new(&file, x);

                let start = Instant::now();
                let res = p.parse_decl();
                // let stop = Instant::now();
                let stop = start.elapsed().as_micros();

                (res, p.diags, stop)
            });

            match res {
                Ok(d) => {
                    println!("parsing {} us", micros);
                    let start = Instant::now();

                    let (decls, diags) = sml_core::elaborate::check_and_elaborate(&d);
                    let stop = start.elapsed().as_micros();

                    println!("elaboration {} us w/ {} errors", stop, diags.len());

                    // if !diags.is_empty() {
                    //     for diag in diags {
                    //         println!("Elaboration {}", diag.report(&file));
                    //     }
                    // }
                }
                Err(e) => {
                    println!("[err] {:?}: {:?}", e.to_diagnostic(), diags);
                }
            }
        }
        return;
    }

    let mut ctx = Context::new();
    println!("SimpleML (c) 2020");
    loop {
        let mut buffer = String::new();
        print!("repl: ");
        std::io::stdout().flush().unwrap();
        std::io::stdin().read_to_string(&mut buffer).unwrap();

        // loop {
        let (res, diags) = INTERNER.with(|i| {
            let x = &mut i.borrow_mut();
            let mut p = Parser::new(&buffer, x);
            (p.parse_decl(), p.diags)
        });

        match res {
            Ok(d) => {
                // println!("{:?}", d);
                let mut check = sml_core::check::Check::default();
                check.check_decl(&d);
                for d in check.diags {
                    println!("Syntax Checking {}", d.report(&buffer));
                }

                let decls = ctx.elaborate_decl(&d);
                println!("{:#?}", decls);

                if !diags.is_empty() {
                    for diag in diags {
                        println!("Parse {}", diag.report(&buffer));
                    }
                }

                if !ctx.diags.is_empty() {
                    let diags = std::mem::replace(&mut ctx.diags, Vec::new());
                    for diag in diags {
                        println!("Elaboration {}", diag.report(&buffer));
                    }
                }
            }
            Err(e) => {
                println!("Parse {}", e.to_diagnostic().report(&buffer));
                if !diags.is_empty() {
                    for diag in diags {
                        println!("Parse {}", diag.report(&buffer));
                    }
                }
            }
        }
    }
}
