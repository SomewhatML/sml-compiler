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
                    let mut ctx = Context::new();
                    let start = Instant::now();
                    match ctx.elaborate_decl(&d) {
                        Ok(_) => {
                            let stop = start.elapsed().as_micros();
                            println!("elaboration {} us", stop);
                        }
                        Err(e) => {
                            println!("[err] {:?}", e);
                        }
                    }

                    // if !diags.is_empty() {
                    //     println!("[err] {:?}", diags);
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
                println!("{:?}", d);
                match ctx.elaborate_decl(&d) {
                    Ok(d) => println!("Ok {:?}", d),
                    Err(diag) => println!("{}", diag.report(&buffer)),
                }
            }
            Err(e) => {
                println!("[err] {:?}: {:?}", e.to_diagnostic().report(&buffer), diags);
            }
        }
    }
}
