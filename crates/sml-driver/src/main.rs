use sml_frontend::parser::Parser;
use sml_util::interner::*;
use std::env;
use std::io::prelude::*;
use std::time::Instant;

fn main() {
    let args = env::args();
    if args.len() > 1 {
        for f in args.skip(1) {
            println!("reading {}", f);
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
                    println!("{} us", micros);
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
                // ctx.elaborate_decl(&d).unwrap();
                // dbg!(&ctx);
                // let elab1 = ctx.elab_program(d);
                // let inlined = hir::inline(&elab1);
                // println!("====> {:?}", &elab1);
                // ctx.dump();
            }
            Err(e) => {
                println!("[err] {:?}: {:?}", e.to_diagnostic(), diags);
            }
        }
    }
}
