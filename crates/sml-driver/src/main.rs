use sml_frontend::parser::Parser;
use sml_util::interner::*;
use std::io::prelude::*;

fn main() {
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
