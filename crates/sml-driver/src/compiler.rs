use sml_core::elaborate::Context;
use sml_frontend::parser::Parser;
use sml_util::diagnostics::{Diagnostic, Level};
use sml_util::interner::*;
use sml_util::pretty_print::{PrettyPrinter, Print};
use std::io::prelude::*;
use std::time::Instant;

use stats_alloc::{Region, StatsAlloc, INSTRUMENTED_SYSTEM};
use std::alloc::System;

#[global_allocator]
static GLOBAL: &StatsAlloc<System> = &INSTRUMENTED_SYSTEM;

#[derive(Copy, Clone, Default, Debug, Ord, PartialOrd, Eq, PartialEq)]
pub struct FileId(pub usize);

pub struct Compiler<'a> {
    pub src: String,
    pub arena: &'a sml_core::arenas::CoreArena<'a>,
    pub elab: Context<'a>,
    pub interner: Interner,
    pub measure: bool,
    pub verbosity: u8,
    pub stop_phase: String,
    pub times: Vec<String>,
}

pub trait Phase<'a> {
    type Input;
    type Output;
    const PHASE: &'static str;

    fn pass(
        &self,
        ctx: &mut Compiler<'a>,
        input: Self::Input,
    ) -> Result<Self::Output, Vec<Diagnostic>>;

    fn output(&self, _: &mut Compiler<'a>, _: Self::Output) {}
}

struct Parse;
struct Elaborate;
struct Monomorphize;

impl<'a> Phase<'a> for Parse {
    type Input = FileId;
    type Output = (sml_frontend::ast::Decl, Vec<Diagnostic>);
    const PHASE: &'static str = "parse";

    fn pass(
        &self,
        ctx: &mut Compiler<'a>,
        _: Self::Input,
    ) -> Result<Self::Output, Vec<Diagnostic>> {
        let mut p = Parser::new(&ctx.src, &mut ctx.interner);

        match p.parse_decl() {
            Ok(decl) => Ok((decl, p.diags)),
            Err(e) => {
                let mut diags = p.diags;
                diags.push(e.to_diagnostic());
                Err(diags)
            }
        }
    }
}

impl<'a> Phase<'a> for Elaborate {
    type Input = (sml_frontend::ast::Decl, Vec<Diagnostic>);
    type Output = Vec<sml_core::Decl<'a>>;
    const PHASE: &'static str = "elaborate";

    fn pass(
        &self,
        ctx: &mut Compiler<'a>,
        input: Self::Input,
    ) -> Result<Self::Output, Vec<Diagnostic>> {
        let (decl, mut diags) = input;
        let mut check = sml_core::check::Check::new(&ctx.interner);
        check.check_decl(&decl);
        diags.extend(check.diags);

        let decls = ctx.elab.elaborate_decl(&decl);
        diags.extend(ctx.elab.diagnostics(&ctx.interner));

        for diag in &diags {
            match diag.level {
                Level::Error => return Err(diags),
                Level::Bug => return Err(diags),
                _ => continue,
            }
        }

        // only have warnings
        report(ctx.verbosity, diags, &ctx.src);

        Ok(decls)
    }

    fn output(&self, ctx: &mut Compiler<'a>, data: Self::Output) {
        print_core_decl(ctx, &data)
    }
}

impl<'a> Phase<'a> for Monomorphize {
    type Input = Vec<sml_core::Decl<'a>>;
    type Output = Vec<sml_core::Decl<'a>>;
    const PHASE: &'static str = "monomorphize";

    fn pass(
        &self,
        ctx: &mut Compiler<'a>,
        input: Self::Input,
    ) -> Result<Self::Output, Vec<Diagnostic>> {
        let mut alpha = sml_core::alpha::Rename::new(&ctx.arena);
        let mut pp = PrettyPrinter::new(&ctx.interner);
        let decls = input
            .iter()
            .map(|decl| alpha.visit_decl(decl, &mut pp))
            .collect();

        // alpha.dump_cache(&mut pp);
        Ok(decls)
    }

    fn output(&self, ctx: &mut Compiler<'a>, data: Self::Output) {
        print_core_decl(ctx, &data)
    }
}

impl<'a> Compiler<'a> {
    fn measure<T, F: FnOnce(&mut Compiler<'a>) -> T>(&mut self, name: &str, f: F) -> T {
        if self.measure {
            let region = Region::new(&GLOBAL);
            let start = Instant::now();
            let r = f(self);
            let stop = Instant::now().duration_since(start).as_micros();
            let stats = region.change();
            self.times.push(format!(
                "Phase: {}, {} us. {} allocations, {} allocated",
                name, stop, stats.allocations, stats.bytes_allocated
            ));
            r
        } else {
            f(self)
        }
    }

    /// Run the phase if `self.stop_phase` is not equal to the phase
    fn run_phase<P: Phase<'a>>(&mut self, phase: P, input: P::Input) -> Option<P::Output> {
        let res = self.measure(P::PHASE, |ctx| phase.pass(ctx, input));
        match res {
            Ok(out) => {
                if self.stop_phase == P::PHASE {
                    phase.output(self, out);
                    return None;
                }
                Some(out)
            }
            Err(diags) => {
                report(self.verbosity, diags, &self.src);
                None
            }
        }
    }

    pub fn run(&mut self, input: String) -> Option<()> {
        self.src = input;
        let input = self.run_phase(Parse, FileId(0))?;
        let input = self.run_phase(Elaborate, input)?;
        let input = self.run_phase(Monomorphize, input)?;

        Monomorphize.output(self, input);
        Some(())
    }
}

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

    let io = std::io::stderr();
    let mut out = io.lock();

    if !bugs.is_empty() {
        for diag in bugs {
            let _ = writeln!(out, "BUG {}", diag.report(verb, &src));
        }
        panic!("aborting due to internal compiler bugs!");
    }

    for diag in warns {
        let _ = writeln!(out, "{}", diag.report(verb, &src));
    }

    for diag in errs {
        let _ = writeln!(out, "{}", diag.report(verb, &src));
    }
}

fn print_core_decl<'a>(ctx: &Compiler<'a>, decls: &[sml_core::Decl<'a>]) {
    let io = std::io::stdout();
    let mut out = io.lock();
    match ctx.verbosity {
        0 => {}
        1 => {
            // Print only types
            let mut pp = PrettyPrinter::new(&ctx.interner);
            for decl in decls {
                use sml_core::{Decl, Rule};
                match decl {
                    Decl::Val(_, Rule { pat, .. }) => {
                        pp.text("val ").print(pat).text(": ").print(pat.ty).line();
                    }
                    Decl::Fun(_, binds) => {
                        for (name, lam) in binds {
                            pp.text("val ")
                                .print(name)
                                .text(": ")
                                .print(ctx.arena.types.arrow(lam.ty, lam.body.ty))
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
            let mut pp = PrettyPrinter::new(&ctx.interner);
            for decl in decls {
                pp.print(decl);
                pp.write(&mut out).unwrap();
                out.flush().unwrap();
            }
        }
    }
    writeln!(out, "").unwrap();
}
