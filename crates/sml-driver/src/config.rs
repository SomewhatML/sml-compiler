use super::*;
use std::env;

#[derive(Copy, Clone, Debug, PartialEq, Ord, PartialOrd, Eq)]
pub enum Phase {
    Parse,
    Elaborate,
    Monomorphize,
}

#[derive(Default)]
pub struct CompilerBuilder {
    measure: Option<bool>,
    verbosity: Option<u8>,
    phase: Option<Phase>,
}

impl CompilerBuilder {
    pub fn build<'a>(self, arena: &'a sml_core::arenas::CoreArena<'a>) -> Compiler<'a> {
        Compiler {
            arena,
            elab: sml_core::elaborate::Context::new(arena),
            interner: Interner::with_capacity(4096),
            measure: self.measure.unwrap_or(false),
            verbosity: self.verbosity.unwrap_or(0),
            current_phase: Phase::Parse,
            stop_phase: self.phase,
            times: Vec::new(),
        }
    }

    pub fn verbosity(mut self, val: u8) -> Self {
        self.verbosity = Some(val);
        self
    }

    pub fn measure(mut self, val: bool) -> Self {
        self.measure = Some(val);
        self
    }

    pub fn phase(mut self, val: Phase) -> Self {
        self.phase = Some(val);
        self
    }
}

pub struct ArgParse {
    pub builder: CompilerBuilder,
    pub files: Vec<String>,
}

impl ArgParse {
    pub fn parse(args: env::Args) -> ArgParse {
        let mut stack = args.skip(1).rev().collect::<Vec<String>>();
        let mut files = Vec::new();
        let mut builder = CompilerBuilder::default();
        while !stack.is_empty() {
            let item = stack.pop().unwrap();
            if item.starts_with("--") {
                match item.as_ref() {
                    "--silent" => {
                        builder = builder.verbosity(0);
                    }
                    "--v" => {
                        builder = builder.verbosity(1);
                    }
                    "--vv" => {
                        builder = builder.verbosity(2);
                    }
                    "--measure" => {
                        builder = builder.measure(true);
                    }
                    "--phase" => {
                        let phase =
                            match stack.pop().expect("expected phase after --phase").as_ref() {
                                "parse" => Phase::Parse,
                                "elab" => Phase::Elaborate,
                                "mono" => Phase::Monomorphize,
                                item => panic!("unrecognized compiler phase: {}", item),
                            };
                        builder = builder.phase(phase);
                    }
                    _ => panic!("unrecognized compiler flag: {}", item),
                }
            } else {
                files.push(item);
            }
        }

        ArgParse { builder, files }
    }
}
