use sml_util::interner::{Interner, Symbol};
use std::collections::VecDeque;
use std::fmt;
use std::io::prelude::*;

mod ast;
mod core;

pub struct PrettyPrinter<'a> {
    indent: usize,
    width: usize,
    max: usize,
    prev_max: Vec<usize>,
    interner: &'a Interner,
    commands: VecDeque<Command>,
}

enum Command {
    Wrap(usize),
    Unwrap,
    Indent(usize),
    Dedent(usize),
    Text(String),
    Line,
}

impl<'a> PrettyPrinter<'a> {
    pub fn new(interner: &'a Interner) -> PrettyPrinter<'a> {
        PrettyPrinter {
            width: 0,
            indent: 0,
            max: 120,
            prev_max: Vec::new(),
            interner,
            commands: VecDeque::new(),
        }
    }

    pub fn test(&mut self) {
        self.wrap(20, |pp| {
            pp.text("case")
                .text("x")
                .nest(2, |pp| pp.line().text("of _ => bar"))
                .nest(3, |pp| {
                    pp.line().nest(2, |pp| {
                        pp.text("| _ => foo")
                            .text("bar baz qux")
                            .text(" flub ")
                            .text(" mosoaic")
                    })
                })
                .line()
                .text("goodbye")
                .text(",")
                .text("world")
                .nest(2, |pp| pp.line().text("indent!").text("is fun!"))
        });
    }

    pub fn write<W: std::io::Write>(&mut self, w: &mut W) -> std::io::Result<()> {
        while let Some(cmd) = self.commands.pop_front() {
            use Command::*;
            match cmd {
                Indent(w) => {
                    self.indent += w;
                }
                Dedent(w) => {
                    self.indent -= w;
                }
                Wrap(width) => {
                    self.prev_max.push(self.max);
                    self.max = width;
                }
                Unwrap => {
                    // should never fail anyway
                    self.max = self.prev_max.pop().unwrap_or(120);
                }
                Line => {
                    if self.width == self.indent {
                        continue;
                    }
                    let spaces = (0..self.indent).map(|_| ' ').collect::<String>();
                    write!(w, "\n{}", spaces)?;
                    self.width = self.indent;
                }
                Text(s) => {
                    if self.width + s.len() >= self.max {
                        let spaces = (0..self.indent).map(|_| ' ').collect::<String>();
                        write!(w, "\n{}{}", spaces, s)?;
                        self.width = self.indent + s.len();
                    } else {
                        self.width += s.len();
                        write!(w, "{}", s)?;
                    }
                }
            }
        }
        Ok(())
    }

    pub fn wrap<F>(&mut self, width: usize, f: F) -> &mut Self
    where
        for<'b> F: Fn(&'b mut PrettyPrinter<'a>) -> &'b mut PrettyPrinter<'a>,
    {
        self.commands.push_back(Command::Wrap(width));
        f(self);
        self.commands.push_back(Command::Unwrap);
        self
    }

    pub fn nest<F>(&mut self, width: usize, f: F) -> &mut Self
    where
        for<'b> F: Fn(&'b mut PrettyPrinter<'a>) -> &'b mut PrettyPrinter<'a>,
    {
        self.commands.push_back(Command::Indent(width));
        f(self);
        self.commands.push_back(Command::Dedent(width));
        self
    }

    pub fn line(&mut self) -> &mut Self {
        self.commands.push_back(Command::Line);
        self
    }

    pub fn text<S: AsRef<str>>(&mut self, s: S) -> &mut Self {
        self.commands.push_back(Command::Text(s.as_ref().into()));
        self
    }

    pub fn print<P: Print>(&mut self, p: &P) -> &mut Self {
        p.print(self)
    }
}

fn fresh_name(x: u32) -> String {
    let last = ((x % 26) as u8 + 'a' as u8) as char;
    (0..x / 26)
        .map(|_| 'z')
        .chain(std::iter::once(last))
        .collect::<String>()
}

pub trait Print {
    fn print<'a, 'b>(&self, pp: &'a mut PrettyPrinter<'b>) -> &'a mut PrettyPrinter<'b>;
}

impl Print for Symbol {
    fn print<'a, 'b>(&self, pp: &'a mut PrettyPrinter<'b>) -> &'a mut PrettyPrinter<'b> {
        match self {
            Symbol::Tuple(n) => pp.text(n.to_string()),
            Symbol::Gensym(n) => pp.text(fresh_name(*n % 100)),
            _ => pp.text(pp.interner.get(*self).unwrap_or("?")),
        }
    }
}
