use crate::interner::{Interner, Symbol};
use crate::Const;
use std::collections::VecDeque;

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

    pub fn write_fmt<W: std::fmt::Write>(&mut self, w: &mut W) -> std::fmt::Result {
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

pub trait Print {
    fn print<'a, 'b>(&self, pp: &'a mut PrettyPrinter<'b>) -> &'a mut PrettyPrinter<'b>;
}

impl Print for Symbol {
    fn print<'a, 'b>(&self, pp: &'a mut PrettyPrinter<'b>) -> &'a mut PrettyPrinter<'b> {
        match self {
            Symbol::Tuple(n) => pp.text(n.to_string()),
            Symbol::Gensym(n) => pp.text(format!("x{}", n)),
            _ => pp.text(pp.interner.get(*self).unwrap_or("?")),
        }
    }
}

impl Print for &Const {
    fn print<'a, 'b>(&self, pp: &'a mut PrettyPrinter<'b>) -> &'a mut PrettyPrinter<'b> {
        match self {
            Const::Unit => pp.text("()"),
            Const::Char(c) => pp.text(format!("#'{}'", c)),
            Const::String(s) => pp.print(s),
            Const::Int(i) => pp.text(i.to_string()),
        }
    }
}

impl<T: std::fmt::Display> Print for T {
    fn print<'a, 'b>(&self, pp: &'a mut PrettyPrinter<'b>) -> &'a mut PrettyPrinter<'b> {
        pp.text(self.to_string())
    }
}
