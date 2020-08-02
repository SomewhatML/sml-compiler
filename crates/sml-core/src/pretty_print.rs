use super::types::{Tycon, Type, TypeVar};
use super::{Const, Expr, ExprKind, Pat, PatKind, SortedRecord};
use sml_util::interner::{Interner, Symbol};
use std::collections::{HashMap, VecDeque};
use std::fmt::{self, Write};

pub struct PrettyPrinter<'a> {
    indent: usize,
    width: usize,
    max: usize,
    prev_max: Vec<usize>,
    interner: &'a Interner,
    commands: VecDeque<Command>,
}

#[derive(Debug)]
enum Command {
    Wrap(usize),
    Unwrap,
    Indent(usize),
    Dedent(usize),
    Text(String),
    Line,
}

impl fmt::Debug for PrettyPrinter<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrettyPrinter")
            .field("commands", &self.commands)
            .finish()
    }
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

    pub fn write<W: fmt::Write>(&mut self, w: &mut W) -> fmt::Result {
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
                        w.write_str(&s)?;
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
            _ => pp.text(pp.interner.get(*self).unwrap_or("?")),
        }
    }
}

impl<T: Print> Print for &SortedRecord<T> {
    fn print<'a, 'b>(&self, pp: &'a mut PrettyPrinter<'b>) -> &'a mut PrettyPrinter<'b> {
        if let Symbol::Tuple(_) = self.rows[0].label {
            pp.text("(");
            for (idx, row) in self.iter().enumerate() {
                pp.print(&row.data);
                if idx != self.rows.len() - 1 {
                    pp.text(", ");
                }
            }
            pp.text(")")
        } else {
            pp.text("{");
            for (idx, row) in self.iter().enumerate() {
                pp.print(&row.label).text(": ").print(&row.data);
                if idx != self.rows.len() - 1 {
                    pp.text(", ");
                }
            }
            pp.text("}")
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

impl<'a> Print for Pat<'a> {
    fn print<'c, 'b>(&self, pp: &'c mut PrettyPrinter<'b>) -> &'c mut PrettyPrinter<'b> {
        match &self.pat {
            PatKind::App(con, Some(pat)) => pp.print(&con.name).text(" ").print(pat),
            PatKind::App(con, None) => pp.print(&con.name),
            PatKind::Const(constant) => pp.print(&constant),
            PatKind::Record(record) => pp.print(&record),
            PatKind::Var(sym) => pp.print(sym),
            PatKind::Wild => pp.text("_"),
        }
    }
}

impl<'a> Print for Type<'a> {
    fn print<'c, 'b>(&self, pp: &'c mut PrettyPrinter<'b>) -> &'c mut PrettyPrinter<'b> {
        let mut map = HashMap::new();
        self.print_rename(pp, &mut map)
    }
}

impl<'a> Type<'a> {
    fn print_rename<'b, 'c>(
        &self,
        pp: &'b mut PrettyPrinter<'c>,
        map: &mut HashMap<usize, String>,
    ) -> &'b mut PrettyPrinter<'c> {
        match self {
            Type::Con(tycon, args) => {
                if tycon == &crate::builtin::tycons::T_ARROW {
                    args[0].print_rename(pp, map).text(" -> ");
                    args[1].print_rename(pp, map)
                } else {
                    for arg in args {
                        arg.print_rename(pp, map).text(" ");
                    }
                    pp.print(&tycon.name)
                }
            }
            Type::Record(fields) => {
                if let Symbol::Tuple(_) = fields[0].label {
                    pp.text("(");
                    for (idx, row) in fields.iter().enumerate() {
                        row.data.print_rename(pp, map);
                        if idx != fields.rows.len() - 1 {
                            pp.text(", ");
                        }
                    }
                    pp.text(")")
                } else {
                    pp.text("{");
                    for (idx, row) in fields.iter().enumerate() {
                        pp.print(&row.label).text(": ");
                        row.data.print_rename(pp, map);
                        if idx != fields.rows.len() - 1 {
                            pp.text(", ");
                        }
                    }
                    pp.text("}")
                }
            }
            Type::Var(tyvar) => match tyvar.ty() {
                Some(bound) => bound.print_rename(pp, map),
                None => match map.get(&tyvar.id) {
                    Some(s) => pp.text(s),
                    None => {
                        let x = map.len();
                        let last = ((x % 26) as u8 + 'a' as u8) as char;
                        let name = format!(
                            "'{}",
                            (0..x / 26)
                                .map(|_| 'z')
                                .chain(std::iter::once(last))
                                .collect::<String>()
                        );
                        pp.text(&name);
                        map.insert(tyvar.id, name);
                        pp
                    }
                },
            },
        }
    }
}
