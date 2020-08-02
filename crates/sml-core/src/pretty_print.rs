use super::types::{Tycon, Type, TypeVar};
use super::{Const, Expr, ExprKind, Pat, PatKind, SortedRecord};
use sml_util::interner::{Interner, Symbol};
use std::collections::{HashMap, VecDeque};
use std::fmt::{self, Write};

// pub enum Doc {
//     Nil,
//     Line,
//     Text(String),
//     Nest(usize, Box<Doc>),
//     Group(Box<Doc>),
//     Append(Vec<Doc>),
// }

// #[derive(Default)]
// pub struct Document {
//     docs: Vec<Doc>,
// }

// impl Document {
//     pub fn nil(&mut self) -> &mut Self {
//         self.docs.push(Doc::Nil);
//         self
//     }

//     pub fn line(&mut self) -> &mut Self {
//         self.docs.push(Doc::Line);
//         self
//     }

//     pub fn text<S: AsRef<str>>(&mut self, s: S) -> &mut Self {
//         self.docs.push(Doc::Text(s.as_ref().into()));
//         self
//     }

//     pub fn nest<F>(&mut self, depth: usize, f: F) -> &mut Self
//         where F: Fn(&mut Document) -> Document
//     {
//         let mut inner = Document::default();
//         let docs = f(&mut inner).docs;
//         self.docs.push(Doc::Nest(depth, Box::new(Doc::Append(docs))));
//         self
//     }

//     pub fn group<F>(&mut self, f: F) -> &mut Self
//         where F: Fn(&mut Document) -> Document
//     {
//         let mut inner = Document::default();
//         let docs = f(&mut inner).docs;
//         self.docs.push(Doc::Group(Box::new(Doc::Append(docs))));
//         self
//     }
// }

// pub struct Formatter<'a> {
//     docs: Vec<Doc>,
//     width: usize,
//     indent: usize,

//     write: Box<dyn fmt::Write + 'a>,
// }

// impl<'a> Formatter<'a> {
//     pub fn best(&mut self) {
//         while let Some(doc) = self.docs.pop() {
//             use Doc::*;
//             match doc {
//                 Nil => continue,
//                 Append(docs) => {
//                     self.docs.extend(docs);
//                 },
//                 Nest(depth, doc) => {
//                     self.indent += depth;
//                     self.docs.extend(doc);
//                 }
//                 _ => continue,
//             }
//         }
//     }
// }

pub struct PrettyPrinter<'a> {
    indent: usize,
    width: usize,
    max: usize,
    prev_max: Vec<usize>,
    interner: &'a Interner,
    write: Box<dyn fmt::Write + 'a>,
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
    pub fn new(interner: &'a Interner, write: Box<dyn fmt::Write + 'a>) -> PrettyPrinter<'a> {
        PrettyPrinter {
            width: 0,
            indent: 0,
            max: 120,
            prev_max: Vec::new(),
            write,
            interner,
            commands: VecDeque::new(),
        }
    }

    pub fn print_symbol(&mut self, sym: Symbol) -> fmt::Result {
        let repr = self.interner.get(sym).unwrap_or("?");
        write!(self.write, "{}", repr)
    }

    pub fn test(&mut self) {
        self.wrap(80, |pp| {
            pp.text("hello, world")
                .line()
                .text("goodbye, world")
                .nest(2, |pp| pp.line().text("indent!"))
        });
    }

    pub fn run_command(&mut self) -> String {
        let mut buffer = String::new();
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
                    write!(&mut buffer, "\n{}", spaces);
                    self.width = self.indent;
                }
                Text(s) => {
                    if self.width + s.len() >= self.max {
                        let spaces = (0..self.indent).map(|_| ' ').collect::<String>();
                        write!(&mut buffer, "\n{}{}", spaces, s);
                        self.width = self.indent + s.len();
                    } else {
                        self.width += s.len();
                        buffer.write_str(&s);
                    }
                }
            }
        }
        buffer
    }

    fn indent(&mut self) {
        self.indent += 1;
    }

    fn dedent(&mut self) {
        self.indent -= 1;
    }

    fn wrap<F>(&mut self, width: usize, f: F) -> &mut Self
    where
        for<'b> F: Fn(&'b mut PrettyPrinter<'a>) -> &'b mut PrettyPrinter<'a>,
    {
        self.commands.push_back(Command::Wrap(width));
        f(self);
        self.commands.push_back(Command::Unwrap);
        self
    }

    fn nest<F>(&mut self, width: usize, f: F) -> &mut Self
    where
        for<'b> F: Fn(&'b mut PrettyPrinter<'a>) -> &'b mut PrettyPrinter<'a>,
    {
        self.commands.push_back(Command::Indent(width));
        f(self);
        self.commands.push_back(Command::Dedent(width));
        self
    }

    fn line(&mut self) -> &mut Self {
        self.commands.push_back(Command::Line);
        self
    }

    fn text<S: AsRef<str>>(&mut self, s: S) -> &mut Self {
        self.commands.push_back(Command::Text(s.as_ref().into()));
        self
    }
    // fn text<(&mut self, s: S)

    pub fn newline(&mut self) -> fmt::Result {
        let spaces = (0..self.indent * 2).map(|_| ' ').collect::<String>();
        writeln!(self.write, "\n{}", spaces)
    }
}

impl fmt::Write for PrettyPrinter<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.write.write_str(s)
    }
}

pub trait Print {
    fn print(&self, printer: &mut PrettyPrinter<'_>) -> fmt::Result;
}

impl<T: Print> Print for SortedRecord<T> {
    fn print(&self, printer: &mut PrettyPrinter<'_>) -> fmt::Result {
        printer.write_str("{{")?;
        for (idx, row) in self.iter().enumerate() {
            printer.print_symbol(row.label)?;
            printer.write_str(": ")?;
            row.data.print(printer)?;
            if idx != self.rows.len() {
                printer.write_str(",")?;
            }
        }
        printer.write_str("}}")
    }
}

impl Print for Const {
    fn print(&self, printer: &mut PrettyPrinter<'_>) -> fmt::Result {
        match self {
            Const::Unit => printer.write_str("()"),
            Const::Char(c) => write!(printer, "#'{}'", c),
            Const::String(s) => {
                printer.write_char('"')?;
                printer.print_symbol(*s)?;
                printer.write_char('"')
            }
            Const::Int(i) => write!(printer, "{}", i),
        }
    }
}

impl<'a> Print for Pat<'a> {
    fn print(&self, printer: &mut PrettyPrinter<'_>) -> fmt::Result {
        match &self.pat {
            PatKind::App(con, Some(pat)) => {
                printer.print_symbol(con.name)?;
                printer.write_str(" ")?;
                pat.print(printer)
            }
            PatKind::App(con, None) => printer.print_symbol(con.name),
            PatKind::Const(constant) => constant.print(printer),
            PatKind::Record(record) => record.print(printer),
            PatKind::Var(sym) => printer.print_symbol(*sym),
            PatKind::Wild => printer.write_str("_"),
        }
    }
}

impl<'a> Print for Type<'a> {
    fn print(&self, printer: &mut PrettyPrinter<'_>) -> fmt::Result {
        let mut map = HashMap::new();
        self.print_rename(printer, &mut map)
    }
}

impl<'a> Type<'a> {
    fn print_rename(
        &self,
        printer: &mut PrettyPrinter<'_>,
        map: &mut HashMap<usize, String>,
    ) -> fmt::Result {
        match self {
            Type::Con(tycon, args) => {
                for arg in args {
                    arg.print_rename(printer, map)?;
                    printer.write_str(" ")?;
                }
                printer.print_symbol(tycon.name)
            }
            Type::Record(fields) => {
                printer.write_str("{{")?;
                for row in fields.iter() {
                    printer.print_symbol(row.label)?;
                    printer.write_str(": ")?;
                    row.data.print_rename(printer, map)?;
                    printer.write_str(",")?;
                }
                printer.write_str("}}")
            }
            Type::Var(tyvar) => match tyvar.ty() {
                Some(bound) => bound.print_rename(printer, map),
                None => match map.get(&tyvar.id) {
                    Some(s) => write!(printer, "{}", s),
                    None => {
                        let x = map.len();
                        let last = ((x % 26) as u8 + 'a' as u8) as char;
                        let name = (0..x / 26)
                            .map(|_| 'z')
                            .chain(std::iter::once(last))
                            .collect::<String>();
                        write!(printer, "{}", name)?;
                        map.insert(tyvar.id, name);
                        Ok(())
                    }
                },
            },
        }
    }
}
