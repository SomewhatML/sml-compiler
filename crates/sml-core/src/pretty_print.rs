use super::types::{Tycon, Type, TypeVar};
use super::{Const, Expr, ExprKind, Pat, PatKind, SortedRecord};
use sml_util::interner::{Interner, Symbol};
use std::collections::HashMap;
use std::fmt::{self, Write};

pub struct PrettyPrinter<'a> {
    indent: usize,
    spaces: usize,
    interner: &'a Interner,
    write: Box<dyn fmt::Write + 'a>,
}

impl<'a> PrettyPrinter<'a> {
    pub fn new(interner: &'a Interner, write: Box<dyn fmt::Write + 'a>) -> PrettyPrinter<'a> {
        PrettyPrinter {
            spaces: 2,
            indent: 0,
            write,
            interner,
        }
    }

    pub fn print_symbol(&mut self, sym: Symbol) -> fmt::Result {
        let repr = self.interner.get(sym).unwrap_or("?");
        write!(self.write, "{}", repr)
    }

    fn indent(&mut self) {
        self.indent += 1;
    }

    fn dedent(&mut self) {
        self.indent -= 1;
    }

    pub fn newline(&mut self) -> fmt::Result {
        let spaces = (0..self.indent * self.spaces)
            .map(|_| ' ')
            .collect::<String>();
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
