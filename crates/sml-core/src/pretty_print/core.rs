use super::{PrettyPrinter, Print, Symbol};
use crate::types::Type;
use crate::{Const, Decl, Expr, ExprKind, Pat, PatKind, Row, Rule};

use std::collections::HashMap;

impl<T: Print> Print for &[Row<T>] {
    fn print<'a, 'b>(&self, pp: &'a mut PrettyPrinter<'b>) -> &'a mut PrettyPrinter<'b> {
        if let Symbol::Tuple(_) = self[0].label {
            pp.text("(");
            for (idx, row) in self.iter().enumerate() {
                pp.print(&row.data);
                if idx != self.len() - 1 {
                    pp.text(", ");
                }
            }
            pp.text(")")
        } else {
            pp.text("{");
            for (idx, row) in self.iter().enumerate() {
                pp.print(&row.label).text(": ").print(&row.data);
                if idx != self.len() - 1 {
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
            PatKind::Record(record) => pp.print(&record.rows.as_slice()),
            PatKind::Var(sym) => pp.print(sym),
            PatKind::Wild => pp.text("_"),
        }
    }
}

impl<'a> Print for Expr<'a> {
    fn print<'b, 'c>(&self, pp: &'b mut PrettyPrinter<'c>) -> &'b mut PrettyPrinter<'c> {
        use ExprKind::*;
        match &self.expr {
            App(e1, e2) => pp.print(e1).text(" ").print(e2),
            Case(casee, rules) => {
                pp.text("case ").print(casee).nest(2, |pp| {
                    pp.line()
                        .text("of ")
                        .print(&rules[0].pat)
                        .text(" => ")
                        .print(&rules[0].expr)
                });
                for rule in rules.iter().skip(1) {
                    pp.nest(3, |pp| {
                        pp.line().nest(2, |pp| {
                            pp.text("| ")
                                .print(&rule.pat)
                                .text(" => ")
                                .print(&rule.expr)
                        })
                    });
                }
                pp
            }
            Con(con, tys) => pp.print(&con.name),
            Const(c) => pp.print(&c),
            Handle(tryy, sym, handler) => pp
                .print(tryy)
                .text("handle ")
                .print(sym)
                .text(" with ")
                .print(handler),
            Lambda(lam) => pp.text("fn ").print(&lam.arg).text(" => ").print(&lam.body),
            Let(decls, body) => pp
                .text("let")
                .line()
                .nest(2, |pp| {
                    for decl in decls {
                        pp.print(decl).line();
                    }
                    pp
                })
                .text("in")
                .line()
                .nest(2, |pp| pp.print(body).line())
                .line()
                .text("end")
                .line(),
            List(exprs) => {
                pp.text("[");
                for (idx, expr) in exprs.iter().enumerate() {
                    pp.print(expr);
                    if idx != exprs.len().saturating_sub(1) {
                        pp.text(", ");
                    }
                }
                pp.text("]")
            }
            Primitive(sym) => pp.print(sym),
            Raise(e) => pp.text("raise ").print(e),
            Record(rows) => pp.print(&rows.as_slice()),
            Seq(exprs) => {
                pp.text("(");
                for (idx, expr) in exprs.iter().enumerate() {
                    pp.print(expr);
                    if idx != exprs.len().saturating_sub(1) {
                        pp.text("; ");
                    }
                }
                pp.text(")")
            }
            Var(s) => pp.print(s),
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

impl<'a> Print for Decl<'a> {
    fn print<'b, 'c>(&self, pp: &'b mut PrettyPrinter<'c>) -> &'b mut PrettyPrinter<'c> {
        match self {
            Decl::Val(Rule { pat, .. }) => {
                pp.text("val ").print(pat).text(": ").print(pat.ty).line()
            }
            Decl::Fun(_, binds) => {
                for (name, lam) in binds {
                    pp.text("val ")
                        .print(name)
                        .text(": ")
                        .print(&Type::Con(
                            crate::builtin::tycons::T_ARROW,
                            vec![lam.ty, lam.body.ty],
                        ))
                        .line();
                }
                pp
            }
            _ => pp,
        }
    }
}
