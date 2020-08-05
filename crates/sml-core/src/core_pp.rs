use crate::types::Type;
use crate::{Decl, Expr, ExprKind, Pat, PatKind, Rule, SortedRecord};
use sml_util::interner::Symbol;
use sml_util::pretty_print::{PrettyPrinter, Print};

use std::{cell::Cell, collections::HashMap};

impl<T: Print> Print for &SortedRecord<T> {
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
                pp.print(&row.label).text("= ").print(&row.data);
                if idx != self.len() - 1 {
                    pp.text(", ");
                }
            }
            pp.text("}")
        }
    }
}

impl<'a> Print for Pat<'a> {
    fn print<'c, 'b>(&self, pp: &'c mut PrettyPrinter<'b>) -> &'c mut PrettyPrinter<'b> {
        match &self.kind {
            PatKind::App(con, Some(pat)) => pp.print(&con.get().name).text(" ").print(pat),
            PatKind::App(con, None) => pp.print(&con.get().name),
            PatKind::Const(constant) => pp.print(&constant),
            PatKind::Record(record) => pp.print(&record),
            PatKind::Var(sym) => pp.print(&sym.get()),
            PatKind::Wild => pp.text("_"),
        }
    }
}

impl<'a> Print for Expr<'a> {
    fn print<'b, 'c>(&self, pp: &'b mut PrettyPrinter<'c>) -> &'b mut PrettyPrinter<'c> {
        use ExprKind::*;
        match &self.kind {
            App(e1, e2) => pp.print(e1).text(" ").print(e2),
            Case(casee, rules) => pp.nest(2, |pp| {
                pp.line().text("case ").print(casee).nest(2, |pp| {
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
            }),
            Con(con, tys) => pp.print(&con.get().name),
            Const(c) => pp.print(&c),
            Handle(tryy, sym, handler) => pp
                .print(tryy)
                .text("handle ")
                .print(&sym.get())
                .text(" with ")
                .print(handler),
            Lambda(lam) => pp
                .text("fn ")
                .print(&lam.get().arg)
                .text(" => ")
                .print(&lam.get().body),
            Let(decls, body) => pp.nest(2, |pp| {
                pp.line()
                    .text("let")
                    .nest(2, |pp| {
                        for decl in decls {
                            pp.print(decl);
                        }
                        pp
                    })
                    .line()
                    .text("in ")
                    .nest(2, |pp| pp.line().print(body))
                    .line()
                    .text("end")
            }),
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
            Record(rows) => {
                let rec = SortedRecord::new_unchecked(rows.clone());
                pp.print(&&rec)
            }
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
            Var(s) => pp.print(&s.get()),
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
    pub fn print_rename<'b, 'c>(
        &self,
        pp: &'b mut PrettyPrinter<'c>,
        map: &mut HashMap<usize, String>,
    ) -> &'b mut PrettyPrinter<'c> {
        match self {
            Type::Con(tycon, args) => {
                let tycon = tycon.get();
                if tycon == crate::builtin::tycons::T_ARROW {
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
                    for (idx, row) in fields.iter().enumerate() {
                        row.data.print_rename(pp, map);
                        if idx != fields.rows.len() - 1 {
                            pp.text(" * ");
                        }
                    }
                    pp
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
                        let last = ((x % 26) as u8 + b'a' as u8) as char;
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
            Type::Flex(flex) => match flex.ty() {
                Some(ty) => ty.print_rename(pp, map),
                None => {
                    pp.text("{");
                    for row in flex.constraints.iter() {
                        pp.print(&row.label).text(": ");
                        row.data.print_rename(pp, map);
                        pp.text(", ");
                    }
                    pp.text("... }")
                }
            },
        }
    }
}

fn print_tyvars<'b, 'c>(
    ids: &[usize],
    map: &mut HashMap<usize, String>,
    pp: &'b mut PrettyPrinter<'c>,
) -> &'b mut PrettyPrinter<'c> {
    match ids.len() {
        0 => pp,
        1 => {
            map.insert(ids[0], "'a".into());
            pp.text("'a ")
        }
        _ => {
            for (idx, tyvar) in ids.iter().enumerate() {
                let last = ((idx % 26) as u8 + b'a' as u8) as char;
                let name = format!(
                    "'{}",
                    (0..idx / 26)
                        .map(|_| 'z')
                        .chain(std::iter::once(last))
                        .collect::<String>()
                );
                pp.text(&name);
                map.insert(*tyvar, name);
                if idx != ids.len() - 1 {
                    pp.text(", ");
                }
            }
            pp.text(" ")
        }
    }
}

impl<'a> Print for Decl<'a> {
    fn print<'b, 'c>(&self, pp: &'b mut PrettyPrinter<'c>) -> &'b mut PrettyPrinter<'c> {
        let mut map = HashMap::new();
        match self {
            Decl::Val(vars, Rule { pat, expr }) => {
                pp.line().text("val ");
                print_tyvars(&vars, &mut map, pp)
                    .print(pat)
                    .text(": ")
                    .print(pat.ty)
                    .text(" = ")
                    .print(expr)
            }
            Decl::Fun(vars, binds) => {
                for (name, lam) in binds {
                    pp.line().text("val ");
                    print_tyvars(&vars, &mut map, pp)
                        .print(name)
                        .text(": ")
                        .print(&Type::Con(
                            Cell::new(crate::builtin::tycons::T_ARROW),
                            vec![lam.ty, lam.body.ty],
                        ))
                        .text(" = ")
                        .text("fn ")
                        .print(&lam.arg)
                        .text(" => ")
                        .print(&lam.body);
                }
                pp
            }
            Decl::Exn(con, Some(ty)) => pp
                .line()
                .text("exception ")
                .print(&con.name)
                .text(" of ")
                .print(*ty),
            Decl::Exn(con, None) => pp.text("exception ").print(&con.name),
            Decl::Datatype(dt) => {
                pp.line().text("datatype ");
                print_tyvars(&dt.tyvars, &mut map, pp)
                    .print(&dt.tycon.name)
                    .text(" = ");

                for (idx, con) in dt.constructors.iter().enumerate() {
                    match con {
                        (con, Some(ty)) => {
                            pp.print(&con.name).text(" of ");
                            ty.print_rename(pp, &mut map);
                        }
                        (con, None) => {
                            pp.print(&con.name);
                        }
                    }
                    if idx != dt.constructors.len().saturating_sub(1) {
                        pp.text(" | ");
                    }
                }
                pp
            }
        }
    }
}
