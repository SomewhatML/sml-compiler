//! Walk the AST and perform syntax checking, as defined in Section 2.9
//!
//! * No expression row, pat row, or type row may bind the same label twice
//! * valbind, typbind, datbind, exbinds may not bind the same identifier twice
//! * No tyvarseq may contain the same `tyvar` twice
//! * For each recursive `pat=exp` valbind, exp must be of the form `fn match`
//! * No datbind, valbind, or exnbind may bind `true`, `false`, `nil`, `::`, or
//!   `ref`
//! * No datbind or exnbind may bind `it`
//! * No real constant may occur in a pattern
//! * tyvarseqs across the same valbinds must be unique

use sml_frontend::ast::*;
use sml_util::diagnostics::Diagnostic;
use sml_util::interner::*;
use sml_util::span::Span;
use std::collections::{HashSet, VecDeque};

const BUILTIN_CONSTRUCTORS: [Symbol; 5] = [S_NIL, S_CONS, S_TRUE, S_FALSE, S_REF];

pub struct Check<'a> {
    interner: &'a Interner,
    pub diags: Vec<Diagnostic>,
}

impl<'a> Check<'a> {
    pub fn new(interner: &'a Interner) -> Self {
        Self {
            interner,
            diags: Vec::new(),
        }
    }

    fn check_pat(&mut self, pattern: &Pat) {
        use PatKind::*;
        let mut vars = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(pattern);
        while let Some(pat) = queue.pop_front() {
            match &pat.data {
                App(_, _) => unreachable!(),
                Ascribe(p, _) => {
                    queue.push_back(p);
                }
                Const(_) => {}
                FlatApp(pats) | List(pats) => {
                    for pat in pats {
                        queue.push_back(pat)
                    }
                }
                Record(rows, _) => {
                    self.check_rows(rows, |c, p| c.check_pat(p));
                }
                Variable(sym) => {
                    if !sym.builtin() {
                        if !vars.insert(*sym) {
                            self.diags.push(
                                Diagnostic::error(
                                    pattern.span,
                                    format!(
                                        "duplicate variable in pattern: '{}'",
                                        self.interner.get(*sym).unwrap_or("?")
                                    ),
                                )
                                .message(pat.span, "redefined here"),
                            );
                        }
                    }
                }
                Wild => {}
            }
        }
    }

    fn check_rows<T, F: FnMut(&mut Check, &T)>(&mut self, rows: &[Row<T>], mut f: F) {
        let mut set = HashSet::new();
        for row in rows {
            if !set.insert(row.label) {
                self.diags.push(Diagnostic::error(
                    row.span,
                    format!(
                        "duplicate record label: '{}'",
                        self.interner.get(row.label).unwrap_or("?")
                    ),
                ));
            }
            f(self, &row.data);
        }
    }

    fn check_expr(&mut self, expr: &Expr) {
        use ExprKind::*;
        match &expr.data {
            Andalso(e1, e2) => {
                self.check_expr(e1);
                self.check_expr(e2);
            }
            App(e1, e2) => {
                self.check_expr(e1);
                self.check_expr(e2);
            }
            Case(expr, rules) => {
                self.check_expr(expr);
                for rule in rules {
                    self.check_pat(&rule.pat);
                    self.check_expr(&rule.expr);
                }
            }
            Const(_) => {}
            Constraint(expr, _) => {
                self.check_expr(expr);
            }
            FlatApp(exprs) => {
                for expr in exprs {
                    self.check_expr(expr);
                }
            }
            Fn(rules) => {
                for rule in rules {
                    self.check_pat(&rule.pat);
                    self.check_expr(&rule.expr);
                }
            }
            Handle(expr, rules) => {
                self.check_expr(expr);
                for rule in rules {
                    self.check_pat(&rule.pat);
                    self.check_expr(&rule.expr);
                }
            }
            If(e1, e2, e3) => {
                self.check_expr(e1);
                self.check_expr(e2);
                self.check_expr(e3);
            }
            Let(decls, expr) => {
                for decl in decls {
                    self.check_decl(decl);
                }
                self.check_expr(expr);
            }
            List(exprs) => {
                for expr in exprs {
                    self.check_expr(expr);
                }
            }
            Orelse(e1, e2) => {
                self.check_expr(e1);
                self.check_expr(e2);
            }
            Primitive(_) => {}
            Raise(expr) => {
                self.check_expr(expr);
            }
            Record(rows) => {
                self.check_rows(rows, |c, e| c.check_expr(e));
            }
            Selector(_) => {}
            Seq(exprs) => {
                for expr in exprs {
                    self.check_expr(expr);
                }
            }
            Var(_) => {}
            While(_, _) => {
                self.diags
                    .push(Diagnostic::error(expr.span, "`while` exprs not supported"));
            }
        }
    }

    fn check_tyvars(&mut self, sp: Span, tyvars: &[Symbol]) {
        let mut set = HashSet::new();
        for tv in tyvars {
            if !set.insert(tv) {
                self.diags.push(Diagnostic::error(
                    sp,
                    format!(
                        "type variable '{}' cannot be rebound",
                        self.interner.get(*tv).unwrap_or("?")
                    ),
                ));
            }
        }
    }

    fn check_datatype(&mut self, datbinds: &[Datatype]) {
        for db in datbinds {
            // check for duplicate tyvar or constructors
            self.check_tyvars(db.span, &db.tyvars);
            self.check_rows(&db.constructors, |_, _| ());

            for con in &db.constructors {
                if BUILTIN_CONSTRUCTORS.contains(&con.label) {
                    self.diags.push(Diagnostic::error(
                        con.span,
                        format!(
                            "builtin data constructor '{}' cannot be rebound",
                            self.interner.get(con.label).unwrap_or("?")
                        ),
                    ));
                }
            }
        }
    }

    fn check_variants(&mut self, datbinds: &[Variant]) {
        self.check_rows(datbinds, |_, _| {});
    }

    fn check_valbinds(&mut self, sp: Span, tyvars: &[Symbol], pat: &Pat, expr: &Expr) {
        self.check_tyvars(sp, tyvars);
        if let PatKind::Variable(s) = pat.data {
            if BUILTIN_CONSTRUCTORS.contains(&s) {
                self.diags.push(Diagnostic::error(
                    pat.span,
                    format!(
                        "builtin data constructor '{}' cannot be rebound",
                        self.interner.get(s).unwrap_or("?")
                    ),
                ));
            }
        }
        self.check_pat(pat);
        self.check_expr(expr);
    }

    fn check_funbinds(&mut self, sp: Span, tyvars: &[Symbol], fbs: &[Fun]) {
        self.check_tyvars(sp, tyvars);
        let mut names = HashSet::new();
        for f in fbs {
            let n = f[0].name;
            let a = f[0].pats.len();
            for fb in f.iter() {
                if n != fb.name {
                    self.diags.push(Diagnostic::error(
                        fb.span,
                        format!(
                            "function clause with a different name; expected: {}, found {}",
                            self.interner.get(n).unwrap_or("?"),
                            self.interner.get(fb.name).unwrap_or("?")
                        ),
                    ));
                }
                if a != fb.pats.len() {
                    self.diags.push(Diagnostic::error(
                        fb.span,
                        format!(
                            "function clause with a different number of args; expected: {}, found {}",
                            a, fb.pats.len()
                        )
                    ));
                }
            }
            if !names.insert(n) {
                self.diags.push(Diagnostic::error(
                    f.span,
                    format!(
                        "function '{}' was previously defined in function bindings",
                        self.interner.get(n).unwrap_or("?")
                    ),
                ));
            }
        }
    }

    pub fn check_decl(&mut self, decl: &Decl) {
        use DeclKind::*;
        match &decl.data {
            Datatype(datbinds) => {
                self.check_datatype(datbinds);
                if datbinds.len() >= 255 {
                    self.diags.push(Diagnostic::error(
                        decl.span,
                        format!("maximum of 255 mutually recursive datatypes"),
                    ));
                }
            }
            Type(_) => {}
            Function(tyvars, fbs) => self.check_funbinds(decl.span, tyvars, fbs),
            Value(tyvars, pat, expr) => self.check_valbinds(decl.span, tyvars, pat, expr),
            Exception(vars) => {
                self.check_variants(vars);
                if vars.len() >= 255 {
                    self.diags.push(Diagnostic::error(
                        decl.span,
                        format!("maximum of 255 mutually recursive datatypes"),
                    ));
                }
            }
            Fixity(_, _, _) => {}
            Local(d1, d2) => {
                self.check_decl(d1);
                self.check_decl(d2);
            }
            Seq(decls) => {
                for decl in decls {
                    self.check_decl(decl);
                }
            }
        }
    }
}
