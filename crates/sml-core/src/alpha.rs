#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_must_use)]
#![allow(dead_code)]
use crate::arenas::CoreArena;
use crate::types::{Constructor, Type};
use crate::{Decl, Expr, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord};
use sml_util::diagnostics::Diagnostic;
use sml_util::hasher::IntHashMap;
use sml_util::interner::Symbol;
use sml_util::pretty_print::PrettyPrinter;
use sml_util::span::Span;
use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};

/// A [`Hash`] implementation that ignores type variables. This really shouldn't
/// be used anywhere outside of the monomorphization code
impl<'a> Hash for Type<'a> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match &self {
            Type::Var(tv) => match tv.ty() {
                Some(ty) => ty.hash(state),
                None => tv.id.hash(state),
            },
            Type::Flex(tv) => match tv.ty() {
                Some(ty) => ty.hash(state),
                None => 0.hash(state),
            },
            Type::Con(tc, vars) => {
                tc.hash(state);
                vars.iter().for_each(|ty| ty.hash(state))
            }
            Type::Record(fields) => fields.iter().for_each(|f| f.data.hash(state)),
        }
    }
}

/// A [`PartialEq`] implementation that ignores type variables. This really shouldn't
/// be used anywhere outside of the monomorphization code
impl<'a> Eq for Type<'a> {}
impl<'a> PartialEq for Type<'a> {
    fn eq(&self, other: &Self) -> bool {
        match (&self, other) {
            (Type::Var(a), Type::Var(b)) => match (a.ty(), b.ty()) {
                (Some(a), Some(b)) => a == b,
                (Some(_), None) => false,
                (None, Some(_)) => false,
                (None, None) => a.id == b.id,
            },
            (Type::Flex(a), Type::Flex(b)) => match (a.ty(), b.ty()) {
                (Some(a), Some(b)) => a == b,
                (Some(_), None) => false,
                (None, Some(_)) => false,
                (None, None) => a
                    .constraints
                    .iter()
                    .zip(b.constraints.iter())
                    .all(|(a, b)| a.label == b.label && a.data == b.data),
            },
            (Type::Con(a, b), Type::Con(c, d)) => a == c && b == d,
            (Type::Record(a), Type::Record(b)) => a
                .iter()
                .zip(b.iter())
                .all(|(a, b)| a.label == b.label && a.data == b.data),
            _ => false,
        }
    }
}
pub struct Rename<'a> {
    arena: &'a CoreArena<'a>,
    cache: Cache<'a>,
    diags: Vec<Diagnostic>,
    id: Cell<u32>,

    bindings: HashMap<usize, &'a Type<'a>>,
}

#[derive(Default)]
pub struct Namespace {
    types: HashMap<Symbol, Symbol>,
    values: HashMap<Symbol, Symbol>,
}

#[derive(Clone)]
pub struct Entry<'a> {
    /// Relate each instantiation of a type to a fresh name
    usages: HashMap<Vec<&'a Type<'a>>, Symbol>,
    tyvars: Vec<usize>,
}

/// Cache polymorphic values with their instantiations
pub struct Cache<'a> {
    cache: HashMap<Symbol, Entry<'a>>,
    stack: Vec<Namespace>,
    id: Cell<u32>,
}

impl<'a> Cache<'a> {
    pub fn new<I: IntoIterator<Item = (Symbol, Vec<usize>)>>(builtins: I) -> Cache<'a> {
        let mut cache = Cache {
            cache: HashMap::default(),
            stack: vec![Namespace::default()],
            id: Cell::new(0),
        };
        for (name, tyvars) in builtins {
            if !tyvars.is_empty() {
                cache.add_entry(name, tyvars);
            }
        }
        cache
    }

    #[inline]
    pub fn fresh(&self) -> Symbol {
        let id = self.id.get();
        self.id.set(id + 1);
        Symbol::gensym(id)
    }

    /// Add a declaration to the monomorphization cache
    pub fn add_entry(&mut self, fresh: Symbol, tyvars: Vec<usize>) {
        let entry = Entry {
            usages: HashMap::new(),
            tyvars,
        };
        self.cache.insert(fresh, entry);
    }

    #[track_caller]
    /// Add a variable instantiation to the mono cache
    pub fn add_usage(&mut self, name: Symbol, usage: Vec<&'a Type<'a>>) -> Symbol {
        let f = self.fresh();
        let entry = self
            .cache
            .get_mut(&name)
            .expect("monomorphization cache missing");
        assert_eq!(entry.tyvars.len(), usage.len());
        let ret = *entry.usages.entry(usage).or_insert(f);
        ret
    }

    pub fn dump_cache(&self, pp: &mut PrettyPrinter<'_>) {
        for (k, entry) in &self.cache {
            if entry.usages.is_empty() {
                continue;
            }
            for (usage, name) in &entry.usages {
                pp.line();
                for v in &entry.tyvars {
                    pp.print(v);
                }
                pp.text(" ");
                pp.print(k).text("=").print(name).text(" ");
                for ty in usage {
                    pp.text(" ").print(*ty).text(",");
                }
                pp.line();
            }
        }
        let mut b = String::new();
        let _ = pp.write_fmt(&mut b);
        println!("{}", b);
    }

    pub fn register_type(&mut self, sym: Symbol) -> Symbol {
        let fresh = self.fresh();
        self.stack.last_mut().unwrap().types.insert(sym, fresh);
        fresh
    }

    pub fn register_val(&mut self, sym: Symbol) -> Symbol {
        let fresh = self.fresh();
        self.stack.last_mut().unwrap().values.insert(sym, fresh);
        fresh
    }

    fn swap<F>(&self, sym: Symbol, selector: F) -> Option<Symbol>
    where
        F: Fn(&Namespace) -> Option<Symbol>,
    {
        match sym {
            Symbol::Interned(_) | Symbol::Gensym(_) => {
                let mut ptr = self.stack.len().saturating_sub(1);
                while let Some(ns) = self.stack.get(ptr) {
                    match selector(ns) {
                        Some(swap) => return Some(swap),
                        None => ptr = ptr.checked_sub(1)?,
                    }
                }
                None
            }
            _ => Some(sym),
        }
    }

    pub fn swap_type(&self, sym: Symbol) -> Option<Symbol> {
        self.swap(sym, |ns| ns.types.get(&sym).copied())
    }

    pub fn swap_value(&self, sym: Symbol) -> Option<Symbol> {
        self.swap(sym, |ns| ns.values.get(&sym).copied())
    }

    #[inline]
    pub fn enter(&mut self) {
        self.stack.push(Namespace::default())
    }

    #[inline]
    pub fn leave(&mut self) {
        self.stack.pop();
    }

    #[inline]
    pub fn get(&self, sym: &Symbol) -> Option<&Entry<'a>> {
        self.cache.get(sym)
    }
}

impl<'a> Rename<'a> {
    pub fn new(arena: &'a CoreArena<'a>, builtin: Vec<(Symbol, Vec<usize>)>) -> Rename<'a> {
        Rename {
            arena,
            cache: Cache::new(builtin),
            diags: Vec::new(),
            id: Cell::new(0),
            bindings: HashMap::new(),
        }
    }

    pub fn mono_decl(
        &mut self,
        decl: &Decl<'a>,
        mono: &mut Vec<Decl<'a>>,
        pp: &mut PrettyPrinter<'_>,
    ) {
        let mut s = String::new();
        pp.print(decl);
        pp.write_fmt(&mut s);
        // println!("monodec {}", s);
        match decl {
            Decl::Val(vars, sym, expr) => {
                let mut s = String::new();
                pp.print(sym);
                pp.write_fmt(&mut s);
                // println!("mono {}", s);
                match self.cache.get(sym).cloned() {
                    Some(entry) => {
                        for (usages, symbol) in &entry.usages {
                            for (v, u) in vars.iter().zip(usages.iter()) {
                                self.bindings.insert(*v, *u);
                            }
                            mono.push(Decl::Val(Vec::new(), *symbol, self.mono_expr(expr, pp)));
                        }
                        if entry.usages.is_empty() {
                            println!("why is this being reached?");
                            mono.push(Decl::Val(Vec::new(), *sym, self.mono_expr(expr, pp)));
                        }
                    }
                    None => {
                        mono.push(Decl::Val(Vec::new(), *sym, self.mono_expr(expr, pp)));
                    }
                }
            }
            Decl::Fun(vars, funs_) => {
                let mut funs = Vec::new();
                for (name, lambda) in funs_ {
                    // pp.print(name);
                    // let mut lambda = *lambda;
                    match self.cache.get(name).cloned() {
                        Some(entry) => {
                            for (usages, symbol) in &entry.usages {
                                let mut lam = *lambda;
                                for (v, u) in vars.iter().zip(usages.iter()) {
                                    self.bindings.insert(*v, *u);
                                }

                                lam.ty = self.visit_type(lam.ty, pp);
                                lam.body = self.mono_expr(&lam.body, pp);
                                funs.push((*symbol, lam));
                                let mut s = String::new();
                                pp.print(&lam.body);
                                pp.write_fmt(&mut s);
                                println!("{}", s);

                                for (v, u) in vars.iter().zip(usages.iter()) {
                                    self.bindings.remove(v);
                                }
                            }
                            if entry.usages.is_empty() {
                                let mut lam = *lambda;
                                lam.ty = self.visit_type(lam.ty, pp);
                                lam.body = self.mono_expr(&lam.body, pp);
                                // pp.text("->").print(name).text(" EMPTY\n").print(name);\
                                // lambda.ty = self.visit_type(lambda.ty, pp);
                                // lambda.body = self.mono_expr(&lambda.body, pp);
                                funs.push((*name, lam));
                            }
                        }
                        None => {
                            let mut lam = *lambda;
                            lam.ty = self.visit_type(lam.ty, pp);
                            lam.body = self.mono_expr(&lam.body, pp);
                            funs.push((*name, lam));
                        }
                    }
                }
                mono.push(Decl::Fun(Vec::new(), funs));
            }
            _ => (),
        }
    }

    pub fn mono_expr(&mut self, expr: &Expr<'a>, pp: &mut PrettyPrinter<'_>) -> Expr<'a> {
        let ty = self.visit_type(expr.ty, pp);
        let kind = match expr.kind {
            ExprKind::App(e1, e2) => {
                let e1 = self.mono_expr(e1, pp);
                let e2 = self.mono_expr(e2, pp);
                ExprKind::App(e1, e2)
            }
            ExprKind::Case(casee, rules) => {
                let (var, ty) = casee;
                let ty = self.visit_type(ty, pp);

                let rules = rules
                    .iter()
                    .map(|rule| {
                        self.cache.enter();
                        let pat = self.visit_pat(&rule.pat, pp);
                        let expr = self.mono_expr(&rule.expr, pp);
                        self.cache.leave();
                        Rule { pat, expr }
                    })
                    .collect();

                ExprKind::Case((*var, ty), rules)
            }
            ExprKind::Con(mut con, tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.visit_type(ty, pp))
                    .collect::<Vec<_>>();
                ExprKind::Con(con, tys)
            }
            ExprKind::Const(c) => ExprKind::Const(*c),
            ExprKind::Handle(tryy, sym, handler) => {
                let tryy = self.mono_expr(tryy, pp);
                let sym = self.cache.swap_value(*sym).expect("BUG: ExprKind::Handle");
                let handler = self.mono_expr(handler, pp);
                ExprKind::Handle(tryy, sym, handler)
            }
            ExprKind::Lambda(lam) => {
                let mut lam = *lam;
                self.cache.enter();
                lam.ty = self.visit_type(lam.ty, pp);
                lam.body = self.mono_expr(&lam.body, pp);
                self.cache.leave();
                ExprKind::Lambda(lam)
            }
            ExprKind::Let(decls, body) => {
                self.cache.enter();
                let body = self.mono_expr(body, pp);
                let mut mono = Vec::new();
                for decl in decls {
                    self.mono_decl(decl, &mut mono, pp);
                }

                self.cache.leave();
                // return new;
                ExprKind::Let(mono, body)
            }
            ExprKind::List(exprs) => {
                ExprKind::List(exprs.iter().map(|e| self.mono_expr(e, pp)).collect())
            }
            ExprKind::Primitive(sym) => ExprKind::Primitive(*sym),
            ExprKind::Raise(e) => ExprKind::Raise(self.mono_expr(e, pp)),
            ExprKind::Record(rows) => ExprKind::Record(
                rows.iter()
                    .map(|row| row.fmap(|ex| self.mono_expr(ex, pp)))
                    .collect(),
            ),
            ExprKind::Selector(ex, label) => ExprKind::Selector(self.mono_expr(ex, pp), *label),
            ExprKind::Seq(exprs) => {
                ExprKind::Seq(exprs.iter().map(|e| self.mono_expr(e, pp)).collect())
            }
            ExprKind::Var(s, tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.visit_type(ty, pp))
                    .collect::<Vec<_>>();
                ExprKind::Var(*s, tys)
            }
        };
        Expr::new(self.arena.exprs.alloc(kind), ty, expr.span)
    }

    pub fn visit_decl(&mut self, decl: &Decl<'a>, pp: &mut PrettyPrinter<'_>) -> Decl<'a> {
        match decl {
            Decl::Val(vars, sym, expr) => {
                let sym = self.cache.register_val(*sym);
                if !vars.is_empty() {
                    self.cache.add_entry(sym, vars.clone());
                }

                let expr = self.visit_expr(&expr, pp);

                Decl::Val(vars.clone(), sym, expr)
            }
            Decl::Fun(vars, funs) => {
                let funs = funs
                    .into_iter()
                    .map(|(sym, mut lam)| {
                        let sym = self.cache.register_val(*sym);
                        self.cache.add_entry(sym, vars.clone());
                        self.cache.enter();
                        lam.arg = self.cache.register_val(lam.arg);
                        lam.ty = self.visit_type(lam.ty, pp);
                        lam.body = self.visit_expr(&lam.body, pp);
                        self.cache.leave();
                        (sym, lam)
                    })
                    .collect();

                Decl::Fun(vars.clone(), funs)
            }
            Decl::Datatype(dts) => {
                // Register all type names in the mutually recursive group
                // prior to walking the bodies
                for dt in dts {
                    self.cache.register_type(dt.tycon.name);
                }

                Decl::Datatype(
                    dts.iter()
                        .map(|dt| {
                            let mut dt = dt.clone();
                            let tyvars = dt.tyvars.clone();

                            dt.tycon.name = self.cache.swap_type(dt.tycon.name).unwrap();
                            if !tyvars.is_empty() {
                                self.cache.add_entry(dt.tycon.name, tyvars.clone());
                            }

                            dt.constructors = dt
                                .constructors
                                .into_iter()
                                .map(|(mut con, ty)| {
                                    con.name = self.cache.register_val(con.name);
                                    if !tyvars.is_empty() {
                                        self.cache.add_entry(con.name, tyvars.clone());
                                    }
                                    con.tycon = self
                                        .cache
                                        .swap_type(con.tycon)
                                        .expect("BUG: Decl::Datatype");
                                    (con, ty)
                                })
                                .collect();
                            dt
                        })
                        .collect(),
                )
            }
            Decl::Exn(con, ty) => {
                let mut con = *con;
                con.name = self.cache.register_val(con.name);
                // con.tycon should be EXN
                let ty = ty.map(|ty| self.visit_type(ty, pp));
                Decl::Exn(con, ty)
            }
        }
    }

    fn visit_type(&mut self, ty: &'a Type<'a>, pp: &mut PrettyPrinter<'_>) -> &'a Type<'a> {
        match ty {
            Type::Var(tyvar) => match tyvar.ty() {
                Some(ty) => self.visit_type(ty, pp),
                None => {
                    match self.bindings.get(&tyvar.id) {
                        Some(bound) => bound,
                        None => ty,
                    }
                    // emit warning for unused type variable
                    // self.arena.types.unit()
                    // ty
                }
            },
            Type::Record(fields) => {
                let args = SortedRecord::new_unchecked(
                    fields
                        .iter()
                        .map(|row| row.fmap(|ty| self.visit_type(ty, pp)))
                        .collect(),
                );
                self.arena.types.alloc(Type::Record(args))
            }
            Type::Flex(flex) => match flex.ty() {
                Some(ty) => self.visit_type(ty, pp),
                None => {
                    // emit warning for unused type variable
                    let sp = flex.constraints[0].span;
                    self.diags
                        .push(Diagnostic::warn(sp, "unresolved flexible record"));
                    self.arena.types.unit()
                }
            },
            Type::Con(mut con, args) => {
                con.name = self.cache.swap_type(con.name).expect("BUG: Type::Con");
                self.arena.types.alloc(Type::Con(
                    con,
                    args.iter().map(|ty| self.visit_type(ty, pp)).collect(),
                ))
            }
        }
    }

    fn visit_pat(&mut self, pat: &Pat<'a>, pp: &mut PrettyPrinter<'_>) -> Pat<'a> {
        let ty = self.visit_type(pat.ty, pp);

        let kind = match pat.kind {
            PatKind::App(mut con, Some(pat)) => {
                con.name = self.cache.swap_value(con.name).expect("BUG: PatKind::Con");
                con.tycon = self.cache.swap_type(con.tycon).expect("BUG: PatKind::Con");
                PatKind::App(con, Some(self.visit_pat(pat, pp)))
            }
            PatKind::App(mut con, None) => {
                con.name = self.cache.swap_value(con.name).expect("BUG: PatKind::Con");
                con.tycon = self.cache.swap_type(con.tycon).expect("BUG: PatKind::Con");
                PatKind::App(con, None)
            }
            PatKind::Const(c) => PatKind::Const(*c),
            PatKind::Record(fields) => PatKind::Record(SortedRecord::new_unchecked(
                fields
                    .iter()
                    .map(|row| row.fmap(|pat| self.visit_pat(pat, pp)))
                    .collect(),
            )),
            PatKind::Var(sym) => PatKind::Var(self.cache.register_val(*sym)),
            PatKind::Wild => PatKind::Var(self.cache.fresh()),
        };
        Pat::new(self.arena.pats.alloc(kind), ty, pat.span)
    }

    pub fn visit_expr(&mut self, expr: &Expr<'a>, pp: &mut PrettyPrinter<'_>) -> Expr<'a> {
        let ty = self.visit_type(expr.ty, pp);
        let kind = match expr.kind {
            ExprKind::App(e1, e2) => {
                let e1 = self.visit_expr(e1, pp);
                let e2 = self.visit_expr(e2, pp);
                ExprKind::App(e1, e2)
            }
            ExprKind::Case(casee, rules) => {
                let (var, ty) = casee;
                let var = self.cache.swap_value(*var).expect("BUG: ExprKind::Case");
                let ty = self.visit_type(ty, pp);

                let rules = rules
                    .iter()
                    .map(|rule| {
                        self.cache.enter();
                        let pat = self.visit_pat(&rule.pat, pp);
                        let expr = self.visit_expr(&rule.expr, pp);
                        self.cache.leave();
                        Rule { pat, expr }
                    })
                    .collect();

                ExprKind::Case((var, ty), rules)
            }
            ExprKind::Con(mut con, tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.visit_type(ty, pp))
                    .collect::<Vec<_>>();

                con.name = self.cache.swap_value(con.name).expect("BUG: ExprKind::Con");
                con.tycon = self.cache.swap_type(con.tycon).expect("BUG: ExprKind::Con");

                // TODO: Unify constructors together to prevent copying the vector twice
                if !tys.is_empty() {
                    con.name = self.cache.add_usage(con.name, tys.clone());
                    con.tycon = self.cache.add_usage(con.tycon, tys.clone());
                }
                ExprKind::Con(con, tys)
            }
            ExprKind::Const(c) => ExprKind::Const(*c),
            ExprKind::Handle(tryy, sym, handler) => {
                let tryy = self.visit_expr(tryy, pp);
                let sym = self.cache.swap_value(*sym).expect("BUG: ExprKind::Handle");
                let handler = self.visit_expr(handler, pp);
                ExprKind::Handle(tryy, sym, handler)
            }
            ExprKind::Lambda(lam) => {
                let mut lam = *lam;
                self.cache.enter();
                lam.arg = self.cache.register_val(lam.arg);
                lam.ty = self.visit_type(lam.ty, pp);
                lam.body = self.visit_expr(&lam.body, pp);
                self.cache.leave();
                ExprKind::Lambda(lam)
            }
            ExprKind::Let(decls, body) => {
                self.cache.enter();
                let decls = decls
                    .iter()
                    .map(|d| self.visit_decl(d, pp))
                    .collect::<Vec<_>>();

                let body = self.visit_expr(body, pp);
                let mut mono = Vec::new();
                for decl in &decls {
                    self.mono_decl(decl, &mut mono, pp);
                }

                if mono.is_empty() {
                    let mut s = String::new();
                    pp.print(expr);
                    pp.write_fmt(&mut s);
                    println!("let?? {}", s);
                }

                // let new = decls.into_iter().rev().fold(body, |body, decl| {
                //     let lett = self.arena.exprs.alloc(ExprKind::Let(vec![decl], body));
                //     Expr::new(lett, body.ty, body.span)
                // });

                self.cache.leave();
                // return new;
                ExprKind::Let(mono, body)
            }
            ExprKind::List(exprs) => {
                ExprKind::List(exprs.iter().map(|e| self.visit_expr(e, pp)).collect())
            }
            ExprKind::Primitive(sym) => ExprKind::Primitive(*sym),
            ExprKind::Raise(e) => ExprKind::Raise(self.visit_expr(e, pp)),
            ExprKind::Record(rows) => ExprKind::Record(
                rows.iter()
                    .map(|row| row.fmap(|ex| self.visit_expr(ex, pp)))
                    .collect(),
            ),
            ExprKind::Selector(ex, label) => ExprKind::Selector(self.visit_expr(ex, pp), *label),
            ExprKind::Seq(exprs) => {
                ExprKind::Seq(exprs.iter().map(|e| self.visit_expr(e, pp)).collect())
            }
            ExprKind::Var(s, tys) => {
                let tys = tys
                    .iter()
                    .map(|ty| self.visit_type(ty, pp))
                    .collect::<Vec<_>>();

                let name = self.cache.swap_value(*s).expect("BUG");

                let name = if !tys.is_empty() {
                    self.cache.add_usage(name, tys.clone())
                } else {
                    name
                };

                ExprKind::Var(name, tys)
            }
        };
        Expr::new(self.arena.exprs.alloc(kind), ty, expr.span)
    }
}
