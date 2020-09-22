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

#[derive(Clone)]
pub struct Entry<'a> {
    /// Relate each instantiation of a type to a fresh name
    usages: HashMap<Vec<&'a Type<'a>>, Symbol>,
    tyvars: Vec<usize>,
}

pub struct Rename<'a> {
    arena: &'a CoreArena<'a>,
    stack: Vec<Namespace>,
    cache: HashMap<Symbol, Entry<'a>>,
    diags: Vec<Diagnostic>,
    id: Cell<u32>,
}

#[derive(Default)]
pub struct Namespace {
    types: HashMap<Symbol, Symbol>,
    values: HashMap<Symbol, Symbol>,
}

pub struct Graph {}

impl<'a> Rename<'a> {
    // pub fn register(&mut self, name: Symbol, decl: )

    pub fn new(arena: &'a CoreArena<'a>, builtin: Vec<(Symbol, Vec<usize>)>) -> Rename<'a> {
        let mut r = Rename {
            arena,
            stack: vec![Namespace::default()],
            cache: HashMap::new(),
            diags: Vec::new(),
            id: Cell::new(0),
        };
        for (sym, tyvars) in builtin {
            if !tyvars.is_empty() {
                r.add_entry(sym, tyvars);
            }
        }
        r
    }

    pub fn to_mono(self) -> Mono<'a> {
        Mono {
            arena: self.arena,
            cache: self.cache,
            id: self.id.get(),
        }
    }

    #[inline]
    pub fn enter(&mut self) {
        self.stack.push(Namespace::default())
    }

    #[inline]
    pub fn leave(&mut self) {
        self.stack.pop();
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

        let bindings = entry
            .tyvars
            .iter()
            .copied()
            .zip(usage.iter().copied())
            .collect::<HashMap<_, _>>();

        let ret = *entry.usages.entry(usage).or_insert(f);

        // Incredibly inefficient
        // for (id, instance) in bindings {
        //     for (_, entry) in self.cache.iter_mut() {
        //         let mut append = Vec::new();
        //         for (usages, _) in &entry.usages {
        //             let mut should_append = false;
        //             let entry = usages
        //                 .iter()
        //                 .map(|ty| match ty.to_unresolved() {
        //                     Some(x) if x == id => {
        //                         should_append = true;
        //                         instance
        //                     }
        //                     _ => ty,
        //                 })
        //                 .collect::<Vec<_>>();
        //             if should_append {
        //                 append.push(entry);
        //             }
        //         }
        //         for usage in append {
        //             entry.usages.insert(usage, self.fresh());
        //         }
        //     }
        // }

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

    #[inline]
    pub fn fresh(&self) -> Symbol {
        let id = self.id.get();
        self.id.set(id + 1);
        Symbol::gensym(id)
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

    pub fn swap_type(&self, sym: Symbol) -> Option<Symbol> {
        match sym {
            Symbol::Interned(_) | Symbol::Gensym(_) => {
                let mut ptr = self.stack.len().saturating_sub(1);
                while let Some(ns) = self.stack.get(ptr) {
                    match ns.types.get(&sym).copied() {
                        Some(swap) => return Some(swap),
                        None => ptr = ptr.checked_sub(1)?,
                    }
                }
                None
            }
            _ => Some(sym),
        }
    }

    pub fn swap_value(&self, sym: Symbol) -> Option<Symbol> {
        match sym {
            Symbol::Interned(_) | Symbol::Gensym(_) => {
                let mut ptr = self.stack.len().saturating_sub(1);
                while let Some(ns) = self.stack.get(ptr) {
                    match ns.values.get(&sym).copied() {
                        Some(swap) => return Some(swap),
                        None => ptr = ptr.checked_sub(1)?,
                    }
                }
                None
            }
            _ => Some(sym),
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
                            mono.push(Decl::Val(Vec::new(), *symbol, *expr));
                        }
                        if entry.usages.is_empty() {
                            println!("why is this being reached?");
                            mono.push(Decl::Val(Vec::new(), *sym, *expr));
                        }
                    }
                    None => {
                        mono.push(Decl::Val(Vec::new(), *sym, *expr));
                    }
                }
            }
            Decl::Fun(vars, funs_) => {
                let mut funs = Vec::new();
                for (name, lambda) in funs_ {
                    let mut s = String::new();
                    pp.print(name);

                    match self.cache.get(name).cloned() {
                        Some(entry) => {
                            for (usages, symbol) in &entry.usages {
                                pp.text("->").print(symbol).text("\n").print(name);
                                funs.push((*symbol, *lambda));
                            }
                            if entry.usages.is_empty() {
                                pp.text("->").print(name).text(" EMPTY\n").print(name);
                                funs.push((*name, *lambda));
                            }
                        }
                        None => {
                            funs.push((*name, *lambda));
                        }
                    }
                    pp.write_fmt(&mut s);

                    // println!("monofn {}", s);
                }
                dbg!(funs.len());
                mono.push(Decl::Fun(Vec::new(), funs));
            }
            _ => (),
        }
    }

    pub fn visit_decl(&mut self, decl: &Decl<'a>, pp: &mut PrettyPrinter<'_>) -> Decl<'a> {
        match decl {
            Decl::Val(vars, sym, expr) => {
                let sym = self.register_val(*sym);
                if !vars.is_empty() {
                    self.add_entry(sym, vars.clone());
                }

                let expr = self.visit_expr(&expr, pp);

                Decl::Val(vars.clone(), sym, expr)
            }
            Decl::Fun(vars, funs) => {
                let funs = funs
                    .into_iter()
                    .map(|(sym, mut lam)| {
                        let sym = self.register_val(*sym);
                        self.add_entry(sym, vars.clone());
                        self.enter();
                        lam.arg = self.register_val(lam.arg);
                        lam.ty = self.visit_type(lam.ty, pp);
                        lam.body = self.visit_expr(&lam.body, pp);
                        self.leave();
                        (sym, lam)
                    })
                    .collect();

                Decl::Fun(vars.clone(), funs)
            }
            Decl::Datatype(dts) => {
                // Register all type names in the mutually recursive group
                // prior to walking the bodies
                for dt in dts {
                    self.register_type(dt.tycon.name);
                }

                Decl::Datatype(
                    dts.iter()
                        .map(|dt| {
                            let mut dt = dt.clone();
                            let tyvars = dt.tyvars.clone();

                            dt.tycon.name = self.swap_type(dt.tycon.name).unwrap();
                            if !tyvars.is_empty() {
                                self.add_entry(dt.tycon.name, tyvars.clone());
                            }

                            dt.constructors = dt
                                .constructors
                                .into_iter()
                                .map(|(mut con, ty)| {
                                    con.name = self.register_val(con.name);
                                    if !tyvars.is_empty() {
                                        self.add_entry(con.name, tyvars.clone());
                                    }
                                    con.tycon =
                                        self.swap_type(con.tycon).expect("BUG: Decl::Datatype");
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
                con.name = self.register_val(con.name);
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
                    // emit warning for unused type variable
                    // self.arena.types.unit()
                    ty
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
                con.name = self.swap_type(con.name).expect("BUG: Type::Con");
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
                con.name = self.swap_value(con.name).expect("BUG: PatKind::Con");
                con.tycon = self.swap_type(con.tycon).expect("BUG: PatKind::Con");
                PatKind::App(con, Some(self.visit_pat(pat, pp)))
            }
            PatKind::App(mut con, None) => {
                con.name = self.swap_value(con.name).expect("BUG: PatKind::Con");
                con.tycon = self.swap_type(con.tycon).expect("BUG: PatKind::Con");
                PatKind::App(con, None)
            }
            PatKind::Const(c) => PatKind::Const(*c),
            PatKind::Record(fields) => PatKind::Record(SortedRecord::new_unchecked(
                fields
                    .iter()
                    .map(|row| row.fmap(|pat| self.visit_pat(pat, pp)))
                    .collect(),
            )),
            PatKind::Var(sym) => PatKind::Var(self.register_val(*sym)),
            PatKind::Wild => PatKind::Var(self.fresh()),
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
                let var = self.swap_value(*var).expect("BUG: ExprKind::Case");
                let ty = self.visit_type(ty, pp);

                let rules = rules
                    .iter()
                    .map(|rule| {
                        self.enter();
                        let pat = self.visit_pat(&rule.pat, pp);
                        let expr = self.visit_expr(&rule.expr, pp);
                        self.leave();
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

                con.name = self.swap_value(con.name).expect("BUG: ExprKind::Con");
                con.tycon = self.swap_type(con.tycon).expect("BUG: ExprKind::Con");

                // TODO: Unify constructors together to prevent copying the vector twice
                if !tys.is_empty() {
                    con.name = self.add_usage(con.name, tys.clone());
                    con.tycon = self.add_usage(con.tycon, tys.clone());
                }
                ExprKind::Con(con, tys)
            }
            ExprKind::Const(c) => ExprKind::Const(*c),
            ExprKind::Handle(tryy, sym, handler) => {
                let tryy = self.visit_expr(tryy, pp);
                let sym = self.swap_value(*sym).expect("BUG: ExprKind::Handle");
                let handler = self.visit_expr(handler, pp);
                ExprKind::Handle(tryy, sym, handler)
            }
            ExprKind::Lambda(lam) => {
                let mut lam = *lam;
                self.enter();
                lam.arg = self.register_val(lam.arg);
                lam.ty = self.visit_type(lam.ty, pp);
                lam.body = self.visit_expr(&lam.body, pp);
                self.leave();
                ExprKind::Lambda(lam)
            }
            ExprKind::Let(decls, body) => {
                self.enter();
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

                self.leave();
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

                let name = self.swap_value(*s).expect("BUG");

                let name = if !tys.is_empty() {
                    self.add_usage(name, tys.clone())
                } else {
                    name
                };

                ExprKind::Var(name, tys)
            }
        };
        Expr::new(self.arena.exprs.alloc(kind), ty, expr.span)
    }
}

pub struct Mono<'a> {
    arena: &'a CoreArena<'a>,
    cache: HashMap<Symbol, Entry<'a>>,
    id: u32,
}

type Bindings<'a> = HashMap<usize, &'a Type<'a>>;
impl<'a> Mono<'a> {
    fn mono_expr(
        &mut self,
        expr: &Expr<'a>,
        bindings: Bindings<'a>,
        pp: &mut PrettyPrinter<'_>,
    ) -> Expr<'a> {
        let mut expr = *expr;
        expr.ty = self.mono_type(expr.ty, &bindings, pp);
        expr
    }

    fn mono_pat(
        &mut self,
        pat: &Pat<'a>,
        bindings: Bindings<'a>,
        pp: &mut PrettyPrinter<'_>,
    ) -> Pat<'a> {
        *pat
    }

    fn mono_type(
        &mut self,
        ty: &'a Type<'a>,
        bindings: &Bindings<'a>,
        pp: &mut PrettyPrinter<'_>,
    ) -> &'a Type<'a> {
        match ty {
            Type::Var(tyvar) => match tyvar.ty() {
                Some(ty) => self.mono_type(ty, bindings, pp),
                None => {
                    // emit warning for unused type variable
                    // self.arena.types.unit()
                    bindings.get(&tyvar.id).copied().unwrap_or(ty)
                }
            },
            Type::Record(fields) => {
                let args = SortedRecord::new_unchecked(
                    fields
                        .iter()
                        .map(|row| row.fmap(|ty| self.mono_type(ty, bindings, pp)))
                        .collect(),
                );
                self.arena.types.alloc(Type::Record(args))
            }
            Type::Flex(flex) => match flex.ty() {
                Some(ty) => self.mono_type(ty, bindings, pp),
                None => {
                    // emit warning for unused type variable
                    self.arena.types.unit()
                }
            },
            Type::Con(mut con, args) => {
                let args = args
                    .iter()
                    .map(|ty| self.mono_type(ty, bindings, pp))
                    .collect::<Vec<_>>();
                match self.cache.get(&con.name).cloned() {
                    Some(entry) => {
                        for (usages, symbol) in &entry.usages {
                            assert_eq!(usages.len(), args.len());
                            if usages == &args {
                                con.name = *symbol;
                                pp.line()
                                    .text("monomorphizing tycon: ")
                                    .print(ty)
                                    .text(" => (");
                                for u in usages.iter() {
                                    pp.print(*u).text(", ");
                                }
                                pp.text(") => ").print(symbol);
                                let mut s = String::new();
                                pp.write_fmt(&mut s);
                                println!("{} {}", entry.usages.len(), s);
                                // println!("usages of tycon! {:?}", con.name);
                                return self.arena.types.alloc(Type::Con(con, Vec::new()));
                            }
                            // bindings.extend(vars.iter().copied().zip(usages.iter().copied()));
                            // out.push(Decl::Val(Vec::new(), *symbol, self.mono_expr(expr, bindings)));
                        }
                        if entry.usages.is_empty() {
                            println!("no usages of type constructor? {:?}", con.name);
                        }
                    }
                    None => {
                        // println!("why is this not being reached?");
                        // out.push(Decl::Val(Vec::new(), *sym, self.mono_expr(expr, bindings)));
                    }
                }

                // con.name = self.swap_type(con.name).expect("BUG: Type::Con");
                self.arena.types.alloc(Type::Con(con, args))
            }
        }
    }

    // fn extend_bindings<F: FnMut(&mut Mono<'a>, Bindings<'a>, Symbol)>(
    //     &mut self,
    //     name: Symbol,
    //     tyvars: &[usize],
    //     bindings: Bindings<'a>,
    //     f: F,
    // ) {
    //     match self.cache.get(&name).clone {
    //         Some(entry) => {
    //             for (usages, symbol) in &entry.usages {
    //                 let mut bindings = bindings.clone();
    //                 bindings.extend(tyvars.iter().copied().zip(usages.iter().copied()));
    //                 f(self, bindings, *symbol)
    //             }
    //         }
    //         None => f(self, bindings, name),
    //     }
    // }

    pub fn mono_decl_inner(
        &mut self,
        decl: &Decl<'a>,
        bindings: Bindings<'a>,
        pp: &mut PrettyPrinter<'_>,
        out: &mut Vec<Decl<'a>>,
    ) {
        match decl {
            Decl::Val(vars, sym, expr) => {
                dbg!(sym);
                match self.cache.get(sym).cloned() {
                    Some(entry) => {
                        for (usages, symbol) in &entry.usages {
                            dbg!(symbol);
                            let mut bindings = bindings.clone();
                            bindings.extend(vars.iter().copied().zip(usages.iter().copied()));
                            out.push(Decl::Val(
                                Vec::new(),
                                *symbol,
                                self.mono_expr(expr, bindings, pp),
                            ));
                        }
                        if entry.usages.is_empty() {
                            println!("why is this being reached?");
                            out.push(Decl::Val(
                                Vec::new(),
                                *sym,
                                self.mono_expr(expr, bindings, pp),
                            ));
                        }
                    }
                    None => {
                        out.push(Decl::Val(
                            Vec::new(),
                            *sym,
                            self.mono_expr(expr, bindings, pp),
                        ));
                    }
                }
            }
            Decl::Fun(vars, funs) => {
                let funs = funs
                    .into_iter()
                    .map(|(sym, mut lam)| {
                        lam.ty = self.mono_type(lam.ty, &bindings, pp);
                        lam.body = self.mono_expr(&lam.body, bindings.clone(), pp);
                        (*sym, lam)
                    })
                    .collect();

                out.push(Decl::Fun(vars.clone(), funs));
            }
            Decl::Datatype(dts) => {
                let mut datatypes = Vec::new();
                for dt in dts {
                    match self.cache.get(&dt.tycon.name).cloned() {
                        Some(entry) => {
                            for (usage, name) in &entry.usages {
                                let mut dt = dt.clone();
                                dt.tycon.name = *name;
                                let mut bind = bindings.clone();
                                bind.extend(dt.tyvars.iter().copied().zip(usage.iter().copied()));
                                dt.tyvars = Vec::new();

                                for (con, arg) in dt.constructors.iter_mut() {
                                    if let Some(ty) = arg {
                                        *ty = self.mono_type(ty, &bind, pp);
                                    }
                                }
                                // for (con, ty) in dt.constructors {
                                //     // mono constructors
                                //     if let Some(ty) = ty {

                                //     }
                                // }
                                datatypes.push(dt);
                            }
                        }
                        None => {
                            datatypes.push(dt.clone());
                        }
                    }
                }
                out.push(Decl::Datatype(datatypes))

                // let decl = Decl::Datatype(
                //     dts.iter()
                //         .map(|dt| {
                //             let mut dt = dt.clone();
                //             dt.tycon.name = self.swap_type(dt.tycon.name).unwrap();
                //             dt.constructors = dt
                //                 .constructors
                //                 .into_iter()
                //                 .map(|(mut con, ty)| {
                //                     con.name = self.register_val(con.name);
                //                     con.tycon =
                //                         self.swap_type(con.tycon).expect("BUG: Decl::Datatype");
                //                     (con, ty)
                //                 })
                //                 .collect();
                //             dt
                //         })
                //         .collect(),
                // );
                // out.push(decl);
                // todo!()
            }
            Decl::Exn(con, ty) => {
                // let mut con = *con;
                // con.name = self.register_val(con.name);
                // // con.tycon should be EXN
                // let ty = ty.map(|ty| self.visit_type(ty, pp));
                // Decl::Exn(con, ty)
                todo!()
            }
        }
    }

    // fn visit_type(&mut self, ty: &'a Type<'a>, pp: &mut PrettyPrinter<'_>) -> &'a Type<'a> {
    //     match ty {
    //         Type::Var(tyvar) => match tyvar.ty() {
    //             Some(ty) => self.visit_type(ty, pp),
    //             None => {
    //                 // emit warning for unused type variable
    //                 // self.arena.types.unit()
    //                 ty
    //             }
    //         },
    //         Type::Record(fields) => {
    //             let args = SortedRecord::new_unchecked(
    //                 fields
    //                     .iter()
    //                     .map(|row| row.fmap(|ty| self.visit_type(ty, pp)))
    //                     .collect(),
    //             );
    //             self.arena.types.alloc(Type::Record(args))
    //         }
    //         Type::Flex(flex) => match flex.ty() {
    //             Some(ty) => self.visit_type(ty, pp),
    //             None => {
    //                 // emit warning for unused type variable
    //                 self.arena.types.unit()
    //             }
    //         },
    //         Type::Con(mut con, args) => {
    //             con.name = self.swap_type(con.name).expect("BUG: Type::Con");
    //             self.arena.types.alloc(Type::Con(
    //                 con,
    //                 args.iter().map(|ty| self.visit_type(ty, pp)).collect(),
    //             ))
    //         }
    //     }
    // }

    // fn visit_pat(&mut self, pat: &Pat<'a>, pp: &mut PrettyPrinter<'_>) -> Pat<'a> {
    //     let ty = self.visit_type(pat.ty, pp);

    //     let kind = match pat.kind {
    //         PatKind::App(mut con, Some(pat)) => {
    //             con.name = self.swap_value(con.name).expect("BUG: PatKind::Con");
    //             con.tycon = self.swap_type(con.tycon).expect("BUG: PatKind::Con");
    //             PatKind::App(con, Some(self.visit_pat(pat, pp)))
    //         }
    //         PatKind::App(mut con, None) => {
    //             con.name = self.swap_value(con.name).expect("BUG: PatKind::Con");
    //             con.tycon = self.swap_type(con.tycon).expect("BUG: PatKind::Con");
    //             PatKind::App(con, None)
    //         }
    //         PatKind::Const(c) => PatKind::Const(*c),
    //         PatKind::Record(fields) => PatKind::Record(SortedRecord::new_unchecked(
    //             fields
    //                 .iter()
    //                 .map(|row| row.fmap(|pat| self.visit_pat(pat, pp)))
    //                 .collect(),
    //         )),
    //         PatKind::Var(sym) => PatKind::Var(self.register_val(*sym)),
    //         PatKind::Wild => PatKind::Var(self.fresh()),
    //     };
    //     Pat::new(self.arena.pats.alloc(kind), ty, pat.span)
    // }

    // fn visit_expr(&mut self, expr: &Expr<'a>, pp: &mut PrettyPrinter<'_>) -> Expr<'a> {
    //     let ty = self.visit_type(expr.ty, pp);
    //     let kind = match expr.kind {
    //         ExprKind::App(e1, e2) => {
    //             let e1 = self.visit_expr(e1, pp);
    //             let e2 = self.visit_expr(e2, pp);
    //             ExprKind::App(e1, e2)
    //         }
    //         ExprKind::Case(casee, rules) => {
    //             let (var, ty) = casee;
    //             let var = self.swap_value(*var).expect("BUG: ExprKind::Case");
    //             let ty = self.visit_type(ty, pp);

    //             let rules = rules
    //                 .iter()
    //                 .map(|rule| {
    //                     self.enter();
    //                     let pat = self.visit_pat(&rule.pat, pp);
    //                     let expr = self.visit_expr(&rule.expr, pp);
    //                     self.leave();
    //                     Rule { pat, expr }
    //                 })
    //                 .collect();

    //             ExprKind::Case((var, ty), rules)
    //         }
    //         ExprKind::Con(mut con, tys) => {
    //             con.name = self.swap_value(con.name).expect("BUG: ExprKind::Con");
    //             con.tycon = self.swap_type(con.tycon).expect("BUG: ExprKind::Con");
    //             let tys = tys
    //                 .iter()
    //                 .map(|ty| self.visit_type(ty, pp))
    //                 .collect::<Vec<_>>();
    //             if !tys.is_empty() {
    //                 self.cache.entry(con.name).or_default().push(tys.clone());
    //             }
    //             ExprKind::Con(con, tys)
    //         }
    //         ExprKind::Const(c) => ExprKind::Const(*c),
    //         ExprKind::Handle(tryy, sym, handler) => {
    //             let tryy = self.visit_expr(tryy, pp);
    //             let sym = self.swap_value(*sym).expect("BUG: ExprKind::Handle");
    //             let handler = self.visit_expr(handler, pp);
    //             ExprKind::Handle(tryy, sym, handler)
    //         }
    //         ExprKind::Lambda(lam) => {
    //             let mut lam = *lam;
    //             self.enter();
    //             lam.arg = self.register_val(lam.arg);
    //             lam.ty = self.visit_type(lam.ty, pp);
    //             lam.body = self.visit_expr(&lam.body, pp);
    //             self.leave();
    //             ExprKind::Lambda(lam)
    //         }
    //         ExprKind::Let(decls, body) => {
    //             // Remove redundant let expressions
    //             if decls.len() == 1 {
    //                 match decls.first() {
    //                     Some(Decl::Val(_, Rule { pat, expr })) if pat.equals_expr(&body) => {
    //                         return self.visit_expr(&expr, pp)
    //                     }
    //                     _ => {}
    //                 }
    //             }
    //             self.enter();
    //             let decls = decls
    //                 .iter()
    //                 .map(|d| self.visit_decl(d, pp))
    //                 .collect::<Vec<_>>();
    //             let body = self.visit_expr(body, pp);
    //             self.leave();
    //             ExprKind::Let(decls, body)
    //         }
    //         ExprKind::List(exprs) => {
    //             ExprKind::List(exprs.iter().map(|e| self.visit_expr(e, pp)).collect())
    //         }
    //         ExprKind::Primitive(sym) => ExprKind::Primitive(*sym),
    //         ExprKind::Raise(e) => ExprKind::Raise(self.visit_expr(e, pp)),
    //         ExprKind::Record(rows) => ExprKind::Record(
    //             rows.iter()
    //                 .map(|row| row.fmap(|ex| self.visit_expr(ex, pp)))
    //                 .collect(),
    //         ),
    //         ExprKind::Seq(exprs) => {
    //             ExprKind::Seq(exprs.iter().map(|e| self.visit_expr(e, pp)).collect())
    //         }
    //         ExprKind::Var(s, tys) => {
    //             let name = self.swap_value(*s).expect("BUG");
    //             let tys = tys
    //                 .iter()
    //                 .map(|ty| self.visit_type(ty, pp))
    //                 .collect::<Vec<_>>();
    //             if !tys.is_empty() {
    //                 self.cache.entry(name).or_default().push(tys.clone());
    //             }
    //             ExprKind::Var(name, tys)
    //         }
    //     };
    //     Expr::new(self.arena.exprs.alloc(kind), ty, expr.span)
    // }
}
