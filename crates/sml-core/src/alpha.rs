use crate::arenas::CoreArena;
use crate::types::{Constructor, Type};
use crate::{Decl, Expr, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord};
use sml_util::diagnostics::Diagnostic;
use sml_util::hasher::IntHashMap;
use sml_util::interner::Symbol;
use sml_util::pretty_print::PrettyPrinter;
use sml_util::span::Span;
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

pub struct Entry<'a> {
    /// Relate each instantiation of a type to a fresh name
    usages: HashMap<Vec<&'a Type<'a>>, Symbol>,
}

pub struct Rename<'a> {
    arena: &'a CoreArena<'a>,
    stack: Vec<Namespace>,
    cache: HashMap<Symbol, Entry<'a>>,
    diags: Vec<Diagnostic>,
    id: u32,
}

#[derive(Default)]
pub struct Namespace {
    types: HashMap<Symbol, Symbol>,
    values: HashMap<Symbol, Symbol>,
}

impl<'a> Rename<'a> {
    // pub fn register(&mut self, name: Symbol, decl: )

    pub fn new(arena: &'a CoreArena<'a>) -> Rename<'a> {
        Rename {
            arena,
            stack: vec![Namespace::default()],
            cache: HashMap::new(),
            diags: Vec::new(),
            id: 0,
        }
    }

    // pub fn to_mono(self) -> Mono<'a> {
    //     Mono {
    //         arena: self.arena,
    //         cache: self.cache,
    //         id: self.id,
    //     }
    // }

    pub fn enter(&mut self) {
        self.stack.push(Namespace::default())
    }

    pub fn leave(&mut self) {
        self.stack.pop();
    }

    pub fn add_entry(&mut self, name: Symbol, usage: Vec<&'a Type<'a>>) -> Symbol {
        let fresh = match self.swap_value(name) {
            Some(n) => n,
            None => self.fresh(),
        };

        let entry = self.cache.entry(name).or_insert_with(|| Entry {
            usages: HashMap::new(),
        });
        *entry.usages.entry(usage).or_insert(fresh)
    }

    pub fn dump_cache(&self, pp: &mut PrettyPrinter<'_>) {
        for (k, entry) in &self.cache {
            if entry.usages.is_empty() {
                continue;
            }
            for (usage, name) in &entry.usages {
                pp.line().print(k).text("=").print(name).text(" ");
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
    pub fn fresh(&mut self) -> Symbol {
        let id = self.id;
        self.id += 1;
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

    pub fn visit_decl(&mut self, decl: &Decl<'a>, pp: &mut PrettyPrinter<'_>) -> Decl<'a> {
        match decl {
            Decl::Val(vars, sym, expr) => {
                let sym = self.register_val(*sym);
                let expr = self.visit_expr(&expr, pp);

                Decl::Val(vars.clone(), sym, expr)
            }
            Decl::Fun(vars, funs) => {
                let funs = funs
                    .into_iter()
                    .map(|(sym, mut lam)| {
                        let sym = self.register_val(*sym);
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
                            dt.tycon.name = self.swap_type(dt.tycon.name).unwrap();
                            dt.constructors = dt
                                .constructors
                                .into_iter()
                                .map(|(mut con, ty)| {
                                    con.name = self.register_val(con.name);
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

    fn visit_expr(&mut self, expr: &Expr<'a>, pp: &mut PrettyPrinter<'_>) -> Expr<'a> {
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

                // TODO: Unify constructors together to prevent copying the vector twice
                if !tys.is_empty() {
                    con.name = self.add_entry(con.name, tys.clone());
                    con.tycon = self.add_entry(con.name, tys.clone());
                } else {
                    con.name = self.swap_value(con.name).expect("BUG: ExprKind::Con");
                    con.tycon = self.swap_type(con.tycon).expect("BUG: ExprKind::Con");
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
                // let new = decls.into_iter().rev().fold(body, |body, decl| {
                //     let lett = self.arena.exprs.alloc(ExprKind::Let(vec![decl], body));
                //     Expr::new(lett, body.ty, body.span)
                // });

                self.leave();
                // return new
                ExprKind::Let(decls, body)
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

                let name = if !tys.is_empty() {
                    self.add_entry(*s, tys.clone())
                } else {
                    self.swap_value(*s).expect("BUG")
                };

                ExprKind::Var(name, tys)
            }
        };
        Expr::new(self.arena.exprs.alloc(kind), ty, expr.span)
    }
}

// pub struct Mono<'a> {
//     arena: &'a CoreArena<'a>,
//     cache: HashMap<Symbol, Entry<'a>>,
//     id: u32,
// }

// impl<'a> Mono<'a> {

//         pub fn visit_decl(&mut self, decl: &Decl<'a>, pp: &mut PrettyPrinter<'_>, out: &mut Vec<Decl<'a>>) {
//             match decl {
//                 Decl::Val(vars, Rule { pat, expr }) => {
//                     let pat = self.visit_pat(&pat, pp);
//                     let expr = self.visit_expr(&expr, pp);

//                     out.push(Decl::Val(vars.clone(), Rule { pat, expr }));
//                 }
//                 Decl::Fun(vars, funs) => {
//                     let funs = funs
//                         .into_iter()
//                         .map(|(sym, mut lam)| {
//                             lam.ty = self.visit_type(lam.ty, pp);
//                             lam.body = self.visit_expr(&lam.body, pp);
//                             (*sym, lam)
//                         })
//                         .collect();

//                     out.push(Decl::Fun(vars.clone(), funs));
//                 }
//                 Decl::Datatype(dts) => {
//                     for dt in dts {
//                         let name = self.register_type(dt.tycon.name);
//                     }

//                     let decl = Decl::Datatype(
//                         dts.iter()
//                             .map(|dt| {
//                                 let mut dt = dt.clone();
//                                 dt.tycon.name = self.swap_type(dt.tycon.name).unwrap();
//                                 dt.constructors = dt
//                                     .constructors
//                                     .into_iter()
//                                     .map(|(mut con, ty)| {
//                                         con.name = self.register_val(con.name);
//                                         con.tycon =
//                                             self.swap_type(con.tycon).expect("BUG: Decl::Datatype");
//                                         (con, ty)
//                                     })
//                                     .collect();
//                                 dt
//                             })
//                             .collect(),
//                     );
//                     out.push(decl);
//                 }
//                 Decl::Exn(con, ty) => {
//                     let mut con = *con;
//                     con.name = self.register_val(con.name);
//                     // con.tycon should be EXN
//                     let ty = ty.map(|ty| self.visit_type(ty, pp));
//                     Decl::Exn(con, ty)
//                 }
//             }
//         }

//         fn visit_type(&mut self, ty: &'a Type<'a>, pp: &mut PrettyPrinter<'_>) -> &'a Type<'a> {
//             match ty {
//                 Type::Var(tyvar) => match tyvar.ty() {
//                     Some(ty) => self.visit_type(ty, pp),
//                     None => {
//                         // emit warning for unused type variable
//                         // self.arena.types.unit()
//                         ty
//                     }
//                 },
//                 Type::Record(fields) => {
//                     let args = SortedRecord::new_unchecked(
//                         fields
//                             .iter()
//                             .map(|row| row.fmap(|ty| self.visit_type(ty, pp)))
//                             .collect(),
//                     );
//                     self.arena.types.alloc(Type::Record(args))
//                 }
//                 Type::Flex(flex) => match flex.ty() {
//                     Some(ty) => self.visit_type(ty, pp),
//                     None => {
//                         // emit warning for unused type variable
//                         self.arena.types.unit()
//                     }
//                 },
//                 Type::Con(mut con, args) => {
//                     con.name = self.swap_type(con.name).expect("BUG: Type::Con");
//                     self.arena.types.alloc(Type::Con(
//                         con,
//                         args.iter().map(|ty| self.visit_type(ty, pp)).collect(),
//                     ))
//                 }
//             }
//         }

//         fn visit_pat(&mut self, pat: &Pat<'a>, pp: &mut PrettyPrinter<'_>) -> Pat<'a> {
//             let ty = self.visit_type(pat.ty, pp);

//             let kind = match pat.kind {
//                 PatKind::App(mut con, Some(pat)) => {
//                     con.name = self.swap_value(con.name).expect("BUG: PatKind::Con");
//                     con.tycon = self.swap_type(con.tycon).expect("BUG: PatKind::Con");
//                     PatKind::App(con, Some(self.visit_pat(pat, pp)))
//                 }
//                 PatKind::App(mut con, None) => {
//                     con.name = self.swap_value(con.name).expect("BUG: PatKind::Con");
//                     con.tycon = self.swap_type(con.tycon).expect("BUG: PatKind::Con");
//                     PatKind::App(con, None)
//                 }
//                 PatKind::Const(c) => PatKind::Const(*c),
//                 PatKind::Record(fields) => PatKind::Record(SortedRecord::new_unchecked(
//                     fields
//                         .iter()
//                         .map(|row| row.fmap(|pat| self.visit_pat(pat, pp)))
//                         .collect(),
//                 )),
//                 PatKind::Var(sym) => PatKind::Var(self.register_val(*sym)),
//                 PatKind::Wild => PatKind::Var(self.fresh()),
//             };
//             Pat::new(self.arena.pats.alloc(kind), ty, pat.span)
//         }

//         fn visit_expr(&mut self, expr: &Expr<'a>, pp: &mut PrettyPrinter<'_>) -> Expr<'a> {
//             let ty = self.visit_type(expr.ty, pp);
//             let kind = match expr.kind {
//                 ExprKind::App(e1, e2) => {
//                     let e1 = self.visit_expr(e1, pp);
//                     let e2 = self.visit_expr(e2, pp);
//                     ExprKind::App(e1, e2)
//                 }
//                 ExprKind::Case(casee, rules) => {
//                     let (var, ty) = casee;
//                     let var = self.swap_value(*var).expect("BUG: ExprKind::Case");
//                     let ty = self.visit_type(ty, pp);

//                     let rules = rules
//                         .iter()
//                         .map(|rule| {
//                             self.enter();
//                             let pat = self.visit_pat(&rule.pat, pp);
//                             let expr = self.visit_expr(&rule.expr, pp);
//                             self.leave();
//                             Rule { pat, expr }
//                         })
//                         .collect();

//                     ExprKind::Case((var, ty), rules)
//                 }
//                 ExprKind::Con(mut con, tys) => {
//                     con.name = self.swap_value(con.name).expect("BUG: ExprKind::Con");
//                     con.tycon = self.swap_type(con.tycon).expect("BUG: ExprKind::Con");
//                     let tys = tys
//                         .iter()
//                         .map(|ty| self.visit_type(ty, pp))
//                         .collect::<Vec<_>>();
//                     if !tys.is_empty() {
//                         self.cache.entry(con.name).or_default().push(tys.clone());
//                     }
//                     ExprKind::Con(con, tys)
//                 }
//                 ExprKind::Const(c) => ExprKind::Const(*c),
//                 ExprKind::Handle(tryy, sym, handler) => {
//                     let tryy = self.visit_expr(tryy, pp);
//                     let sym = self.swap_value(*sym).expect("BUG: ExprKind::Handle");
//                     let handler = self.visit_expr(handler, pp);
//                     ExprKind::Handle(tryy, sym, handler)
//                 }
//                 ExprKind::Lambda(lam) => {
//                     let mut lam = *lam;
//                     self.enter();
//                     lam.arg = self.register_val(lam.arg);
//                     lam.ty = self.visit_type(lam.ty, pp);
//                     lam.body = self.visit_expr(&lam.body, pp);
//                     self.leave();
//                     ExprKind::Lambda(lam)
//                 }
//                 ExprKind::Let(decls, body) => {
//                     // Remove redundant let expressions
//                     if decls.len() == 1 {
//                         match decls.first() {
//                             Some(Decl::Val(_, Rule { pat, expr })) if pat.equals_expr(&body) => {
//                                 return self.visit_expr(&expr, pp)
//                             }
//                             _ => {}
//                         }
//                     }
//                     self.enter();
//                     let decls = decls
//                         .iter()
//                         .map(|d| self.visit_decl(d, pp))
//                         .collect::<Vec<_>>();
//                     let body = self.visit_expr(body, pp);
//                     self.leave();
//                     ExprKind::Let(decls, body)
//                 }
//                 ExprKind::List(exprs) => {
//                     ExprKind::List(exprs.iter().map(|e| self.visit_expr(e, pp)).collect())
//                 }
//                 ExprKind::Primitive(sym) => ExprKind::Primitive(*sym),
//                 ExprKind::Raise(e) => ExprKind::Raise(self.visit_expr(e, pp)),
//                 ExprKind::Record(rows) => ExprKind::Record(
//                     rows.iter()
//                         .map(|row| row.fmap(|ex| self.visit_expr(ex, pp)))
//                         .collect(),
//                 ),
//                 ExprKind::Seq(exprs) => {
//                     ExprKind::Seq(exprs.iter().map(|e| self.visit_expr(e, pp)).collect())
//                 }
//                 ExprKind::Var(s, tys) => {
//                     let name = self.swap_value(*s).expect("BUG");
//                     let tys = tys
//                         .iter()
//                         .map(|ty| self.visit_type(ty, pp))
//                         .collect::<Vec<_>>();
//                     if !tys.is_empty() {
//                         self.cache.entry(name).or_default().push(tys.clone());
//                     }
//                     ExprKind::Var(name, tys)
//                 }
//             };
//             Expr::new(self.arena.exprs.alloc(kind), ty, expr.span)
//         }
// }
