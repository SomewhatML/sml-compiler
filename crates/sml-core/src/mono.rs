use crate::alpha::Rename;
use crate::arenas::CoreArena;
use crate::types::{Constructor, Tycon, Type};
use crate::visit::Visitor;
use crate::{Decl, Lambda, TypeId};
use sml_util::interner::Symbol;
use sml_util::pretty_print::PrettyPrinter;
use std::any::Any;
use std::collections::HashMap;

pub struct Mono<'a, 'i> {
    pub pp: PrettyPrinter<'i>,
    pub arena: &'a CoreArena<'a>,
    map: HashMap<Symbol, HashMap<&'a [&'a Type<'a>], Symbol>>,
    constrs: HashMap<Symbol, (Symbol, HashMap<&'a [&'a Type<'a>], Constructor>)>,
    next: u32,
}

struct ReplaceTy<'a> {
    arena: &'a CoreArena<'a>,
    map: HashMap<usize, &'a Type<'a>>,
}

impl<'a> Visitor<'a> for ReplaceTy<'a> {
    fn arena(&self) -> &'a crate::arenas::CoreArena<'a> {
        self.arena
    }

    fn visit_type(&mut self, ty: &'a Type<'a>) -> &'a Type<'a> {
        match ty {
            Type::Var(tyvar) => match tyvar.ty() {
                Some(ty) => self.visit_type(ty),
                None => match self.map.get(&tyvar.id) {
                    Some(ty) => ty,
                    None => panic!("BUG, tyvar not monomorphized!"),
                },
            },
            Type::Con(tycon, targs) => self.arena.types.alloc(Type::Con(
                *tycon,
                targs.into_iter().map(|ty| self.visit_type(ty)).collect(),
            )),
            Type::Record(record) => self
                .arena
                .types
                .alloc(Type::Record(record.fmap(|ty| self.visit_type(ty)))),
            Type::Flex(_) => ty,
        }
    }
}

impl<'a, 'i> Mono<'a, 'i> {
    pub fn new(pp: PrettyPrinter<'i>, arena: &'a CoreArena<'a>) -> Mono<'a, 'i> {
        Mono {
            pp,
            arena,
            map: HashMap::default(),
            constrs: HashMap::default(),
            next: 100,
        }
    }

    fn rename_var(&mut self, var: Symbol, targs: &'a [&'a Type<'a>]) -> Symbol {
        if !targs.is_empty() {
            let sym = Symbol::Gensym(self.next);
            self.next += 1;
            *self.map.entry(var).or_default().entry(targs).or_insert(sym)
        } else {
            var
        }
    }

    fn rename_tycon(&mut self, tycon: Symbol, targs: &'a [&'a Type<'a>]) -> Symbol {
        if !targs.is_empty() {
            let sym = Symbol::Gensym(self.next);
            self.next += 1;
            let (tycon, _) = self
                .constrs
                .entry(tycon)
                .or_insert_with(|| (sym, HashMap::new()));
            *tycon
        } else {
            tycon
        }
    }

    fn rename_con(&mut self, con: Constructor, targs: &'a [&'a Type<'a>]) -> Constructor {
        if !targs.is_empty() {
            let sym = Symbol::Gensym(self.next);
            self.next += 1;
            let (tycon, map) = self
                .constrs
                .entry(con.tycon)
                .or_insert_with(|| (sym, HashMap::new()));
            match map.get(targs) {
                Some(con) => *con,
                None => {
                    let newcon = Constructor {
                        name: Symbol::Gensym(self.next),
                        type_id: TypeId(self.next),
                        tycon: *tycon,
                        tag: con.tag,
                        arity: con.arity,
                        type_arity: 0,
                    };
                    map.insert(targs, newcon);

                    newcon
                }
            }
        } else {
            con
        }
    }

    fn visit_decl_duplicate(&mut self, decl: &crate::Decl<'a>, vec: &mut Vec<Decl<'a>>) {
        match decl {
            Decl::Val(vars, sym, expr) => {
                if !vars.is_empty() {
                    match self.map.get(sym) {
                        Some(targs) => {
                            self.pp.text("duplicating new Val decl").print(sym).stdout();
                            // for (concrete, newname)
                        }
                        None => {
                            self.pp
                                .text("BUG, should be in mono cache:")
                                .print(sym)
                                .stdout();
                        }
                    }
                }
                // let replace = vars
                //     .iter()
                //     .zip(*concrete)
                //     .map(|(a, b)| (*a, *b))
                //     .collect::<HashMap<_,_>>();

                // let mut renamer = ReplaceTy {arena: &self.arena, map: replace};
                let expr = self.visit_expr(*expr);
                vec.push(Decl::Val(vars.to_vec(), *sym, expr));
            }

            Decl::Fun(vars, lambda) => {
                if !vars.is_empty() {
                    let mut duplicated = Vec::new();
                    for (name, lam) in lambda {
                        match self.map.get(name) {
                            Some(targs) => {
                                if targs.is_empty() {
                                    self.pp
                                        .text("BUG? should be in mono cache:")
                                        .print(name)
                                        .stdout();
                                }
                                for (concrete, newname) in targs {
                                    self.pp
                                        .text("duplicating new fun ")
                                        .print(name)
                                        .text("->")
                                        .print(newname)
                                        .nest(2, |pp| {
                                            for (v, c) in vars.iter().zip(*concrete) {
                                                pp.line().text(format!("var {}", v)).print(*c);
                                            }
                                            pp.line()
                                        })
                                        .stdout();
                                    let replace = vars
                                        .iter()
                                        .zip(*concrete)
                                        .map(|(a, b)| (*a, *b))
                                        .collect::<HashMap<_, _>>();

                                    let mut renamer = ReplaceTy {
                                        arena: &self.arena,
                                        map: replace,
                                    };
                                    let lam = renamer.visit_lambda(&lam);
                                    // lam.ty = lam.ty.apply(&self.arena.types, &replace);

                                    duplicated.push((*newname, lam));
                                }
                            }
                            None => {
                                self.pp
                                    .text("BUG? should be in mono cache:")
                                    .print(name)
                                    .stdout();
                                let lam = self.visit_lambda(lam);
                                duplicated.push((*name, lam));
                            }
                        }
                    }
                    // let duplicated = duplicated.iter().map(|(s,l)| (*s, self.visit_lambda(l))).collect();
                    // Vars must be empty now
                    vec.push(Decl::Fun(Vec::new(), duplicated));
                } else {
                    vec.push(Decl::Fun(Vec::new(), lambda.to_vec()));
                }
            }
            Decl::Datatype(dts) => {
                let mut duplicated = Vec::new();
                for dt in dts {
                    if !dt.tyvars.is_empty() {
                        match self.constrs.get(&dt.tycon.name) {
                            Some((tycon, map)) => {
                                let mut constructors = Vec::new();
                                for (targs, constr) in map {
                                    constructors.push((*constr, None));
                                }
                                duplicated.push(crate::Datatype {
                                    tycon: Tycon {
                                        name: *tycon,
                                        arity: 0,
                                        scope_depth: dt.tycon.scope_depth,
                                    },
                                    tyvars: Vec::new(),
                                    constructors,
                                });
                            }
                            None => {
                                self.pp
                                    .text("BUG: dt missing from cache ")
                                    .print(&*decl)
                                    .line()
                                    .stdout();
                            }
                        }
                    } else {
                        duplicated.push(dt.clone());
                    }
                }
                vec.push(Decl::Datatype(duplicated))
            }
            _ => {
                let decl = self.walk_decl(decl);
                vec.push(decl);
            }
        }
    }
}

impl<'a, 'i> Visitor<'a> for Mono<'a, 'i> {
    fn arena(&self) -> &'a crate::arenas::CoreArena<'a> {
        self.arena
    }

    fn visit_type(&mut self, ty: &'a crate::types::Type<'a>) -> &'a crate::types::Type<'a> {
        // ty
        match ty {
            Type::Var(tyvar) => {
                if let Some(ty) = tyvar.ty() {
                    self.visit_type(ty)
                } else {
                    ty
                }
            }
            Type::Con(tycon, targs) => {
                let name = self.rename_tycon(tycon.name, targs);
                let tycon = Tycon {
                    name,
                    arity: 0,
                    scope_depth: tycon.scope_depth,
                };
                self.arena.types.alloc(Type::Con(tycon, Vec::new()))
            }
            Type::Record(record) => self
                .arena
                .types
                .alloc(Type::Record(record.fmap(|ty| self.visit_type(ty)))),
            Type::Flex(_) => ty,
        }
    }

    fn visit_expr_con(
        &mut self,
        con: crate::types::Constructor,
        targs: &'a [&'a crate::types::Type<'a>],
    ) -> crate::ExprKind<'a> {
        if !targs.is_empty() {
            self.pp
                .text("visiting monomorphized Constructor ")
                .print(&con.name);
            targs.iter().for_each(|ty| {
                self.pp.text(" ").print(*ty);
            });
            let con = self.rename_con(con, targs);
            self.pp.text(": ").print(&con.name).stdout();
            crate::ExprKind::Con(con, Vec::new())
        } else {
            crate::ExprKind::Con(self.visit_con(con), Vec::new())
        }
    }

    fn visit_expr_let(
        &mut self,
        decls: &[crate::Decl<'a>],
        body: crate::Expr<'a>,
    ) -> crate::ExprKind<'a> {
        // let decls: Vec<Decl<'a>> = decls.iter().map(|d| self.visit_decl(d)).collect();
        for decl in decls {
            self.visit_decl(decl);
        }
        let expr = self.visit_expr(body);
        let mut new_decs = Vec::new();
        for decl in decls {
            self.visit_decl_duplicate(decl, &mut new_decs);
        }
        crate::ExprKind::Let(new_decs, expr)
    }

    fn visit_expr_var(
        &mut self,
        sym: sml_util::interner::Symbol,
        targs: &'a [&'a crate::types::Type<'a>],
    ) -> crate::ExprKind<'a> {
        let sym = self.visit_sym(&sym);
        let sym = self.rename_var(sym, targs);

        crate::ExprKind::Var(
            self.visit_sym(&sym),
            targs.into_iter().map(|ty| self.visit_type(*ty)).collect(),
        )
    }
}
