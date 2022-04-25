use crate::arenas::CoreArena;
use crate::types::{Constructor, Tycon, Type};
use crate::visit::Visitor;
use crate::{builtin, Datatype, Decl, Expr, ExprKind, Lambda, TypeId};
use sml_util::interner::Symbol;
use sml_util::pretty_print::PrettyPrinter;
use std::any::Any;
use std::collections::HashMap;

// struct TypeMap<'a, T> {
//     inner: HashMap<T, HashMap<&'a [&'a Type<'a>], T>>
// }

// impl<'a, T> TypeMap<'a, T> {
//     pub fn new() -> Self {
//         TypeMap {
//             inner: HashMap::default(),
//         }
//     }

//     pub fn insert(&mut self, key: T, types: &'a [&'a Type<'a>])

// }

pub struct Mono<'a, 'i> {
    pub pp: PrettyPrinter<'i>,
    pub arena: &'a CoreArena<'a>,
    values: HashMap<Symbol, HashMap<&'a [&'a Type<'a>], Symbol>>,
    types: HashMap<Symbol, HashMap<&'a [&'a Type<'a>], Symbol>>,
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
            values: HashMap::default(),
            types: HashMap::default(),
            next: 100,
        }
    }

    fn mk_replacer(&self, tyvars: &[usize], targs: &'a [&'a Type<'a>]) -> ReplaceTy<'a> {
        let map = tyvars.iter().zip(targs).map(|(v, a)| (*v, *a)).collect();
        ReplaceTy {
            arena: &self.arena,
            map,
        }
    }

    fn rename_var(&mut self, var: Symbol, targs: &'a [&'a Type<'a>]) -> Symbol {
        if !targs.is_empty() {
            let sym = Symbol::Gensym(self.next);
            self.next += 1;
            *self
                .values
                .entry(var)
                .or_default()
                .entry(targs)
                .or_insert(sym)
        } else {
            var
        }
    }

    fn rename_tycon(&mut self, tycon: Symbol, targs: &'a [&'a Type<'a>]) -> Symbol {
        if !targs.is_empty() {
            let sym = Symbol::Gensym(self.next);
            self.next += 1;
            *self
                .types
                .entry(tycon)
                .or_default()
                .entry(targs)
                .or_insert(sym)
        } else {
            tycon
        }
    }

    fn rename_con(&mut self, con: Constructor, targs: &'a [&'a Type<'a>]) -> Constructor {
        if !targs.is_empty() {
            let sym = Symbol::Gensym(self.next);
            self.next += 1;
            let tycon = self.rename_tycon(con.tycon, targs);
            let name = self.rename_var(con.name, targs);
            Constructor {
                name,
                tycon,
                type_arity: 0,
                ..con
            }
        } else {
            con
        }
    }

    pub fn run(&mut self, top: Expr<'a>) -> Expr<'a> {
        let body = self.visit_expr(top);
        let decls = self.visit_builtin();
        Expr::new(
            self.arena.exprs.alloc(ExprKind::Let(decls, body)),
            body.ty,
            body.span,
        )
    }

    fn visit_builtin(&mut self) -> Vec<Decl<'a>> {
        // let list = Datatype {
        // tycon: builtin::tycons::T_LIST,
        // tyvars: todo!(),
        // constructors: todo!(),
        // }
        let mut duplicated = Vec::new();
        match self.types.get(&builtin::tycons::T_LIST.name) {
            Some(map) => {
                // let cons = self.values.get(&builtin::constructors::C_CONS.name).expect("BUG");
                // let nil = self.values.get(&builtin::constructors::C_NIL.name).expect("BUG");
                // let cons = [builtin::constructors::C_CONS, builtin::constructors::C_NIL];
                for (targs, &tycon) in map {
                    let mut constructors = Vec::new();
                    let rng = self.arena.types.alloc(Type::Con(
                        Tycon {
                            name: tycon,
                            arity: 0,
                            scope_depth: 0,
                        },
                        Vec::new(),
                    ));
                    let dom = self.arena.types.tuple([targs[0], rng]);
                    if let Some(old) = self.values.get(&builtin::constructors::C_CONS.name) {
                        if let Some(&name) = old.get(targs) {
                            let con = Constructor {
                                name,
                                tycon,
                                type_arity: 0,
                                ..builtin::constructors::C_CONS
                            };

                            constructors.push((con, Some(dom)));
                        }
                    }
                    if let Some(old) = self.values.get(&builtin::constructors::C_NIL.name) {
                        if let Some(&name) = old.get(targs) {
                            let con = Constructor {
                                name,
                                tycon,
                                type_arity: 0,
                                ..builtin::constructors::C_NIL
                            };
                            constructors.push((con, None));
                        }
                    }
                    // }
                    // if constructors.is_empty() {
                    //     constructors.push()
                    // }
                    duplicated.push(Datatype {
                        tycon: Tycon {
                            name: tycon,
                            arity: 0,
                            scope_depth: 0,
                        },
                        tyvars: Vec::new(),
                        constructors,
                    });
                }
            }
            None => {
                //List not used! Impressive!
            }
        }

        if duplicated.is_empty() {
            Vec::new()
        } else {
            vec![Decl::Datatype(duplicated)]
        }
    }

    fn visit_decl_duplicate(&mut self, decl: &crate::Decl<'a>, vec: &mut Vec<Decl<'a>>) {
        match decl {
            Decl::Val(vars, sym, expr) => {
                if !vars.is_empty() {
                    match self.values.get(sym) {
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
                let mut duplicated = Vec::new();
                if !vars.is_empty() {
                    for (name, lam) in lambda {
                        match self.values.get(name) {
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
                } else {
                    for (sym, lam) in lambda {
                        duplicated.push((*sym, self.visit_lambda(lam)));
                    }
                }
                vec.push(Decl::Fun(Vec::new(), duplicated));
            }
            Decl::Datatype(dts) => {
                let mut duplicated = Vec::new();
                for dt in dts {
                    if !dt.tyvars.is_empty() {
                        if let Some(tycon_map) = self.types.get(&dt.tycon.name) {
                            for (tyargs, &tycon) in tycon_map {
                                let mut constructors = Vec::new();
                                for &(con, ty) in &dt.constructors {
                                    match self.values.get(&con.name) {
                                        Some(map) => {
                                            match map.get(tyargs) {
                                                Some(&name) => {
                                                    let ty = match ty {
                                                        Some(ty) => Some(
                                                            self.mk_replacer(&dt.tyvars, tyargs)
                                                                .visit_type(ty),
                                                        ),
                                                        None => None,
                                                    };
                                                    let con = Constructor {
                                                        name,
                                                        tycon,
                                                        type_arity: 0,
                                                        ..con
                                                    };
                                                    constructors.push((con, ty));
                                                }
                                                None => {
                                                    self.pp
                                                        .text("BUG constructor ")
                                                        .print(&con.name)
                                                        .text(" not found with tyargs")
                                                        .line()
                                                        .stdout();
                                                    // Bug? or just unused?
                                                }
                                            }
                                        }
                                        None => {
                                            self.pp
                                                .text("BUG constructor ")
                                                .print(&con.name)
                                                .text(" not found in mono cache")
                                                .line()
                                                .stdout();
                                        }
                                    }
                                }

                                duplicated.push(Datatype {
                                    tycon: Tycon {
                                        name: tycon,
                                        arity: 0,
                                        scope_depth: dt.tycon.arity,
                                    },
                                    tyvars: Vec::new(),
                                    constructors,
                                })
                            }
                        }
                    } else {
                        duplicated.push(dt.clone());
                    }
                }
                vec.push(Decl::Datatype(duplicated))
            }
            Decl::Exn(_, _) => todo!(),
            // _ => {
            //     let decl = self.walk_decl(decl);
            //     vec.push(decl);
            // }
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
        // for decl in decls {
        //     self.visit_decl(decl);
        // }
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

    // fn visit_expr_list(&mut self, list: &[Expr<'a>]) -> ExprKind<'a> {

    // }
}
