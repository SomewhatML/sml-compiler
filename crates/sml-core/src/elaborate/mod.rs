mod decision;
mod exprs;
mod pats;
mod prec;
mod types;

use super::builtin::constructors::*;
use super::builtin::tycons::*;
use super::*;
use sml_frontend::ast;
use sml_frontend::parser::precedence::{self, Fixity};
use sml_util::diagnostics::Diagnostic;
use sml_util::interner::{S_CONS, S_FALSE, S_NIL, S_REF, S_TRUE};
use std::cell::Cell;
use std::collections::{HashMap, HashSet};

pub fn check_and_elaborate(decl: &ast::Decl) -> (Vec<Decl>, Vec<Diagnostic>) {
    let mut check = super::check::Check::default();
    check.check_decl(decl);

    let mut ctx = Context::new();
    let decls = ctx.elaborate_decl(decl);

    let mut diags = check.diags;
    diags.extend(ctx.diags);
    (decls, diags)
}

/// Identifier status for the Value Environment, as defined in the Defn.
#[derive(Copy, Clone, Debug)]
pub enum IdStatus {
    Exn(Constructor),
    Con(Constructor),
    Var,
}

/// Essentially a minimized Value Environment (VE) containing only datatype
/// constructors, and without the indirection of going from names->id->def
#[derive(Clone, Debug)]
pub struct Cons {
    name: Symbol,
    scheme: Scheme,
}

/// TyStr, a [`TypeStructure`] from the Defn. This is a component of the
/// Type Environment, TE
#[derive(Clone, Debug)]
pub enum TypeStructure {
    /// TyStr (t, VE), a datatype
    Datatype(Tycon, Vec<Cons>),
    /// TyStr (_, VE), a definition. Rather than include a whole VE hashmap,
    /// we can include just a single entry
    Scheme(Scheme),
    /// TyStr (t, {}), a name
    Tycon(Tycon),
}

impl TypeStructure {
    pub fn arity(&self) -> usize {
        match self {
            TypeStructure::Tycon(con) | TypeStructure::Datatype(con, _) => con.arity,
            TypeStructure::Scheme(s) => s.arity(),
        }
    }

    pub fn apply(&self, args: Vec<Type>) -> Type {
        match self {
            TypeStructure::Tycon(con) | TypeStructure::Datatype(con, _) => Type::Con(*con, args),
            TypeStructure::Scheme(s) => s.apply(args),
        }
    }
}
/// An environment scope, that can hold a collection of type and expr bindings
#[derive(Default, Debug)]
pub struct Namespace {
    parent: Option<usize>,
    types: HashMap<Symbol, TypeId>,
    values: HashMap<Symbol, ExprId>,
    infix: HashMap<Symbol, Fixity>,
}

#[derive(Default, Debug)]
pub struct Context {
    // stacks for alpha-renaming
    tyvars: Vec<(Symbol, TypeVar)>,

    namespaces: Vec<Namespace>,
    current: usize,

    // All types live here, indexed by `TypeId`
    types: Vec<TypeStructure>,
    // All values live here, indexed by `ExprId`
    values: Vec<(Scheme, IdStatus)>,

    // Generation of fresh type variables
    tyvar_id: Cell<usize>,
    tyvar_rank: usize,

    // Generation of fresh value variables
    var_id: Cell<u32>,

    pub diags: Vec<Diagnostic>,
}

impl Namespace {
    pub fn with_parent(id: usize) -> Namespace {
        Namespace {
            parent: Some(id),
            types: HashMap::with_capacity(32),
            values: HashMap::with_capacity(64),
            infix: HashMap::with_capacity(16),
        }
    }
}

impl Context {
    pub fn new() -> Context {
        let mut ctx = Context::default();
        ctx.namespaces.push(Namespace::default());

        for tc in &crate::builtin::tycons::T_BUILTINS {
            ctx.define_type(tc.name, TypeStructure::Tycon(*tc));
        }

        let nil = ctx.fresh_tyvar();

        ctx.define_value(
            S_NIL,
            Scheme::Poly(
                vec![nil.id],
                Type::Con(builtin::tycons::T_LIST, vec![Type::Var(nil)]),
            ),
            IdStatus::Con(builtin::constructors::C_NIL),
        );

        let cons = ctx.fresh_tyvar();
        let crec = Type::Record(vec![
            Row {
                label: Symbol::tuple_field(1),
                data: Type::Var(cons.clone()),
                span: Span::dummy(),
            },
            Row {
                label: Symbol::tuple_field(2),
                data: Type::Con(builtin::tycons::T_LIST, vec![Type::Var(cons.clone())]),
                span: Span::dummy(),
            },
        ]);
        ctx.define_value(
            S_CONS,
            Scheme::Poly(
                vec![cons.id],
                Type::arrow(
                    crec,
                    Type::Con(builtin::tycons::T_LIST, vec![Type::Var(cons)]),
                ),
            ),
            IdStatus::Con(builtin::constructors::C_CONS),
        );

        ctx.define_value(
            S_TRUE,
            Scheme::Mono(Type::bool()),
            IdStatus::Con(builtin::constructors::C_TRUE),
        );
        ctx.define_value(
            S_FALSE,
            Scheme::Mono(Type::bool()),
            IdStatus::Con(builtin::constructors::C_FALSE),
        );

        let reff = ctx.fresh_tyvar();
        ctx.define_value(
            S_REF,
            Scheme::Poly(
                vec![reff.id],
                Type::arrow(
                    Type::Var(reff.clone()),
                    Type::Con(builtin::tycons::T_REF, vec![Type::Var(reff)]),
                ),
            ),
            IdStatus::Con(builtin::constructors::C_REF),
        );
        ctx.elab_decl_fixity(&ast::Fixity::Infixr, 4, S_CONS);
        ctx
    }
    /// Keep track of the type variable stack, while executing the combinator
    /// function `f` on `self`. Any stack growth is popped off after `f`
    /// returns.
    fn with_tyvars<T, F: FnMut(&mut Context) -> T>(&mut self, mut f: F) -> T {
        let n = self.tyvars.len();
        let r = f(self);
        while self.tyvars.len() != n {
            self.tyvars.pop();
        }
        r
    }

    /// Handle namespacing. The method creates a new child namespace, enters it
    /// and then calls `f`. After `f` has returned, the current scope is
    /// returned to it's previous value
    fn with_scope<T, F: FnOnce(&mut Context) -> T>(&mut self, f: F) -> T {
        let prev = self.current;
        let next = self.namespaces.len();
        self.namespaces.push(Namespace::with_parent(prev));
        self.current = next;
        let r = f(self);

        self.current = prev;
        r
    }

    fn define_type(&mut self, sym: Symbol, tystr: TypeStructure) -> TypeId {
        let id = TypeId(self.types.len() as u32);
        self.types.push(tystr);
        self.namespaces[self.current].types.insert(sym, id);
        id
    }

    fn define_value(&mut self, sym: Symbol, scheme: Scheme, status: IdStatus) -> ExprId {
        let id = ExprId(self.values.len() as u32);
        self.values.push((scheme, status));
        self.namespaces[self.current].values.insert(sym, id);
        id
    }

    fn unbind_value(&mut self, sym: Symbol) {
        // self.values.push((scheme, status));
        // self.namespaces[self.current].values.insert(sym, id);
        let id = self.namespaces[self.current]
            .values
            .get(&sym)
            .expect("error: redefine_value");
        let s = Scheme::Mono(Type::Var(self.fresh_tyvar()));
        std::mem::replace(&mut self.values[id.0 as usize].0, s);
    }

    /// Starting from the current [`Namespace`], search for a bound name.
    /// If it's not found, then recursively search parent namespaces
    fn lookup_infix(&self, s: &Symbol) -> Option<Fixity> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.infix.get(s) {
                Some(idx) => return Some(*idx),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    fn lookup_type_id(&self, sym: &Symbol) -> Option<TypeId> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.types.get(sym) {
                Some(idx) => return Some(*idx),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    fn lookup_type(&self, sym: &Symbol) -> Option<&TypeStructure> {
        Some(&self[self.lookup_type_id(sym)?])
    }

    fn lookup_value(&self, sym: &Symbol) -> Option<&(Scheme, IdStatus)> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.values.get(sym) {
                Some(idx) => return Some(&self[*idx]),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    fn lookup_tyvar(&mut self, s: &Symbol, allow_unbound: bool) -> Option<TypeVar> {
        for (sym, tv) in self.tyvars.iter().rev() {
            if sym == s {
                return Some(tv.clone());
            }
        }
        if allow_unbound {
            let v = self.fresh_tyvar();
            self.tyvars.push((*s, v.clone()));
            Some(v)
        } else {
            None
        }
    }

    fn fresh_tyvar(&self) -> TypeVar {
        let ex = self.tyvar_id.get();
        self.tyvar_id.set(ex + 1);
        TypeVar::new(ex, self.tyvar_rank)
    }

    fn fresh_var(&self) -> Symbol {
        let ex = self.var_id.get();
        self.var_id.set(ex + 1);
        Symbol::Gensym(ex)
    }

    fn const_ty(&self, c: &Const) -> Type {
        use super::builtin::tycons::*;
        match c {
            Const::Char(_) => Type::Con(T_CHAR, vec![]),
            Const::Int(_) => Type::Con(T_INT, vec![]),
            Const::String(_) => Type::Con(T_STRING, vec![]),
            Const::Unit => Type::Con(T_UNIT, vec![]),
        }
    }

    /// Generic function to elaborate an ast::Row<T> into a core::Row<S>
    /// where T might be ast::Type and S is core::Type, for instance
    fn elab_row<T, S, F: FnMut(&mut Context, &T) -> S>(
        &mut self,
        mut f: F,
        row: &ast::Row<T>,
    ) -> Row<S> {
        Row {
            label: row.label,
            span: row.span,
            data: f(self, &row.data),
        }
    }

    fn namespace_iter(&self) -> NamespaceIter<'_> {
        NamespaceIter {
            ctx: self,
            ptr: Some(self.current),
        }
    }
}

/// A partially elaborated Vec<ast::FnBinding>
struct PartialFun<'s> {
    name: Symbol,
    clauses: Vec<PartialFnBinding<'s>>,
    arity: usize,
    arg_tys: Vec<Type>,
    res_ty: Type,
    ty: Type,
}

/// A partially elaborated ast::FnBinding
struct PartialFnBinding<'s> {
    expr: &'s ast::Expr,
    pats: Vec<Pat>,
    bindings: Vec<pats::Binding>,
    span: Span,
}

impl Context {
    fn elab_decl_fixity(&mut self, fixity: &ast::Fixity, bp: u8, sym: Symbol) {
        let fix = match fixity {
            ast::Fixity::Infix => Fixity::Infix(bp, bp + 1),
            ast::Fixity::Infixr => Fixity::Infix(bp + 1, bp),
            ast::Fixity::Nonfix => Fixity::Nonfix,
        };
        self.namespaces[self.current].infix.insert(sym, fix);
    }

    fn elab_decl_local(&mut self, decls: &ast::Decl, body: &ast::Decl, elab: &mut Vec<Decl>) {
        self.with_scope(|f| {
            f.elaborate_decl_inner(decls, elab);
            f.elaborate_decl_inner(body, elab)
        })
    }

    fn elab_decl_seq(&mut self, decls: &[ast::Decl], elab: &mut Vec<Decl>) {
        for d in decls {
            self.elaborate_decl_inner(d, elab);
        }
    }

    fn elab_decl_type(&mut self, tbs: &[ast::Typebind], _elab: &mut Vec<Decl>) {
        for typebind in tbs {
            let scheme = if !typebind.tyvars.is_empty() {
                self.with_tyvars(|f| {
                    for s in typebind.tyvars.iter() {
                        let v = f.fresh_tyvar();
                        f.tyvars.push((*s, v));
                    }
                    let ty = f.elaborate_type(&typebind.ty, false);
                    let s = match typebind.tyvars.len() {
                        0 => Scheme::Mono(ty),
                        _ => Scheme::Poly(
                            typebind
                                .tyvars
                                .iter()
                                .map(|tv| f.lookup_tyvar(tv, false).unwrap().id)
                                .collect(),
                            ty,
                        ),
                    };

                    s
                })
            } else {
                Scheme::Mono(self.elaborate_type(&typebind.ty, false))
            };
            self.define_type(typebind.tycon, TypeStructure::Scheme(scheme));
        }
    }

    fn elab_decl_conbind(&mut self, db: &ast::Datatype, elab: &mut Vec<Decl>) {
        let tycon = Tycon::new(db.tycon, db.tyvars.len());

        // This is safe to unwrap, because we already bound it.
        let type_id = self.lookup_type_id(&db.tycon).unwrap();

        // Should be safe to unwrap here as well, since the caller has bound db.tyvars
        let tyvars: Vec<TypeVar> = db
            .tyvars
            .iter()
            .map(|sym| self.lookup_tyvar(sym, false).unwrap())
            .collect();

        let mut constructors = Vec::new();
        for (tag, con) in db.constructors.iter().enumerate() {
            if self.lookup_value(&con.label).is_some() {
                self.diags.push(Diagnostic::warn(
                    con.span,
                    format!("rebinding of data constructor {:?}", con.label),
                ));
                return;
            }

            let cons = Constructor {
                name: con.label,
                type_id,
                tag: tag as u32,
            };

            let res = Type::Con(tycon, tyvars.iter().cloned().map(Type::Var).collect());
            let ty = match &con.data {
                Some(ty) => {
                    let dom = self.elaborate_type(ty, false);
                    constructors.push((cons, Some(dom.clone())));

                    Type::arrow(dom, res)
                }
                None => {
                    constructors.push((cons, None));

                    res
                }
            };

            let s = match tyvars.len() {
                0 => Scheme::Mono(ty),
                _ => Scheme::Poly(tyvars.iter().map(|tv| tv.id).collect(), ty),
            };

            self.define_value(con.label, s, IdStatus::Con(cons));
        }
        let dt = Datatype {
            tycon,
            tyvars: tyvars.iter().map(|tv| tv.id).collect(),
            constructors,
        };
        elab.push(Decl::Datatype(dt));
    }

    fn elab_decl_datatype(&mut self, dbs: &[ast::Datatype], elab: &mut Vec<Decl>) {
        // Add all of the type constructors to the environment first, so that
        // we can construct data constructor arguments (e.g. recursive/mutually
        // recursive datatypes)
        for db in dbs {
            let tycon = Tycon::new(db.tycon, db.tyvars.len());
            self.define_type(db.tycon, TypeStructure::Tycon(tycon));
        }
        for db in dbs {
            self.with_tyvars(|f| {
                for s in &db.tyvars {
                    let v = f.fresh_tyvar();
                    f.tyvars.push((*s, v));
                }
                f.elab_decl_conbind(db, elab)
            });
        }
    }

    fn elab_decl_exception(&mut self, exns: &[ast::Variant], elab: &mut Vec<Decl>) {
        for exn in exns {
            let con = Constructor {
                name: exn.label,
                type_id: TypeId(8),
                tag: 0,
            };

            match &exn.data {
                Some(ty) => {
                    let ty = self.elaborate_type(ty, false);
                    elab.push(Decl::Exn(con, Some(ty.clone())));
                    self.define_value(
                        exn.label,
                        Scheme::Mono(Type::arrow(ty, Type::exn())),
                        IdStatus::Exn(con),
                    );
                }
                None => {
                    elab.push(Decl::Exn(con, None));
                    self.define_value(exn.label, Scheme::Mono(Type::exn()), IdStatus::Exn(con));
                }
            }
        }
    }

    /// Perform initial elaboration on a function binding, enough to build up an environment
    fn elab_decl_fnbind_ty<'s>(
        &mut self,
        name: Symbol,
        arity: usize,
        fbs: &'s [ast::FnBinding],
    ) -> PartialFun<'s> {
        let arg_tys = (0..arity)
            .map(|_| Type::Var(self.fresh_tyvar()))
            .collect::<Vec<Type>>();
        let res_ty = Type::Var(self.fresh_tyvar());

        let mut clauses = Vec::new();
        for clause in fbs {
            if let Some(ty) = &clause.res_ty {
                let t = self.elaborate_type(&ty, false);
                self.unify(ty.span, &res_ty, &t);
                // .map_err(|diag| {
                //     diag.message(clause.span, format!("function clause with result constraint of different type: expected {:?}, got {:?}", &res_ty, &t))
                // });
            }

            let mut pats = Vec::new();
            let mut bindings = Vec::new();
            for (idx, pat) in clause.pats.iter().enumerate() {
                let pat = self.elaborate_pat_inner(pat, false, &mut bindings);
                self.unify(pat.span, &arg_tys[idx], &pat.ty);
                // .map_err(|diag| {
                //     diag.message(clause.span, format!("function clause with argument of different type: expected {:?}, got {:?}", &arg_tys[0], &pat.ty))
                // });
                pats.push(pat);
            }
            clauses.push(PartialFnBinding {
                expr: &clause.expr,
                pats,
                bindings,
                span: clause.span,
            })
        }

        let ty = arg_tys
            .iter()
            .rev()
            .cloned()
            .fold(res_ty.clone(), |acc, arg| Type::arrow(arg, acc));

        PartialFun {
            name,
            clauses,
            arity,
            arg_tys,
            res_ty,
            ty,
        }
    }

    fn elab_decl_fnbind(&mut self, fun: PartialFun) -> Lambda {
        let PartialFun {
            clauses,
            res_ty,
            arg_tys,
            arity,
            ..
        } = fun;
        let mut rules = Vec::new();

        // Destructure so that we can move `bindings` into a closure
        for PartialFnBinding {
            mut pats,
            expr,
            bindings,
            span,
        } in clauses
        {
            // Make a new scope, in which we define the pattern bindings, and proceed
            // to elaborate the body of the function clause
            let expr = self.with_scope(move |ctx| {
                for pats::Binding { var, tv } in bindings {
                    ctx.define_value(var, Scheme::Mono(Type::Var(tv)), IdStatus::Var);
                }
                ctx.elaborate_expr(&expr)
            });

            // Unify function clause body with result type
            self.unify(span, &res_ty, &expr.ty);
            // .map_err(|diag| {
            //     diag.message(
            //         span,
            //         format!(
            //             "function clause with body of different type: expected {:?}, got {:?}",
            //             &res_ty, &expr.ty
            //         ),
            //     )
            // });

            // If we have more than 1 pattern, turn it into a tuple (really, a record)
            let pat = match arity {
                1 => pats.remove(0),
                _ => {
                    let mut rows = Vec::new();
                    let mut tys = Vec::new();
                    let mut sp = pats[0].span;
                    for (idx, pat) in pats.into_iter().enumerate() {
                        sp += pat.span;
                        tys.push(Row {
                            label: Symbol::tuple_field(idx as u32 + 1),
                            data: pat.ty.clone(),
                            span: pat.span,
                        });
                        rows.push(Row {
                            label: Symbol::tuple_field(idx as u32 + 1),
                            span: pat.span,
                            data: pat,
                        });
                    }
                    Pat::new(PatKind::Record(rows), Type::Record(tys), sp)
                }
            };

            let rule = Rule { pat, expr };
            rules.push(rule);
        }

        // Now generate fresh argument names for our function, so we can curry
        let mut fresh_args = arg_tys
            .iter()
            .rev()
            .cloned()
            .map(|ty| (self.fresh_var(), ty))
            .collect::<Vec<(Symbol, Type)>>();

        // Generate the scrutinee for the case expression
        // Once again, if we have multiple args, tuplify them
        let scrutinee = match arity {
            1 => {
                let (sym, ty) = &fresh_args[0];
                Expr::new(ExprKind::Var(*sym), ty.clone(), Span::dummy())
            }
            _ => {
                let (rho, tau): (Vec<Row<Expr>>, Vec<Row<Type>>) = fresh_args
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(idx, (sym, ty))| {
                        (
                            Row {
                                label: Symbol::tuple_field(idx as u32 + 1),
                                data: Expr::new(ExprKind::Var(sym), ty.clone(), Span::dummy()),
                                span: Span::dummy(),
                            },
                            Row {
                                label: Symbol::tuple_field(idx as u32 + 1),
                                data: ty,
                                span: Span::dummy(),
                            },
                        )
                    })
                    .unzip();
                Expr::new(ExprKind::Record(rho), Type::Record(tau), Span::dummy())
            }
        };

        self.build_decision_tree(&scrutinee, &rules);

        let case = Expr::new(
            ExprKind::Case(Box::new(scrutinee), rules),
            res_ty.clone(),
            Span::dummy(),
        );

        let (a, t) = fresh_args.pop().unwrap();

        let (body, ty) = fresh_args
            .into_iter()
            .fold((case, res_ty), |(expr, rty), (arg, ty)| {
                (
                    Expr::new(
                        ExprKind::Lambda(Box::new(Lambda {
                            arg,
                            ty: ty.clone(),
                            body: expr,
                        })),
                        Type::arrow(ty.clone(), rty.clone()),
                        Span::dummy(),
                    ),
                    Type::arrow(ty, rty),
                )
            });

        // Rebind with final type. Unbind so that generalization happens properly
        self.unbind_value(fun.name);
        self.define_value(
            fun.name,
            self.generalize(Type::arrow(t.clone(), ty)),
            IdStatus::Var,
        );

        Lambda {
            arg: a,
            ty: t,
            body,
        }
    }

    fn elab_decl_fun(&mut self, tyvars: &[Symbol], fbs: &[ast::Fun], elab: &mut Vec<Decl>) {
        self.with_tyvars(|ctx| {
            let mut vars = Vec::new();

            for sym in tyvars {
                let f = ctx.fresh_tyvar();
                vars.push(f.id);
                ctx.tyvars.push((*sym, f));
            }

            let mut info = Vec::new();
            // Check to make sure all of the function clauses are consistent within each binding group
            for f in fbs {
                let n = f[0].name;
                let a = f[0].pats.len();
                let fns = ctx.elab_decl_fnbind_ty(n, a, f);
                ctx.define_value(fns.name, Scheme::Mono(fns.ty.clone()), IdStatus::Var);
                info.push(fns);
            }

            elab.push(Decl::Fun(
                vars.clone(),
                info.into_iter()
                    .map(|fun| ctx.elab_decl_fnbind(fun))
                    .collect::<Vec<Lambda>>(),
            ));
        })
    }

    fn elab_decl_val(
        &mut self,
        tyvars: &[Symbol],
        pat: &ast::Pat,
        expr: &ast::Expr,
        elab: &mut Vec<Decl>,
    ) {
        self.with_tyvars(|ctx| {
            for tyvar in tyvars {
                ctx.tyvars.push((*tyvar, ctx.fresh_tyvar()));
            }
            let expr = ctx.elaborate_expr(expr);
            let (pat, bindings) = ctx.elaborate_pat(pat, false);

            let non_expansive = expr.non_expansive();
            ctx.unify(expr.span, &pat.ty, &expr.ty);
            for pats::Binding { var, tv } in bindings {
                let sch = match non_expansive {
                    true => ctx.generalize(Type::Var(tv)),
                    false => Scheme::Mono(Type::Var(tv)),
                };
                ctx.define_value(var, sch, IdStatus::Var);
            }

            elab.push(Decl::Val(Rule { pat, expr }));
        })
    }

    pub fn elaborate_decl_inner(&mut self, decl: &ast::Decl, elab: &mut Vec<Decl>) {
        self.tyvar_rank += 1;
        match &decl.data {
            ast::DeclKind::Datatype(dbs) => self.elab_decl_datatype(dbs, elab),
            ast::DeclKind::Type(tbs) => self.elab_decl_type(tbs, elab),
            ast::DeclKind::Function(tyvars, fbs) => self.elab_decl_fun(tyvars, fbs, elab),
            ast::DeclKind::Value(tyvars, pat, expr) => self.elab_decl_val(tyvars, pat, expr, elab),
            ast::DeclKind::Exception(exns) => self.elab_decl_exception(exns, elab),
            ast::DeclKind::Fixity(fixity, bp, sym) => self.elab_decl_fixity(fixity, *bp, *sym),
            ast::DeclKind::Local(decls, body) => self.elab_decl_local(decls, body, elab),
            ast::DeclKind::Seq(decls) => self.elab_decl_seq(decls, elab),
        }
    }

    pub fn elaborate_decl(&mut self, decl: &ast::Decl) -> Vec<Decl> {
        let mut elab = Vec::new();
        self.elaborate_decl_inner(decl, &mut elab);
        elab
    }
}

impl std::ops::Index<TypeId> for Context {
    type Output = TypeStructure;
    fn index(&self, index: TypeId) -> &Self::Output {
        &self.types[index.0 as usize]
    }
}

impl std::ops::Index<ExprId> for Context {
    type Output = (Scheme, IdStatus);
    fn index(&self, index: ExprId) -> &Self::Output {
        &self.values[index.0 as usize]
    }
}

pub struct NamespaceIter<'c> {
    ctx: &'c Context,
    ptr: Option<usize>,
}

impl<'c> Iterator for NamespaceIter<'c> {
    type Item = &'c Namespace;
    fn next(&mut self) -> Option<Self::Item> {
        let n = self.ptr?;
        let ns = &self.ctx.namespaces[n];
        self.ptr = ns.parent;
        Some(ns)
    }
}
