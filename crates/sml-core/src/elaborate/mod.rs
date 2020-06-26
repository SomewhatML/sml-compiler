mod prec;
mod stack;

use super::builtin::constructors::*;
use super::builtin::tycons::*;
use super::inference::Constraint;
use super::*;
use sml_frontend::ast;
use sml_frontend::parser::precedence::{self, Fixity, Precedence, Query};
use sml_util::diagnostics::Diagnostic;
use sml_util::interner::{S_CONS, S_FALSE, S_NIL, S_REF, S_TRUE};
use stack::TyVarStack;
use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

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
    tyvars: TyVarStack,

    namespaces: Vec<Namespace>,
    current: usize,

    types: Vec<TypeStructure>,
    values: Vec<(Scheme, IdStatus)>,

    tyvar_id: Cell<usize>,
    tyvar_rank: usize,

    constraints: Vec<Constraint>,

    decls: Vec<Decl>,
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

        // ctx.define_value(S_NIL, Scheme::Poly(vec![0], Type::Con(builtin::tycons::T_LIST, vec![Type::Var(TypeVar::new(0, 0))])), IdStatus::Con(builtin::constructors::C_NIL));
        // ctx.define_value(S_CONS, Scheme::Poly(vec![0], Type::Con(builtin::tycons::T_LIST, vec![Type::Var(TypeVar::new(0, 0))])), IdStatus::Con(builtin::constructors::C_CONS));
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
        ctx.elab_decl_fixity(&ast::Fixity::Infixr, 4, S_CONS)
            .unwrap();
        ctx.tyvar_id.set(1);
        ctx
    }
    /// Keep track of the type variable stack, while executing the combinator
    /// function `f` on `self`. Any stack growth is popped off after `f`
    /// returns.
    fn with_tyvars<T, F: FnMut(&mut Context) -> T>(&mut self, mut f: F) -> T {
        let n = self.tyvars.len();
        let r = f(self);
        let to_pop = self.tyvars.len() - n;
        self.tyvars.popn(to_pop);
        r
    }

    /// Handle namespacing. The method creates a new child namespace, enters it
    /// and then calls `f`. After `f` has returned, the current scope is returned
    /// to it's previous value
    fn with_scope<T, F: FnMut(&mut Context) -> T>(&mut self, mut f: F) -> T {
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

    fn define_value(&mut self, sym: Symbol, scheme: Scheme, is: IdStatus) -> ExprId {
        let id = ExprId(self.values.len() as u32);
        self.values.push((scheme, is));
        self.namespaces[self.current].values.insert(sym, id);
        id
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

    fn lookup_type(&self, sym: &Symbol) -> Option<&TypeStructure> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.types.get(sym) {
                Some(idx) => return Some(&self[*idx]),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    fn lookup_typeid(&self, sym: &Symbol) -> Option<TypeId> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.types.get(sym) {
                Some(idx) => return Some(*idx),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
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
            Some(self.fresh_tyvar())
        } else {
            None
        }
    }

    fn fresh_tyvar(&self) -> TypeVar {
        let ex = self.tyvar_id.get();
        self.tyvar_id.set(ex + 1);
        TypeVar::new(ex, self.tyvar_rank)
    }
}

/// Note that this can only be called once!
fn bind(sp: Span, var: &TypeVar, ty: &Type) -> Result<(), Diagnostic> {
    if ty.occurs_check(var) {
        return Err(Diagnostic::error(
            sp,
            format!("Cyclic type detected: {:?}", ty),
        ));
    }

    var.data.set(ty.clone()).unwrap();
    Ok(())
}

impl Context {
    fn unify(&self, sp: Span, a: &Type, b: &Type) -> Result<(), Diagnostic> {
        match (a, b) {
            (Type::Var(a), b) => match a.ty() {
                Some(ty) => self.unify(sp, ty, b),
                None => bind(sp, a, b),
            },
            (a, Type::Var(b)) => match b.ty() {
                Some(ty) => self.unify(sp, a, ty),
                None => bind(sp, b, a),
            },
            (Type::Con(a, a_args), Type::Con(b, b_args)) => {
                if a != b {
                    Err(Diagnostic::error(
                        sp,
                        format!("Can't unify type constructor {:?} and {:?}", a, b),
                    ))
                } else if a_args.len() != b_args.len() {
                    Err(Diagnostic::error(
                        sp,
                        "Can't unify type constructors with different argument lengths",
                    )
                    .message(sp, format!("first type has arguments: {:?}", a_args))
                    .message(sp, format!("and second type has arguments: {:?}", b_args)))
                } else {
                    for (c, d) in a_args.into_iter().zip(b_args) {
                        self.unify(sp, c, d)?;
                    }
                    Ok(())
                }
            }
            (Type::Record(r1), Type::Record(r2)) => {
                let mut r1 = r1.clone();
                let mut r2 = r2.clone();
                r1.sort_by(|a, b| a.label.cmp(&b.label));
                r2.sort_by(|a, b| a.label.cmp(&b.label));

                for (ra, rb) in r1.into_iter().zip(r2.into_iter()) {
                    self.unify(sp, &ra.data, &rb.data)?;
                }

                Ok(())
            }
            (a, b) => Err(Diagnostic::error(
                sp,
                format!("Can't unify types {:?} and {:?}", a, b),
            )),
        }
    }

    // fn unify(&self, sp: Span, ty1: Type, ty2: Type) -> Result<Type, Diagnostic> {
    //     match (ty1, ty2) {
    //         (Type::Var(x), ty2) => Ok(ty2),
    //         (ty1, Type::Var(x)) => Ok(ty1),
    //         (Type::Con(tc1, a_args), Type::Con(tc2, b_args)) => {
    //             if tc1 != tc2 {
    //                 Err(Diagnostic::error(
    //                     sp,
    //                     format!("Can't unify type constructor {:?} and {:?}", tc1, tc2),
    //                 ))
    //             } else if a_args.len() != b_args.len() {
    //                 Err(Diagnostic::error(
    //                     sp,
    //                     "Can't unify type constructors with different argument lengths",
    //                 )
    //                 .message(sp, format!("first type has arguments: {:?}", a_args))
    //                 .message(sp, format!("and second type has arguments: {:?}", b_args)))
    //             } else {
    //                 Ok(Type::Con(
    //                     tc1,
    //                     a_args
    //                         .into_iter()
    //                         .zip(b_args)
    //                         .map(|(a, b)| self.unify(sp, a, b))
    //                         .collect::<Result<_, _>>()?,
    //                 ))
    //             }
    //         }
    //         (Type::Record(mut r1), Type::Record(mut r2)) => {
    //             r1.sort_by(|a, b| a.label.cmp(&b.label));
    //             r2.sort_by(|a, b| a.label.cmp(&b.label));

    //             let rows = r1
    //                 .into_iter()
    //                 .zip(r2.into_iter())
    //                 .map(|(a, b)| a.fmap(|ty| self.unify(sp, ty, b.data)).flatten())
    //                 .collect::<Result<_, _>>()?;
    //             Ok(Type::Record(rows))
    //         }
    //         (a, b) => Err(Diagnostic::error(
    //             sp,
    //             format!("Can't unify types {:?} and {:?}", a, b),
    //         )),
    //     }
    // }

    fn unify_list(&self, sp: Span, tys: &[Type]) -> Result<(), Diagnostic> {
        let fst = &tys[0];
        for ty in tys {
            self.unify(sp, ty, fst)?;
        }
        Ok(())
    }

    fn unify_list_ref(&self, sp: Span, tys: &[&Type]) -> Result<(), Diagnostic> {
        let fst = &tys[0];
        for ty in tys {
            self.unify(sp, ty, fst)?;
        }
        Ok(())
    }
}

impl Context {
    fn elaborate_type(&mut self, ty: &ast::Type, allow_unbound: bool) -> Result<Type, Diagnostic> {
        use ast::TypeKind::*;
        match &ty.data {
            Var(s) => match self.lookup_tyvar(s, allow_unbound) {
                Some(tv) => Ok(Type::Var(tv)),
                None => Err(Diagnostic::error(
                    ty.span,
                    format!("unbound type variable {:?}", s),
                )),
            },
            Con(s, args) => {
                let args = args
                    .iter()
                    .map(|ty| self.elaborate_type(&ty, allow_unbound))
                    .collect::<Result<Vec<Type>, _>>()?;
                let con = self.lookup_type(s).ok_or_else(|| {
                    Diagnostic::error(ty.span, format!("unbound type variable {:?}", s))
                })?;
                if con.arity() != args.len() {
                    Err(Diagnostic::error(
                        ty.span,
                        format!(
                            "type constructor requires {} arguments, but {} are supplied",
                            con.arity(),
                            args.len()
                        ),
                    )
                    .message(ty.span, format!("in type {:?}", ty)))
                } else {
                    Ok(con.apply(args))
                }
            }
            Record(rows) => rows
                .into_iter()
                .map(|row| self.elab_row(|f, r| f.elaborate_type(r, allow_unbound), row))
                .collect::<Result<Vec<Row<Type>>, _>>()
                .map(Type::Record),
        }
    }

    fn generalize(&self, ty: Type) -> Scheme {
        let ftv = ty.ftv(self.tyvar_rank);
        match ftv.len() {
            0 => Scheme::Mono(ty),
            _ => Scheme::Poly(ftv, ty),
        }
    }

    fn instantiate(&self, scheme: Scheme) -> Type {
        match scheme {
            Scheme::Mono(ty) => ty,
            Scheme::Poly(vars, ty) => {
                let map = vars
                    .into_iter()
                    .map(|v| (v, Type::Var(self.fresh_tyvar())))
                    .collect();
                ty.apply(&map)
            }
        }
    }
}

impl Context {
    fn elab_if(&mut self, sp: Span, e1: Expr, e2: Expr, e3: Expr) -> Result<Expr, Diagnostic> {
        let tru = Rule {
            pat: Pat::new(PatKind::App(C_TRUE, None), Type::bool(), e2.span),
            expr: e2,
        };
        let fls = Rule {
            pat: Pat::new(PatKind::App(C_FALSE, None), Type::bool(), e3.span),
            expr: e3,
        };

        Ok(Expr::new(
            ExprKind::Case(Box::new(e1), vec![tru, fls]),
            Type::bool(),
            sp,
        ))
    }

    fn elab_rule(&mut self, rule: &ast::Rule, bind: bool) -> Result<Rule, Diagnostic> {
        let pat = self.elaborate_pat(&rule.pat, bind)?;
        let expr = self.elaborate_expr(&rule.expr)?;
        Ok(Rule { pat, expr })
    }

    fn elaborate_expr(&mut self, expr: &ast::Expr) -> Result<Expr, Diagnostic> {
        match &expr.data {
            ast::ExprKind::Andalso(e1, e2) => {
                let e1 = self.elaborate_expr(e1)?;
                let e2 = self.elaborate_expr(e2)?;
                self.unify(e1.span, &e1.ty, &Type::bool())?;
                self.unify(e2.span, &e2.ty, &Type::bool())?;

                let fls = Expr::new(ExprKind::Con(C_FALSE, vec![]), Type::bool(), expr.span);
                self.elab_if(expr.span, e1, e2, fls)
            }
            ast::ExprKind::App(e1, e2) => {
                let e1 = self.elaborate_expr(e1)?;
                let e2 = self.elaborate_expr(e2)?;
                match e1.ty.clone().de_arrow() {
                    Some((arg, res)) => {
                        self.unify(e2.span, arg, &e2.ty)?;
                        Ok(Expr::new(
                            ExprKind::App(Box::new(e1), Box::new(e2)),
                            res.clone(),
                            expr.span,
                        ))
                    }
                    None => Err(Diagnostic::error(
                        expr.span,
                        format!("can't assign an arrow type to {:?}", e1),
                    )),
                }
            }
            ast::ExprKind::FlatApp(exprs) => {
                let p = match self.expr_precedence(exprs.clone(), expr.span) {
                    Ok(p) => Ok(p),
                    Err(precedence::Error::EndsInfix) => Err(Diagnostic::error(
                        expr.span,
                        "application pattern ends with an infix operator",
                    )),
                    Err(precedence::Error::InfixInPrefix) => Err(Diagnostic::error(
                        expr.span,
                        "application pattern starts with an infix operator",
                    )),
                    Err(precedence::Error::SamePrecedence) => Err(Diagnostic::error(
                        expr.span,
                        "application pattern mixes operators of equal precedence",
                    )),
                    Err(precedence::Error::InvalidOperator) => Err(Diagnostic::error(
                        expr.span,
                        "application pattern doesn't contain infix operator",
                    )),
                }?;
                self.elaborate_expr(&p)
            }
            ast::ExprKind::Case(scrutinee, rules) => {
                let casee = self.elaborate_expr(scrutinee)?;
                let rules = rules
                    .into_iter()
                    .map(|r| self.elab_rule(r, true))
                    .collect::<Result<Vec<Rule>, _>>()?;

                let mut rtys = rules
                    .iter()
                    .map(|r| Type::arrow(r.pat.ty.clone(), r.expr.ty.clone()))
                    .collect::<Vec<Type>>();

                self.unify_list(expr.span, &rtys)?;
                let fst = rtys.remove(0);

                let (arg, res) = fst.de_arrow().ok_or_else(|| {
                    Diagnostic::bug(expr.span, "match rules should have arrow type!")
                })?;

                self.unify(scrutinee.span, &casee.ty, arg)?;

                Ok(Expr::new(
                    ExprKind::Case(Box::new(casee), rules),
                    res.clone(),
                    expr.span,
                ))
            }
            ast::ExprKind::Const(c) => {
                let ty = self.const_ty(c);
                Ok(Expr::new(ExprKind::Const(*c), ty, expr.span))
            }
            ast::ExprKind::Var(sym) => match self.lookup_value(sym) {
                Some((scheme, ids)) => {
                    let ty = self.instantiate(scheme.clone());
                    Ok(Expr::new(ExprKind::Var(*sym), ty, expr.span))
                }
                None => Err(Diagnostic::error(
                    expr.span,
                    format!("unbound variable {:?}", sym),
                )),
            },
            ast::ExprKind::Record(rows) => {
                let rows = rows
                    .into_iter()
                    .map(|r| self.elab_row(|ec, r| ec.elaborate_expr(r), r))
                    .collect::<Result<Vec<Row<Expr>>, _>>()?;
                let tys = rows
                    .iter()
                    .cloned()
                    .map(|r| r.fmap(|x| x.ty))
                    .collect::<Vec<Row<Type>>>();
                let ty = Type::Record(tys);
                Ok(Expr::new(ExprKind::Record(rows), ty, expr.span))
            }
            _ => Err(Diagnostic::error(
                expr.span,
                format!("unknown expr {:?}", expr),
            )),
        }
    }
}

impl Context {
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
    fn elab_row<T, S, E, F: FnMut(&mut Context, &T) -> Result<S, E>>(
        &mut self,
        mut f: F,
        row: &ast::Row<T>,
    ) -> Result<Row<S>, E> {
        Ok(Row {
            label: row.label,
            span: row.span,
            data: f(self, &row.data)?,
        })
    }

    fn elaborate_pat(&mut self, pat: &ast::Pat, bind: bool) -> Result<Pat, Diagnostic> {
        use ast::PatKind::*;
        match &pat.data {
            App(con, p) => {
                let p = self.elaborate_pat(p, bind)?;
                match self.lookup_value(con).cloned() {
                    Some((scheme, IdStatus::Con(constr))) => {
                        // TODO: Scheme instantiation
                        let inst = self.instantiate(scheme);
                        let (arg, res) = inst.de_arrow().ok_or_else(|| {
                            Diagnostic::error(pat.span, "constant constructor applied to pattern")
                                .message(p.span, format!("constructor: {:?} ", con))
                        })?;

                        let _ = self.unify(pat.span, arg, &p.ty)?;
                        Ok(Pat::new(
                            PatKind::App(constr, Some(Box::new(p))),
                            res.clone(),
                            pat.span,
                        ))
                    }
                    _ => Err(Diagnostic::error(
                        pat.span,
                        format!("Non-constructor {:?} applied to pattern {:?}", con, p),
                    )),
                }
            }
            Ascribe(p, ty) => {
                let p = self.elaborate_pat(p, bind)?;
                let ty = self.elaborate_type(ty, false)?;
                self.unify(pat.span, &p.ty, &ty)?;
                Ok(p)
            }
            Const(c) => {
                let ty = self.const_ty(c);
                Ok(Pat::new(PatKind::Const(*c), ty, pat.span))
            }
            FlatApp(pats) => {
                let p = match self.pat_precedence(pats.clone(), pat.span) {
                    Ok(p) => Ok(p),
                    Err(precedence::Error::EndsInfix) => Err(Diagnostic::error(
                        pat.span,
                        "application pattern ends with an infix operator",
                    )),
                    Err(precedence::Error::InfixInPrefix) => Err(Diagnostic::error(
                        pat.span,
                        "application pattern starts with an infix operator",
                    )),
                    Err(precedence::Error::SamePrecedence) => Err(Diagnostic::error(
                        pat.span,
                        "application pattern mixes operators of equal precedence",
                    )),
                    Err(precedence::Error::InvalidOperator) => Err(Diagnostic::error(
                        pat.span,
                        "application pattern doesn't contain infix operator",
                    )),
                }?;
                self.elaborate_pat(&p, bind)
            }
            List(pats) => {
                let pats: Vec<Pat> = pats
                    .into_iter()
                    .map(|p| self.elaborate_pat(p, bind))
                    .collect::<Result<_, _>>()?;

                let tys = pats.iter().map(|p| &p.ty).collect::<Vec<&Type>>();
                self.unify_list_ref(pat.span, &tys)?;

                let ty = tys[0].clone();

                Ok(Pat::new(
                    PatKind::List(pats),
                    Type::Con(T_LIST, vec![ty]),
                    pat.span,
                ))
            }
            Record(rows) => {
                let pats: Vec<Row<Pat>> = rows
                    .into_iter()
                    .map(|r| self.elab_row(|f, rho| f.elaborate_pat(rho, bind), r))
                    .collect::<Result<_, _>>()?;

                let tys = pats
                    .iter()
                    .map(|p| Row {
                        label: p.label,
                        span: p.span,
                        data: p.data.ty.clone(),
                    })
                    .collect::<Vec<Row<Type>>>();

                Ok(Pat::new(PatKind::Record(pats), Type::Record(tys), pat.span))
            }
            Variable(sym) => match self.lookup_value(sym).cloned() {
                // Rule 35
                Some((scheme, IdStatus::Exn(c))) | Some((scheme, IdStatus::Con(c))) => {
                    let ty = self.instantiate(scheme.clone());
                    Ok(Pat::new(PatKind::App(c, None), ty, pat.span))
                }
                _ => {
                    // Rule 34
                    let tv = self.fresh_tyvar();
                    if bind {
                        self.define_value(*sym, Scheme::Mono(Type::Var(tv.clone())), IdStatus::Var);
                    }
                    Ok(Pat::new(PatKind::Var(*sym), Type::Var(tv), pat.span))
                }
            },
            Wild => Ok(Pat::new(
                PatKind::Wild,
                Type::Var(self.fresh_tyvar()),
                pat.span,
            )),
        }
    }
}

impl Context {
    fn elab_decl_fixity(
        &mut self,
        fixity: &ast::Fixity,
        bp: u8,
        sym: Symbol,
    ) -> Result<(), Diagnostic> {
        let fix = match fixity {
            ast::Fixity::Infix => Fixity::Infix(bp, bp + 1),
            ast::Fixity::Infixr => Fixity::Infix(bp + 1, bp),
            ast::Fixity::Nonfix => Fixity::Nonfix,
        };
        self.namespaces[self.current].infix.insert(sym, fix);
        Ok(())
    }

    fn elab_decl_local(&mut self, decls: &ast::Decl, body: &ast::Decl) -> Result<(), Diagnostic> {
        self.with_scope(|f| {
            f.elaborate_decl(decls)?;
            f.elaborate_decl(body)
        })
    }

    fn elab_decl_seq(&mut self, decls: &[ast::Decl]) -> Result<(), Diagnostic> {
        for d in decls {
            self.elaborate_decl(d)?;
        }
        Ok(())
    }

    fn elab_decl_type(&mut self, tbs: &[ast::Typebind]) -> Result<(), Diagnostic> {
        for typebind in tbs {
            let scheme = if !typebind.tyvars.is_empty() {
                self.with_tyvars(|f| {
                    for s in typebind.tyvars.iter() {
                        let v = f.fresh_tyvar();
                        f.tyvars.push(*s, v);
                    }
                    let ty = f.elaborate_type(&typebind.ty, false)?;
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

                    Ok(s)
                })?
            } else {
                Scheme::Mono(self.elaborate_type(&typebind.ty, false)?)
            };
            self.define_type(typebind.tycon, TypeStructure::Scheme(scheme));
        }
        Ok(())
    }

    fn elab_decl_conbind(&mut self, db: &ast::Datatype) -> Result<(), Diagnostic> {
        let tycon = Tycon::new(db.tycon, db.tyvars.len());

        // This is safe to unwrap, because we already bound it.
        let type_id = self.lookup_typeid(&db.tycon).unwrap();

        // Should be safe to unwrap here as well, since the caller has bound db.tyvars
        let tyvars: Vec<TypeVar> = db
            .tyvars
            .iter()
            .map(|sym| self.lookup_tyvar(sym, false).unwrap())
            .collect();

        for (tag, con) in db.constructors.iter().enumerate() {
            if self.lookup_value(&con.label).is_some() {
                return Err(Diagnostic::error(
                    con.span,
                    format!(
                        "rebinding of data constructor {:?} is disallowed",
                        con.label
                    ),
                ));
            }

            let res = Type::Con(tycon, tyvars.iter().cloned().map(Type::Var).collect());
            let ty = match &con.data {
                Some(ty) => {
                    let dom = self.elaborate_type(ty, false)?;
                    Type::arrow(dom, res)
                }
                None => res,
            };

            let cons = Constructor {
                name: con.label,
                type_id,
                tag: tag as u32,
            };

            let s = match tyvars.len() {
                0 => Scheme::Mono(ty),
                _ => Scheme::Poly(tyvars.iter().map(|tv| tv.id).collect(), ty),
            };

            self.define_value(con.label, s, IdStatus::Con(cons));
        }

        Ok(())
    }

    fn elab_decl_datatype(&mut self, dbs: &[ast::Datatype]) -> Result<(), Diagnostic> {
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
                    f.tyvars.push(*s, v);
                }
                f.elab_decl_conbind(db)
            })?;
        }
        Ok(())
    }

    fn elab_decl_exception(&mut self, exns: &[ast::Variant]) -> Result<(), Diagnostic> {
        for exn in exns {
            match &exn.data {
                Some(ty) => {
                    let ty = self.elaborate_type(ty, false)?;
                    self.define_value(
                        exn.label,
                        Scheme::Mono(Type::arrow(ty, Type::exn())),
                        IdStatus::Exn(Constructor {
                            name: exn.label,
                            type_id: TypeId(8),
                            tag: 0,
                        }),
                    );
                }
                None => {
                    self.define_value(
                        exn.label,
                        Scheme::Mono(Type::exn()),
                        IdStatus::Exn(Constructor {
                            name: exn.label,
                            type_id: TypeId(8),
                            tag: 0,
                        }),
                    );
                }
            }
        }
        Ok(())
    }

    pub fn elaborate_decl(&mut self, decl: &ast::Decl) -> Result<(), Diagnostic> {
        use ast::DeclKind::*;
        match &decl.data {
            Datatype(dbs) => self.elab_decl_datatype(dbs),
            Type(tbs) => self.elab_decl_type(tbs),
            Function(tyvars, fbs) => unimplemented!(),
            Value(pat, expr) => {
                let pat = self.elaborate_pat(pat, false)?;
                let expr = self.elaborate_expr(expr)?;
                dbg!(&expr);
                self.unify(decl.span, &pat.ty, &expr.ty)
            }
            Exception(exns) => self.elab_decl_exception(exns),
            Fixity(fixity, bp, sym) => self.elab_decl_fixity(fixity, *bp, *sym),
            Local(decls, body) => self.elab_decl_local(decls, body),
            Seq(decls) => self.elab_decl_seq(decls),
            Do(expr) => unimplemented!(),
        }
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
