//! Elaboration from AST to an explicity typed, Core ML language
//!

use crate::arenas::{CoreArena, TypeArena};
use crate::builtin::{constructors, populate_context};
use crate::types::{Constructor, Flex, Scheme, Tycon, Type, TypeVar};
use crate::{
    Datatype, Decl, Expr, ExprId, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord, TypeId,
};
use sml_frontend::ast;
use sml_frontend::parser::precedence::{self, Fixity, Precedence, Query};
use sml_util::diagnostics::Diagnostic;
use sml_util::interner::{Interner, Symbol};
use sml_util::pretty_print::PrettyPrinter;
use sml_util::span::Span;
use sml_util::Const;
use std::collections::HashMap;
use std::fmt::Write;

pub fn check_and_elaborate<'a>(
    arena: &'a CoreArena<'a>,
    decl: &ast::Decl,
    interner: &'a Interner,
) -> (Vec<Decl<'a>>, Vec<Diagnostic>) {
    let mut check = super::check::Check::new(interner);
    check.check_decl(decl);

    let mut ctx = Context::new(arena);
    let decls = ctx.elaborate_decl(decl);

    let mut diags = check.diags;
    diags.extend(ctx.diagnostics(interner));
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
#[derive(Clone)]
pub struct Cons<'a> {
    name: Symbol,
    scheme: Scheme<'a>,
}

/// TyStr, a [`TypeStructure`] from the Defn. This is a component of the
/// Type Environment, TE
#[derive(Clone)]
pub enum TypeStructure<'a> {
    /// TyStr (t, VE), a datatype
    Datatype(Tycon, Vec<Cons<'a>>),
    /// TyStr (_, VE), a definition. Rather than include a whole VE hashmap,
    /// we can include just a single entry
    Scheme(Scheme<'a>),
    /// TyStr (t, {}), a name
    Tycon(Tycon),
}

impl<'a> TypeStructure<'a> {
    pub fn arity(&self) -> usize {
        match self {
            TypeStructure::Tycon(con) | TypeStructure::Datatype(con, _) => con.arity,
            TypeStructure::Scheme(s) => s.arity(),
        }
    }

    pub fn apply(&self, arena: &'a TypeArena<'a>, args: Vec<&'a Type<'a>>) -> &'a Type<'a> {
        match self {
            TypeStructure::Tycon(con) | TypeStructure::Datatype(con, _) => {
                arena.alloc(Type::Con(*con, args))
            }
            TypeStructure::Scheme(s) => s.apply(arena, args),
        }
    }
}

/// A partially elaborated Vec<ast::FnBinding>
struct PartialFun<'s, 'a> {
    name: Symbol,
    clauses: Vec<PartialFnBinding<'s, 'a>>,
    arity: usize,
    /// Argument types, invariant that |arg_tys| = arity
    arg_tys: Vec<&'a Type<'a>>,
    /// The resulting type
    res_ty: &'a Type<'a>,
    /// The overall flattened type, where for each ty_i in args, we have
    /// ty_0 -> ty_1 -> ... ty_arity -> res_ty
    ty: &'a Type<'a>,
}

/// A partially elaborated ast::FnBinding
struct PartialFnBinding<'s, 'a> {
    /// Function body
    expr: &'s ast::Expr,
    /// List of bound patterns `fun merge xs ys` = [xs, ys]
    pats: Vec<Pat<'a>>,
    /// A list of variables bound in `pats`, and fresh type variables
    /// to be associated with those symbols
    bindings: Vec<(Symbol, &'a Type<'a>)>,
    span: Span,
}

/// An environment scope, that can hold a collection of type and expr bindings
#[derive(Default, Debug)]
pub struct Namespace {
    parent: Option<usize>,
    depth: usize,
    types: HashMap<Symbol, TypeId>,
    values: HashMap<Symbol, ExprId>,
    infix: HashMap<Symbol, Fixity>,
}

/// An elaboration context, holding the namespace and type definitions
/// for the program we are elaborating
pub struct Context<'a> {
    // stacks for alpha-renaming of explicity named type variables 'a
    tyvars: Vec<(Symbol, &'a TypeVar<'a>)>,

    // A list of [`Namespace`] structs, but this is a not stack. Namespaces can
    // be pushed onto the end, but they may never be deleted or re-ordered
    namespaces: Vec<Namespace>,
    // An index into `namespaces`, representing the current scope
    current: usize,

    // All defined types live here, indexed by `TypeId`
    types: Vec<TypeStructure<'a>>,
    // All defined values live here, indexed by `ExprId`
    values: Vec<(Scheme<'a>, IdStatus)>,

    tyvar_rank: usize,
    local_depth: usize,

    pub(crate) arena: &'a CoreArena<'a>,
    pub elab_errors: Vec<ElabError>,
    unification_errors: Vec<CantUnify<'a>>,
}

impl Namespace {
    pub fn with_parent(id: usize, depth: usize) -> Namespace {
        Namespace {
            parent: Some(id),
            depth,
            types: HashMap::with_capacity(32),
            values: HashMap::with_capacity(64),
            infix: HashMap::with_capacity(16),
        }
    }
}

impl<'a> Context<'a> {
    pub fn new(arena: &'a CoreArena<'a>) -> Context<'a> {
        let mut ctx = Context {
            tyvars: Vec::default(),
            namespaces: Vec::default(),
            current: 0,
            tyvar_rank: 0,
            local_depth: 0,
            types: Vec::default(),
            values: Vec::default(),
            elab_errors: Vec::default(),
            unification_errors: Vec::default(),
            arena,
        };
        ctx.namespaces.push(Namespace::default());
        populate_context(&mut ctx);
        ctx.elab_decl_fixity(&ast::Fixity::Infixr, 4, constructors::C_CONS.name);
        ctx
    }

    /// Keep track of the type variable stack, while executing the combinator
    /// function `f` on `self`. Any stack growth is popped off after `f`
    /// returns.
    fn with_tyvars<T, F: FnMut(&mut Context<'a>) -> T>(&mut self, mut f: F) -> T {
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
    fn with_scope<T, F: FnOnce(&mut Context<'a>) -> T>(&mut self, f: F) -> T {
        let prev = self.current;
        let next = self.namespaces.len();
        self.namespaces
            .push(Namespace::with_parent(prev, self.scope_depth() + 1));
        self.current = next;
        let r = f(self);

        self.current = prev;
        r
    }

    #[inline]
    fn scope_depth(&self) -> usize {
        self.namespaces[self.current].depth
    }

    /// Globally define a type
    pub(crate) fn define_type(&mut self, sym: Symbol, tystr: TypeStructure<'a>) -> TypeId {
        let id = TypeId(self.types.len() as u32);
        self.types.push(tystr);
        let ns = if self.local_depth > 0 {
            self.namespaces[self.current].parent.unwrap_or(self.current)
        } else {
            self.current
        };
        self.namespaces[ns].types.insert(sym, id);
        id
    }

    /// Globally define a value
    pub(crate) fn define_value(
        &mut self,
        sym: Symbol,
        span: Span,
        scheme: Scheme<'a>,
        status: IdStatus,
    ) -> ExprId {
        let id = ExprId(self.values.len() as u32);
        let scheme = self.check_scheme(span, scheme);
        self.values.push((scheme, status));
        let ns = if self.local_depth > 0 {
            self.namespaces[self.current].parent.unwrap_or(self.current)
        } else {
            self.current
        };
        self.namespaces[ns].values.insert(sym, id);
        id
    }

    fn check_scheme(&mut self, span: Span, scheme: Scheme<'a>) -> Scheme<'a> {
        if self.local_depth > 0 {
            // is scope_depth() - 1 correct, or do we modify by local_depth
            match scheme {
                Scheme::Mono(ty) => self.check_type_names(span, ty, self.scope_depth() - 1),
                Scheme::Poly(_, ty) => self.check_type_names(span, ty, self.scope_depth() - 1),
            }
        }
        scheme
    }

    /// Unbind a value, replacing it's currently defined scheme with
    /// Scheme::Mono('a), where 'a is some fresh type variable
    ///
    /// # Panics
    ///
    /// This will panic if `sym` is not defined in the current namespace
    /// tree
    fn unbind_value(&mut self, sym: Symbol) {
        let id = self.namespaces[self.current]
            .values
            .get(&sym)
            .expect("error: redefine_value");
        let s = Scheme::Mono(self.fresh_tyvar());
        let _ = std::mem::replace(&mut self.values[id.0 as usize].0, s);
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

    /// Return the index of a symbol into the global type definition vector
    fn lookup_type_id(&self, sym: &Symbol) -> Option<TypeId> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.types.get(sym) {
                Some(idx) => return Some(*idx),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    fn lookup_type(&self, sym: &Symbol) -> Option<&TypeStructure<'a>> {
        Some(&self.types[self.lookup_type_id(sym)?.0 as usize])
    }

    fn lookup_value(&self, sym: &Symbol) -> Option<&(Scheme<'a>, IdStatus)> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.values.get(sym) {
                Some(idx) => return Some(&self.values[idx.0 as usize]),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    fn lookup_tyvar(&mut self, s: &Symbol, allow_unbound: bool) -> Option<&'a TypeVar<'a>> {
        for (sym, tv) in self.tyvars.iter().rev() {
            if sym == s {
                return Some(tv);
            }
        }
        if allow_unbound {
            let v = self.arena.types.fresh_type_var(self.tyvar_rank);
            self.tyvars.push((*s, v));
            Some(v)
        } else {
            None
        }
    }

    pub(crate) fn fresh_tyvar(&self) -> &'a Type<'a> {
        self.arena.types.fresh_var(self.tyvar_rank)
    }

    pub(crate) fn fresh_var(&self) -> Symbol {
        self.arena.exprs.allocate_id()
    }

    fn const_ty(&self, c: &Const) -> &'a Type<'a> {
        match c {
            Const::Char(_) => self.arena.types.char(),
            Const::Int(_) => self.arena.types.int(),
            Const::String(_) => self.arena.types.string(),
            Const::Unit => self.arena.types.unit(),
        }
    }

    /// Generic function to elaborate an ast::Row<T> into a core::Row<S>
    /// where T might be ast::Type and S is core::Type, for instance
    fn elab_row<T, S, F: FnMut(&mut Context<'a>, &T) -> S>(
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

    pub fn diagnostics(&mut self, interner: &Interner) -> Vec<Diagnostic> {
        // let mut diags = std::mem::replace(&mut self.diags, Vec::new());
        let mut diags = Vec::new();
        let mut pp = PrettyPrinter::new(interner);
        diags.extend(
            self.elab_errors
                .drain(..)
                .filter_map(|e| e.convert_err(&mut pp)),
        );
        diags.extend(
            self.unification_errors
                .drain(..)
                .filter_map(|e| e.convert_err(&mut pp)),
        );
        diags
    }
}

pub struct ElabError {
    sp: Span,
    message: String,
    kind: ErrorKind,
}

pub enum ErrorKind {
    Unbound(Symbol),
    Rebound(Symbol),
    Escape(Symbol),
    Arity(usize, usize),
    Redundant,
    Inexhaustive,
    Generalize,
    Message,
}

impl ElabError {
    pub fn new(sp: Span, msg: &str) -> ElabError {
        ElabError {
            sp,
            message: msg.into(),
            kind: ErrorKind::Message,
        }
    }

    pub fn kind(mut self, kind: ErrorKind) -> Self {
        self.kind = kind;
        self
    }

    fn convert_err(self, pp: &mut PrettyPrinter<'_>) -> Option<Diagnostic> {
        let mut buffer = String::new();
        match self.kind {
            ErrorKind::Unbound(sym) => {
                write!(&mut buffer, "unbound {}: ", self.message).ok()?;
                pp.print(&sym).write_fmt(&mut buffer).ok()?;
            }
            ErrorKind::Rebound(sym) => {
                write!(&mut buffer, "rebound {}: ", self.message).ok()?;
                pp.print(&sym).write_fmt(&mut buffer).ok()?;
                return Some(Diagnostic::warn(self.sp, buffer));
            }
            ErrorKind::Escape(sym) => {
                write!(&mut buffer, "{}: ", self.message).ok()?;
                pp.print(&sym).write_fmt(&mut buffer).ok()?;
            }
            ErrorKind::Arity(expect, got) => {
                write!(
                    &mut buffer,
                    "arity mismatch in {}. Expected {}, got {}",
                    self.message, expect, got
                )
                .ok()?;
            }
            ErrorKind::Generalize => {
                return Some(Diagnostic::warn(self.sp, self.message));
            }
            _ => {
                buffer = self.message;
            }
        }
        Some(Diagnostic::error(self.sp, buffer))
    }
}

struct CantUnify<'a> {
    pub ty1: &'a Type<'a>,
    pub ty2: &'a Type<'a>,
    pub sp1: Option<Span>,
    pub sp2: Option<Span>,
    pub message: String,
    pub reason: String,
    pub originating: Option<Span>,
}

impl<'a> CantUnify<'a> {
    pub fn new(ty1: &'a Type<'a>, ty2: &'a Type<'a>) -> CantUnify<'a> {
        CantUnify {
            ty1,
            ty2,
            sp1: None,
            sp2: None,
            message: String::new(),
            reason: String::new(),
            originating: None,
        }
    }

    pub fn message<S: Into<String>>(mut self, s: S) -> Self {
        self.message = s.into();
        self
    }

    pub fn reason<S: Into<String>>(mut self, s: S) -> Self {
        self.reason = s.into();
        self
    }

    pub fn span(mut self, sp: Span) -> Self {
        self.originating = Some(sp);
        self
    }

    pub fn add_spans(mut self, s1: Span, s2: Span) -> Self {
        self.sp1 = Some(s1);
        self.sp2 = Some(s2);
        self
    }

    fn convert_err(self, pp: &mut PrettyPrinter<'_>) -> Option<Diagnostic> {
        let mut map = HashMap::new();

        let mut buffer = String::new();
        let sp = self.originating?;
        write!(
            &mut buffer,
            "Type unification: {}\n{}: ",
            self.message, self.reason
        )
        .ok()?;
        self.ty1
            .print_rename(pp, &mut map)
            .write_fmt(&mut buffer)
            .ok()?;
        write!(&mut buffer, ", ").ok()?;
        self.ty2
            .print_rename(pp, &mut map)
            .write_fmt(&mut buffer)
            .ok()?;
        Some(Diagnostic::error(sp, buffer))
    }
}

impl<'a> Context<'a> {
    /// Note that this can only be called once per type variable!
    fn bind<F>(&mut self, var: &'a TypeVar<'a>, ty: &'a Type<'a>, f: &F)
    where
        F: Fn() -> CantUnify<'a>,
    {
        if let Type::Var(v2) = ty {
            // TODO: Ensure that testing on id alone is ok - I believe it should be
            if v2.id == var.id {
                return;
            }
        }
        if ty.occurs_check(var) {
            let err = f().reason("Cyclic type detected");
            self.unification_errors.push(err);
        } else {
            // Move into else block, so that even if occurs check fails, we can
            // proceed with type checking without creating a cycle
            match ty {
                Type::Flex(flex) => match flex.ty() {
                    Some(ty) => var.data.set(Some(ty)),
                    None => var.data.set(Some(ty)),
                },
                _ => var.data.set(Some(ty)),
            }
        }
    }

    fn unify_records<F>(
        &mut self,
        r1: &SortedRecord<&'a Type<'a>>,
        r2: &SortedRecord<&'a Type<'a>>,
        ty1: &'a Type<'a>,
        ty2: &'a Type<'a>,
        f: &F,
    ) where
        F: Fn(CantUnify<'a>) -> CantUnify<'a>,
    {
        if r1.len() != r2.len() {
            let err =
                f(CantUnify::new(ty1, ty2)).reason("Record types have differing number of fields");
            self.unification_errors.push(err);
            return;
        }

        for (ra, rb) in r1.iter().zip(r2.iter()) {
            if ra.label != rb.label {
                let err = f(CantUnify::new(&ra.data, &rb.data))
                    .reason("Record labels don't match")
                    .add_spans(ra.span, rb.span);
                self.unification_errors.push(err);
                return;
            }
            self.unify(&ra.data, &rb.data, f); //&|c| f(c).reason("Record fields have differing types").add_spans(ra.span, rb.span));
        }
    }

    /// Check that every constraint in the flexible record type unifies
    /// with the rigid record
    fn one_flex<F>(
        &mut self,
        rigid: &SortedRecord<&'a Type<'a>>,
        flex: &Flex<'a>,
        rigid_ty: &'a Type<'a>,
        flex_ty: &'a Type<'a>,
        f: &F,
    ) where
        F: Fn(CantUnify<'a>) -> CantUnify<'a>,
    {
        for field in flex.constraints.iter() {
            match rigid.contains(&field.label) {
                Some(row) => {
                    self.unify(&field.data, &row.data, f);
                }
                None => {
                    let err = f(CantUnify::new(rigid_ty, flex_ty))
                        .reason("Flexible record constraint not in rigid record");
                    self.unification_errors.push(err);
                    return;
                }
            }
        }
        flex.unified.set(Some(rigid_ty));
    }

    fn unify<F>(&mut self, a: &'a Type<'a>, b: &'a Type<'a>, f: &F)
    where
        F: Fn(CantUnify<'a>) -> CantUnify<'a>,
    {
        match (a, b) {
            (Type::Var(a1), Type::Var(b1)) => match (a1.ty(), b1.ty()) {
                (Some(a), Some(b)) => self.unify(a, b, f),
                (Some(a), None) => self.unify(a, b, f),
                (None, Some(b)) => self.unify(a, b, f),
                (None, None) => self.bind(a1, b, &|| f(CantUnify::new(a, b))),
            },
            (Type::Var(a_var), b) => match a_var.ty() {
                Some(ty) => self.unify(ty, b, f),
                None => self.bind(a_var, b, &|| f(CantUnify::new(a, b))),
            },
            (a, Type::Var(b_var)) => match b_var.ty() {
                Some(ty) => self.unify(a, ty, f),
                None => self.bind(b_var, a, &|| f(CantUnify::new(a, b))),
            },
            (Type::Con(tc1, a_args), Type::Con(tc2, b_args)) => {
                if tc1 != tc2 {
                    let err = f(CantUnify::new(a, b)).reason("Type constructors differ");
                    self.unification_errors.push(err);
                } else if a_args.len() != b_args.len() {
                    let err = f(CantUnify::new(a, b))
                        .reason("Argument lengths to type constructors differ");
                    self.unification_errors.push(err);
                } else {
                    for (c, d) in a_args.iter().zip(b_args) {
                        self.unify(c, d, f);
                    }
                }
            }
            (Type::Record(r1), Type::Record(r2)) => self.unify_records(r1, r2, a, b, f),
            (Type::Flex(flex), Type::Record(rec)) => match flex.ty() {
                Some(r1) => self.unify(r1, b, f),
                None => self.one_flex(rec, flex, b, a, f),
            },
            (Type::Record(rec), Type::Flex(flex)) => match flex.ty() {
                Some(r1) => self.unify(r1, b, f),
                None => self.one_flex(rec, flex, a, b, f),
            },
            (a, b) => {
                let err = f(CantUnify::new(a, b)).reason("Can't unify these types");
                self.unification_errors.push(err);
            }
        }
    }

    fn unify_list(&mut self, sp: Span, tys: &[&'a Type<'a>]) {
        if tys.len() == 1 {
            return;
        }
        let fst = &tys[0];
        for ty in tys {
            self.unify(ty, fst, &|c| {
                c.span(sp).message("List has items of differing types")
            });
        }
    }

    fn generalize(&self, ty: &'a Type<'a>) -> Scheme<'a> {
        let ftv = ty.ftv_rank(self.tyvar_rank);

        match ftv.len() {
            0 => Scheme::Mono(ty),
            _ => Scheme::Poly(ftv.into_iter().collect(), ty),
        }
    }

    fn instantiate(&self, scheme: &Scheme<'a>) -> &'a Type<'a> {
        match scheme {
            Scheme::Mono(ty) => ty,
            Scheme::Poly(vars, ty) => {
                let map = vars.iter().map(|v| (*v, self.fresh_tyvar())).collect();
                ty.apply(&self.arena.types, &map)
            }
        }
    }

    fn check_type_names(&mut self, sp: Span, ty: &'a Type<'a>, depth: usize) {
        let mut names = Vec::new();
        ty.visit(|f| {
            if let Type::Con(tc, _) = f {
                names.push(*tc);
            }
        });

        for tycon in names {
            if tycon.scope_depth > depth {
                self.elab_errors.push(
                    ElabError::new(sp, "type escapes scope").kind(ErrorKind::Escape(tycon.name)),
                )
            }
        }
    }

    fn elaborate_type(&mut self, ty: &ast::Type, allow_unbound: bool) -> &'a Type<'a> {
        use ast::TypeKind::*;
        match &ty.data {
            Var(s) => match self.lookup_tyvar(s, allow_unbound) {
                Some(tv) => self.arena.types.alloc(Type::Var(tv)),
                None => {
                    self.elab_errors.push(
                        ElabError::new(ty.span, "type variable").kind(ErrorKind::Unbound(*s)),
                    );

                    self.fresh_tyvar()
                }
            },
            Con(s, args) => {
                let args = args
                    .iter()
                    .map(|ty| self.elaborate_type(&ty, allow_unbound))
                    .collect::<Vec<_>>();

                let con = match self.lookup_type(s) {
                    Some(t) => t.clone(),
                    None => {
                        self.elab_errors.push(
                            ElabError::new(ty.span, "type variable").kind(ErrorKind::Unbound(*s)),
                        );
                        TypeStructure::Tycon(Tycon {
                            name: self.fresh_var(),
                            arity: args.len(),
                            scope_depth: self.scope_depth(),
                        })
                    }
                };

                if con.arity() != args.len() {
                    self.elab_errors.push(
                        ElabError::new(ty.span, "type constructor")
                            .kind(ErrorKind::Arity(con.arity(), args.len())),
                    );
                }
                con.apply(&self.arena.types, args)
            }
            Record(rows) => self.arena.types.alloc(Type::Record(SortedRecord::new(
                rows.iter()
                    .map(|row| self.elab_row(|f, r| f.elaborate_type(r, allow_unbound), row))
                    .collect::<Vec<Row<_>>>(),
            ))),
        }
    }
}

impl<'a> Context<'a> {
    fn elab_if(&mut self, sp: Span, e1: Expr<'a>, e2: Expr<'a>, e3: Expr<'a>) -> Expr<'a> {
        let tru = Rule {
            pat: Pat::new(
                self.arena
                    .pats
                    .alloc(PatKind::App(constructors::C_TRUE, None)),
                self.arena.types.bool(),
                e2.span,
            ),
            expr: e2,
        };
        let fls = Rule {
            pat: Pat::new(
                self.arena
                    .pats
                    .alloc(PatKind::App(constructors::C_FALSE, None)),
                self.arena.types.bool(),
                e3.span,
            ),
            expr: e3,
        };

        self.unify(e1.ty, self.arena.types.bool(), &|c| {
            c.span(e1.span)
                .message("conditional doesn't have type `bool`")
        });
        self.unify(e2.ty, e3.ty, &|c| {
            c.span(e2.span)
                .add_spans(e2.span, e3.span)
                .message("branches of `if` expression don't have the same types")
        });

        Expr::new(
            self.arena.exprs.alloc(ExprKind::Case(e1, vec![tru, fls])),
            e2.ty,
            sp,
        )
    }

    fn elab_rule(&mut self, rule: &ast::Rule, bind: bool) -> Rule<'a> {
        let (pat, _) = self.elaborate_pat(&rule.pat, bind);
        let expr = self.elaborate_expr(&rule.expr);
        Rule { pat, expr }
    }

    fn elab_rules(&mut self, sp: Span, rules: &[ast::Rule]) -> (Vec<Rule<'a>>, &'a Type<'a>) {
        self.with_scope(|ctx| {
            let rules = rules
                .iter()
                .map(|r| ctx.elab_rule(r, true))
                .collect::<Vec<Rule>>();

            let mut rtys = rules
                .iter()
                .map(|r| ctx.arena.types.arrow(r.pat.ty, r.expr.ty))
                .collect::<Vec<_>>();

            ctx.unify_list(sp, &rtys);
            let fst = rtys.remove(0);
            (rules, fst)
        })
    }

    fn elaborate_expr(&mut self, expr: &ast::Expr) -> Expr<'a> {
        match &expr.data {
            ast::ExprKind::Andalso(e1, e2) => {
                let e1 = self.elaborate_expr(e1);
                let e2 = self.elaborate_expr(e2);
                let fls = Expr::new(
                    self.arena
                        .exprs
                        .alloc(ExprKind::Con(constructors::C_FALSE, vec![])),
                    self.arena.types.bool(),
                    expr.span,
                );
                self.elab_if(expr.span, e1, e2, fls)
            }
            ast::ExprKind::App(e1, e2) => {
                let e1 = self.elaborate_expr(e1);
                let e2 = self.elaborate_expr(e2);

                let f = self.fresh_tyvar();
                self.unify(e1.ty, self.arena.types.arrow(e2.ty, f), &|c| {
                    c.span(expr.span)
                        .add_spans(e1.span, e2.span)
                        .message("can't unify function with argument types")
                });
                Expr::new(self.arena.exprs.alloc(ExprKind::App(e1, e2)), f, expr.span)
            }
            ast::ExprKind::Case(scrutinee, rules) => {
                let casee = self.elaborate_expr(scrutinee);

                let (rules, ty) = self.elab_rules(expr.span, rules);

                let (arg, res) = match ty.de_arrow() {
                    Some((a, r)) => (a, r),
                    None => {
                        let (dom, rng) = (self.fresh_tyvar(), self.fresh_tyvar());
                        let arr = self.arena.types.arrow(dom, rng);
                        self.unify(ty, arr, &|c| {
                            c.span(expr.span)
                                .message("something wrong with match rules")
                        });
                        (dom, rng)
                    }
                };

                self.unify(casee.ty, arg, &|c| {
                    c.span(scrutinee.span)
                        .message("`case` expression and patterns don't have the same type")
                });
                crate::match_compile::case(self, casee, res, rules, scrutinee.span)
            }
            ast::ExprKind::Const(c) => {
                let ty = self.const_ty(c);
                Expr::new(self.arena.exprs.alloc(ExprKind::Const(*c)), ty, expr.span)
            }
            ast::ExprKind::Constraint(ex, ty) => {
                let ex = self.elaborate_expr(ex);
                let ty_ = self.elaborate_type(ty, false);
                self.unify(ex.ty, ty_, &|c| {
                    c.span(expr.span)
                        .add_spans(ex.span, ty.span)
                        .message("expression type and constraint don't match")
                });
                ex
            }
            ast::ExprKind::FlatApp(exprs) => {
                let p = match self.expr_precedence(exprs.clone()) {
                    Ok(p) => p,
                    Err(err) => {
                        match err {
                            precedence::Error::EndsInfix => self.elab_errors.push(ElabError::new(
                                expr.span,
                                "application expr ends with an infix operator",
                            )),
                            precedence::Error::InfixInPrefix => {
                                self.elab_errors.push(ElabError::new(
                                    expr.span,
                                    "application expr starts with an infix operator",
                                ))
                            }
                            precedence::Error::SamePrecedence => {
                                self.elab_errors.push(ElabError::new(
                                    expr.span,
                                    "application expr mixes operators of equal precedence",
                                ))
                            }
                            precedence::Error::InvalidOperator => {
                                self.elab_errors.push(ElabError::new(
                                    expr.span,
                                    "application expr doesn't contain infix operator",
                                ))
                            }
                        }
                        // Return a dummy variable so that we can continue elaboration
                        ast::Expr::new(
                            ast::ExprKind::Var(self.arena.exprs.allocate_id()),
                            Span::dummy(),
                        )
                    }
                };
                self.elaborate_expr(&p)
            }
            ast::ExprKind::Fn(rules) => {
                let (rules, ty) = self.elab_rules(expr.span, rules);

                let (arg, res) = match ty.de_arrow() {
                    Some((a, r)) => (a, r),
                    None => {
                        let (dom, rng) = (self.fresh_tyvar(), self.fresh_tyvar());
                        let arr = self.arena.types.arrow(dom, rng);
                        self.unify(ty, arr, &|c| {
                            c.span(expr.span)
                                .message("something wrong with match rules")
                        });
                        (dom, rng)
                    }
                };

                let gensym = self.fresh_var();
                let casee = self.arena.expr_var(gensym, arg);
                let body = crate::match_compile::case(self, casee, res, rules, expr.span);

                Expr::new(
                    self.arena.exprs.alloc(ExprKind::Lambda(Lambda {
                        arg: gensym,
                        ty: arg,
                        body,
                    })),
                    ty,
                    expr.span,
                )
            }
            ast::ExprKind::Handle(tryy, rules) => {
                let tryy = self.elaborate_expr(tryy);
                let (rules, ty) = self.elab_rules(expr.span, rules);

                let (arg, res) = match ty.de_arrow() {
                    Some((a, r)) => (a, r),
                    None => {
                        let (dom, rng) = (self.fresh_tyvar(), self.fresh_tyvar());
                        let arr = self.arena.types.arrow(dom, rng);
                        self.unify(ty, arr, &|c| {
                            c.span(expr.span)
                                .message("something wrong with match rules")
                        });
                        (dom, rng)
                    }
                };

                self.unify(tryy.ty, res, &|c| {
                    c.span(tryy.span)
                        .message("`try` expression and handler result types don't match")
                });
                self.unify(arg, self.arena.types.exn(), &|c| {
                    c.span(expr.span)
                        .message("handler match rules don't have `exn` type")
                });
                // tryy handle case $gensym of |...
                let gensym = self.fresh_var();
                let scrutinee = self.arena.expr_var(gensym, arg);
                let body = crate::match_compile::case(self, scrutinee, res, rules, expr.span);
                Expr::new(
                    self.arena.exprs.alloc(ExprKind::Handle(tryy, gensym, body)),
                    res,
                    expr.span,
                )
            }
            ast::ExprKind::If(e1, e2, e3) => {
                let e1 = self.elaborate_expr(e1);
                let e2 = self.elaborate_expr(e2);
                let e3 = self.elaborate_expr(e3);
                self.elab_if(expr.span, e1, e2, e3)
            }
            ast::ExprKind::Let(decls, body) => {
                let mut elab = Vec::new();
                let body = self.with_scope(|ctx| {
                    for decl in decls {
                        ctx.elaborate_decl_inner(decl, &mut elab);
                    }
                    ctx.elaborate_expr(body)
                });
                self.check_type_names(body.span, body.ty, self.scope_depth());
                Expr::new(
                    self.arena.exprs.alloc(ExprKind::Let(elab, body)),
                    body.ty,
                    expr.span,
                )
            }
            ast::ExprKind::List(exprs) => {
                let exprs = exprs
                    .iter()
                    .map(|ex| self.elaborate_expr(ex))
                    .collect::<Vec<_>>();

                let tys = exprs.iter().map(|ex| ex.ty).collect::<Vec<_>>();
                self.unify_list(expr.span, &tys);
                // Pick the first type, since that was what everything was unified against
                let ty = self.arena.types.list(tys[0]);
                Expr::new(self.arena.exprs.alloc(ExprKind::List(exprs)), ty, expr.span)
            }
            ast::ExprKind::Orelse(e1, e2) => {
                let e1 = self.elaborate_expr(e1);
                let e2 = self.elaborate_expr(e2);

                let tru = Expr::new(
                    self.arena
                        .exprs
                        .alloc(ExprKind::Con(constructors::C_TRUE, vec![])),
                    self.arena.types.bool(),
                    expr.span,
                );
                self.elab_if(expr.span, e1, tru, e2)
            }
            ast::ExprKind::Primitive(prim) => {
                let name = prim.sym;
                let ty = self.elaborate_type(&prim.ty, false);

                Expr::new(
                    self.arena.exprs.alloc(ExprKind::Primitive(name)),
                    ty,
                    expr.span,
                )
            }
            ast::ExprKind::Raise(expr) => {
                let ty = self.fresh_tyvar();
                let ex = self.elaborate_expr(expr);
                self.unify(ex.ty, self.arena.types.exn(), &|c| {
                    c.span(expr.span)
                        .message("expression in `raise` is not an exception")
                });
                Expr::new(self.arena.exprs.alloc(ExprKind::Raise(ex)), ty, expr.span)
            }
            ast::ExprKind::Record(rows) => {
                let rows = rows
                    .into_iter()
                    .map(|r| self.elab_row(|ec, r| ec.elaborate_expr(r), r))
                    .collect::<Vec<Row<Expr>>>();
                let tys = rows
                    .iter()
                    .map(|r| r.fmap(|x| x.ty))
                    .collect::<Vec<Row<_>>>();

                let ty = self.arena.types.alloc(Type::Record(SortedRecord::new(tys)));
                Expr::new(
                    self.arena.exprs.alloc(ExprKind::Record(rows)),
                    ty,
                    expr.span,
                )
            }
            ast::ExprKind::Selector(s) => {
                let row = ast::Row {
                    label: *s,
                    data: ast::Pat::new(ast::PatKind::Variable(*s), Span::dummy()),
                    span: Span::dummy(),
                };
                let pat = ast::Pat::new(ast::PatKind::Record(vec![row], true), Span::dummy());
                let inner = ast::Expr::new(ast::ExprKind::Var(*s), Span::dummy());
                self.elaborate_expr(&ast::Expr::new(
                    ast::ExprKind::Fn(vec![ast::Rule {
                        pat,
                        expr: inner,
                        span: expr.span,
                    }]),
                    expr.span,
                ))
            }
            ast::ExprKind::Seq(exprs) => {
                let exprs = exprs
                    .iter()
                    .map(|ex| self.elaborate_expr(ex))
                    .collect::<Vec<_>>();
                // exprs.len() >= 2, but we'll use saturating_sub just to be safe
                for ex in &exprs[..exprs.len().saturating_sub(2)] {
                    self.unify(ex.ty, self.arena.types.unit(), &|c| {
                        c.span(expr.span)
                            .message("expressions in a sequence must have type `unit`")
                    });
                }
                let ty = exprs.last().unwrap().ty;
                Expr::new(self.arena.exprs.alloc(ExprKind::Seq(exprs)), ty, expr.span)
            }
            ast::ExprKind::Var(sym) => match self.lookup_value(sym) {
                Some((scheme, _)) => {
                    let ty = self.instantiate(scheme);
                    // println!("inst {:?} [{:?}] -> {:?}", sym, scheme, ty);
                    Expr::new(
                        self.arena
                            .exprs
                            .alloc(ExprKind::Var(std::cell::Cell::new(*sym))),
                        ty,
                        expr.span,
                    )
                }
                None => {
                    self.elab_errors
                        .push(ElabError::new(expr.span, "variable").kind(ErrorKind::Unbound(*sym)));
                    Expr::new(
                        self.arena.exprs.fresh_var(),
                        self.arena.types.fresh_var(self.tyvar_rank),
                        expr.span,
                    )
                }
            },
            _ => panic!(Diagnostic::error(
                expr.span,
                format!("unknown expr {:?}", expr),
            )),
        }
    }
}

impl<'a> Context<'a> {
    fn elaborate_pat(
        &mut self,
        pat: &ast::Pat,
        bind: bool,
    ) -> (Pat<'a>, Vec<(Symbol, &'a Type<'a>)>) {
        let mut bindings = Vec::new();
        (self.elaborate_pat_inner(pat, bind, &mut bindings), bindings)
    }

    fn delist(&self, pats: Vec<Pat<'a>>, ty: &'a Type<'a>, sp: Span) -> Pat<'a> {
        let nil = Pat::new(
            self.arena
                .pats
                .alloc(PatKind::App(constructors::C_NIL, None)),
            ty,
            sp,
        );
        pats.into_iter().fold(nil, |xs, x| {
            let cons = Pat::new(self.arena.pats.tuple([x, xs].iter().copied()), x.ty, x.span);
            Pat::new(
                self.arena
                    .pats
                    .alloc(PatKind::App(constructors::C_CONS, Some(cons))),
                ty,
                sp,
            )
        })
    }

    fn elaborate_pat_inner(
        &mut self,
        pat: &ast::Pat,
        bind: bool,
        bindings: &mut Vec<(Symbol, &'a Type<'a>)>,
    ) -> Pat<'a> {
        use ast::PatKind::*;
        match &pat.data {
            App(con, p) => {
                let p = self.elaborate_pat_inner(p, bind, bindings);
                match self.lookup_value(con).cloned() {
                    Some((scheme, IdStatus::Exn(constr)))
                    | Some((scheme, IdStatus::Con(constr))) => {
                        let inst = self.instantiate(&scheme);

                        let (arg, res) = match inst.de_arrow() {
                            Some((a, r)) => (a, r),
                            None => {
                                let (dom, rng) = (self.fresh_tyvar(), self.fresh_tyvar());
                                let arr = self.arena.types.arrow(dom, rng);
                                self.unify(inst, arr, &|c| {
                                    c.span(pat.span).message(
                                        "can't unify pattern application and argument types",
                                    )
                                });
                                (dom, rng)
                            }
                        };
                        self.unify(arg, p.ty, &|c| {
                            c.span(pat.span)
                                .message("pattern constructor and argument have different types")
                        });
                        Pat::new(
                            self.arena.pats.alloc(PatKind::App(constr, Some(p))),
                            res,
                            pat.span,
                        )
                    }
                    _ => {
                        self.elab_errors.push(ElabError::new(
                            pat.span,
                            "Non-constructor applied to pattern",
                        ));
                        Pat::new(
                            self.arena.pats.wild(),
                            self.arena.types.fresh_var(self.tyvar_rank),
                            pat.span,
                        )
                    }
                }
            }
            Ascribe(p, ty) => {
                let p = self.elaborate_pat_inner(p, bind, bindings);
                let ty_ = self.elaborate_type(ty, true);
                self.unify(p.ty, ty_, &|c| {
                    c.span(pat.span)
                        .add_spans(p.span, ty.span)
                        .message("pattern type and constraint type don't match")
                });
                p
            }
            Const(c) => {
                let ty = self.const_ty(c);
                Pat::new(self.arena.pats.alloc(PatKind::Const(*c)), ty, pat.span)
            }
            FlatApp(pats) => {
                let p = match self.pat_precedence(pats.clone()) {
                    Ok(p) => p,
                    Err(err) => {
                        match err {
                            precedence::Error::EndsInfix => self.elab_errors.push(ElabError::new(
                                pat.span,
                                "application pattern ends with an infix operator",
                            )),
                            precedence::Error::InfixInPrefix => {
                                self.elab_errors.push(ElabError::new(
                                    pat.span,
                                    "application pattern starts with an infix operator",
                                ))
                            }
                            precedence::Error::SamePrecedence => {
                                self.elab_errors.push(ElabError::new(
                                    pat.span,
                                    "application pattern mixes operators of equal precedence",
                                ))
                            }
                            precedence::Error::InvalidOperator => {
                                self.elab_errors.push(ElabError::new(
                                    pat.span,
                                    "application pattern doesn't contain infix operator",
                                ))
                            }
                        }

                        // attempt error recovery
                        ast::Pat::new(ast::PatKind::Wild, pat.span)
                    }
                };
                self.elaborate_pat_inner(&p, bind, bindings)
            }
            List(pats) => {
                let pats: Vec<Pat> = pats
                    .into_iter()
                    .map(|p| self.elaborate_pat_inner(p, bind, bindings))
                    .collect::<Vec<Pat>>();

                let tys = pats.iter().map(|p| p.ty).collect::<Vec<_>>();
                self.unify_list(pat.span, &tys);
                self.delist(pats, self.arena.types.list(tys[0]), pat.span)
            }
            Record(rows, flex) => {
                let pats: Vec<Row<Pat>> = rows
                    .iter()
                    .map(|r| self.elab_row(|f, rho| f.elaborate_pat_inner(rho, bind, bindings), r))
                    .collect::<Vec<_>>();

                let tys = pats
                    .iter()
                    .map(|p| Row {
                        label: p.label,
                        span: p.span,
                        data: p.data.ty,
                    })
                    .collect::<Vec<Row<_>>>();

                let ty = match flex {
                    false => self.arena.types.alloc(Type::Record(SortedRecord::new(tys))),
                    true => self
                        .arena
                        .types
                        .alloc(Type::Flex(Flex::new(SortedRecord::new(tys)))),
                };
                Pat::new(
                    self.arena
                        .pats
                        .alloc(PatKind::Record(SortedRecord::new(pats))),
                    ty,
                    pat.span,
                )
            }
            Variable(sym) => match self.lookup_value(sym) {
                // Rule 35
                Some((scheme, IdStatus::Exn(c))) | Some((scheme, IdStatus::Con(c))) => {
                    let ty = self.instantiate(scheme);
                    Pat::new(self.arena.pats.alloc(PatKind::App(*c, None)), ty, pat.span)
                }
                _ => {
                    // Rule 34
                    let mut name = *sym;
                    if bindings.iter().map(|(s, _)| s).any(|s| s == sym) {
                        name = self.fresh_var();
                        self.elab_errors.push(ElabError::new(
                            pat.span,
                            "duplicate variable in pattern, emitting bogus value",
                        ));
                    }
                    let ty = self.fresh_tyvar();
                    if bind {
                        self.define_value(name, pat.span, Scheme::Mono(ty), IdStatus::Var);
                    }

                    bindings.push((name, ty));
                    Pat::new(self.arena.pats.alloc(PatKind::Var(name)), ty, pat.span)
                }
            },
            Wild => Pat::new(self.arena.pats.wild(), self.fresh_tyvar(), pat.span),
        }
    }
}

impl<'a> Context<'a> {
    fn elab_decl_fixity(&mut self, fixity: &ast::Fixity, bp: u8, sym: Symbol) {
        let fix = match fixity {
            ast::Fixity::Infix => Fixity::Infix(bp, bp + 1),
            ast::Fixity::Infixr => Fixity::Infix(bp + 1, bp),
            ast::Fixity::Nonfix => Fixity::Nonfix,
        };
        self.namespaces[self.current].infix.insert(sym, fix);
    }

    fn elab_decl_local(&mut self, decls: &ast::Decl, body: &ast::Decl, elab: &mut Vec<Decl<'a>>) {
        self.with_scope(|ctx| {
            ctx.elaborate_decl_inner(decls, elab);
            ctx.local_depth += 1;
            ctx.elaborate_decl_inner(body, elab);
            ctx.local_depth -= 1;
        })
    }

    fn elab_decl_seq(&mut self, decls: &[ast::Decl], elab: &mut Vec<Decl<'a>>) {
        for d in decls {
            self.elaborate_decl_inner(d, elab);
        }
    }

    fn elab_decl_type(&mut self, tbs: &[ast::Typebind], _elab: &mut Vec<Decl<'a>>) {
        for typebind in tbs {
            let scheme = if !typebind.tyvars.is_empty() {
                self.with_tyvars(|ctx| {
                    for s in typebind.tyvars.iter() {
                        let v = ctx.arena.types.fresh_type_var(ctx.tyvar_rank);
                        ctx.tyvars.push((*s, v));
                    }
                    let ty = ctx.elaborate_type(&typebind.ty, false);
                    let s = match typebind.tyvars.len() {
                        0 => Scheme::Mono(ty),
                        _ => Scheme::Poly(
                            typebind
                                .tyvars
                                .iter()
                                .map(|tv| ctx.lookup_tyvar(tv, false).unwrap().id)
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

    fn elab_decl_conbind(&mut self, db: &ast::Datatype, elab: &mut Vec<Decl<'a>>) {
        let tycon = Tycon::new(db.tycon, db.tyvars.len(), self.scope_depth());

        // This is safe to unwrap, because we already bound it.
        let type_id = self.lookup_type_id(&db.tycon).unwrap();

        // Should be safe to unwrap here as well, since the caller has bound db.tyvars
        let tyvars: Vec<&'a TypeVar<'a>> = db
            .tyvars
            .iter()
            .map(|sym| self.lookup_tyvar(sym, false).unwrap())
            .collect();

        let mut constructors = Vec::new();
        for (tag, con) in db.constructors.iter().enumerate() {
            if self.lookup_value(&con.label).is_some() {
                self.elab_errors.push(
                    ElabError::new(con.span, "data constructor")
                        .kind(ErrorKind::Rebound(con.label)),
                );
                // return;
            }

            let cons = Constructor {
                name: con.label,
                type_id,
                tag: tag as u8,
                arity: con.data.is_some() as u8,
                type_arity: db.constructors.len() as u8,
            };

            let res = self.arena.types.alloc(Type::Con(
                tycon,
                tyvars
                    .iter()
                    .map(|v| &*self.arena.types.alloc(Type::Var(v)))
                    .collect(),
            ));

            let ty = match &con.data {
                Some(ty) => {
                    let dom = self.elaborate_type(ty, false);
                    constructors.push((cons, Some(dom)));
                    self.arena.types.arrow(dom, res)
                }
                None => {
                    constructors.push((cons, None));
                    res
                }
            };

            // calling `generalize` here will actually introduce some bugs, since
            // any type vars could've already been placed in the VE, thereby
            // preventing later constructors containing the same tyvars from
            // being properly generalized
            let s = match tyvars.len() {
                0 => Scheme::Mono(ty),
                _ => Scheme::Poly(tyvars.iter().map(|tv| tv.id).collect(), ty),
            };
            self.define_value(con.label, con.span, s, IdStatus::Con(cons));
        }
        let dt = Datatype {
            tycon,
            tyvars: tyvars.iter().map(|tv| tv.id).collect(),
            constructors,
        };
        elab.push(Decl::Datatype(dt));
    }

    fn elab_decl_datatype(&mut self, dbs: &[ast::Datatype], elab: &mut Vec<Decl<'a>>) {
        // Add all of the type constructors to the environment first, so that
        // we can construct data constructor arguments (e.g. recursive/mutually
        // recursive datatypes)
        for db in dbs {
            let tycon = Tycon::new(db.tycon, db.tyvars.len(), self.scope_depth());
            self.define_type(db.tycon, TypeStructure::Tycon(tycon));
        }
        for db in dbs {
            self.with_tyvars(|ctx| {
                for s in &db.tyvars {
                    let v = ctx.arena.types.fresh_type_var(ctx.tyvar_rank);
                    ctx.tyvars.push((*s, v));
                }
                ctx.elab_decl_conbind(db, elab)
            });
        }
    }

    fn elab_decl_exception(&mut self, exns: &[ast::Variant], elab: &mut Vec<Decl<'a>>) {
        for exn in exns {
            let con = Constructor {
                name: exn.label,
                type_id: TypeId(8),
                tag: 0,
                arity: exn.data.is_some() as u8,
                type_arity: exns.len() as u8,
            };

            match &exn.data {
                Some(ty) => {
                    let ty = self.elaborate_type(ty, false);
                    elab.push(Decl::Exn(con, Some(ty)));
                    self.define_value(
                        exn.label,
                        exn.span,
                        Scheme::Mono(self.arena.types.arrow(ty, self.arena.types.exn())),
                        IdStatus::Exn(con),
                    );
                }
                None => {
                    elab.push(Decl::Exn(con, None));
                    self.define_value(
                        exn.label,
                        exn.span,
                        Scheme::Mono(self.arena.types.exn()),
                        IdStatus::Exn(con),
                    );
                }
            }
        }
    }

    /// Perform initial elaboration on a function binding, enough to build up an
    /// environment
    fn elab_decl_fnbind_ty<'s>(
        &mut self,
        name: Symbol,
        arity: usize,
        fbs: &'s [ast::FnBinding],
    ) -> PartialFun<'s, 'a> {
        let arg_tys = (0..arity)
            .map(|_| self.fresh_tyvar())
            .collect::<Vec<&'a Type<'a>>>();
        let res_ty = self.fresh_tyvar();
        let mut clauses = Vec::new();
        for clause in fbs {
            if let Some(ty) = &clause.res_ty {
                let t = self.elaborate_type(&ty, false);
                self.unify(res_ty, t, &|c| {
                    c.span(ty.span)
                        .message("function clause with result constraint of different type")
                });
            }

            let mut pats = Vec::new();
            let mut bindings = Vec::new();

            for (idx, pat) in clause.pats.iter().enumerate() {
                let pat = self.elaborate_pat_inner(pat, false, &mut bindings);
                self.unify(arg_tys[idx], pat.ty, &|c| {
                    c.span(pat.span)
                        .message("function clause with argument of different type")
                });
                pats.push(pat);
            }
            if pats.len() < arity {
                for idx in pats.len()..arity {
                    let wild = Pat::new(self.arena.pats.wild(), self.fresh_tyvar(), clause.span);
                    self.unify(arg_tys[idx], wild.ty, &|c| {
                        c.span(wild.span)
                            .message("function clause with argument of different type")
                    });
                    pats.push(wild);
                }
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
            .fold(res_ty, |acc, arg| self.arena.types.arrow(arg, acc));

        PartialFun {
            name,
            clauses,
            arity,
            arg_tys,
            res_ty,
            ty,
        }
    }

    fn elab_decl_fnbind(&mut self, fun: PartialFun<'_, 'a>) -> Lambda<'a> {
        let PartialFun {
            clauses,
            res_ty,
            arg_tys,
            ..
        } = fun;

        let mut dontgeneralize = false;
        let mut patterns = Vec::new();
        let mut rules = Vec::new();
        let mut total_sp = clauses[0].span;
        // Destructure so that we can move `bindings` into a closure
        for PartialFnBinding {
            pats,
            expr,
            bindings,
            span,
        } in clauses
        {
            // Make a new scope, in which we define the pattern bindings, and proceed
            // to elaborate the body of the function clause
            self.tyvar_rank += 1;
            let expr = self.with_scope(move |ctx| {
                for (var, tv) in bindings {
                    ctx.define_value(var, span, Scheme::Mono(tv), IdStatus::Var);
                }
                ctx.elaborate_expr(&expr)
            });
            self.tyvar_rank -= 1;
            // Unify function clause body with result type
            self.unify(res_ty, expr.ty, &|c| {
                c.span(span)
                    .message("function clause body doesn't match with return type")
            });

            let tuple_ty = self.arena.types.tuple(pats.iter().map(|pat| pat.ty));
            let tuple_pat = Pat::new(self.arena.pats.tuple(pats.iter().copied()), tuple_ty, span);
            let rule = Rule {
                pat: tuple_pat,
                expr,
            };

            if pats.iter().any(|p| p.flexible()) {
                dontgeneralize = true;
            }

            total_sp += span;
            patterns.push(pats);
            rules.push(rule);
        }

        // Now generate fresh argument names for our function, so we can curry
        let mut fresh_args = arg_tys
            .iter()
            // .rev()
            .map(|ty| (self.fresh_var(), *ty))
            .collect::<Vec<(Symbol, _)>>();

        let case =
            crate::match_compile::fun(self, res_ty, fresh_args.clone(), patterns, rules, total_sp);

        // Fold over the arguments and types, creating nested lambda functions
        let (a, t) = fresh_args.remove(0);
        let (body, ty) =
            fresh_args
                .into_iter()
                .rev()
                .fold((case, res_ty), |(expr, rty), (arg, ty)| {
                    (
                        Expr::new(
                            self.arena.exprs.alloc(ExprKind::Lambda(Lambda {
                                arg,
                                ty,
                                body: expr,
                            })),
                            self.arena.types.arrow(ty, rty),
                            Span::dummy(),
                        ),
                        self.arena.types.arrow(ty, rty),
                    )
                });

        // Rebind with final type. Unbind first so that generalization happens properly
        self.unbind_value(fun.name);
        let ty = self.arena.types.arrow(t, ty);
        let sch = match dontgeneralize {
            true => Scheme::Mono(ty),
            false => self.generalize(ty),
        };

        self.define_value(fun.name, total_sp, sch, IdStatus::Var);

        Lambda {
            arg: a,
            ty: t,
            body,
        }
    }

    fn elab_decl_fun(&mut self, tyvars: &[Symbol], fbs: &[ast::Fun], elab: &mut Vec<Decl<'a>>) {
        self.with_tyvars(|ctx| {
            let mut vars = Vec::new();
            ctx.tyvar_rank += 1;
            for sym in tyvars {
                let f = ctx.arena.types.fresh_type_var(ctx.tyvar_rank + 1);
                vars.push(f.id);
                ctx.tyvars.push((*sym, f));
            }

            let mut info = Vec::new();
            // Check to make sure all of the function clauses are consistent within each
            // binding group
            for f in fbs {
                let name = f[0].name;
                let arity = f.iter().map(|fb| fb.pats.len()).max().unwrap_or(1);
                let fns = ctx.elab_decl_fnbind_ty(name, arity, f);

                ctx.define_value(fns.name, f.span, Scheme::Mono(fns.ty), IdStatus::Var);
                info.push(fns);
            }
            ctx.tyvar_rank -= 1;

            elab.push(Decl::Fun(
                vars,
                info.into_iter()
                    .map(|fun| (fun.name, ctx.elab_decl_fnbind(fun)))
                    .collect::<Vec<(Symbol, Lambda)>>(),
            ));
        })
    }

    fn elab_decl_val(
        &mut self,
        tyvars: &[Symbol],
        pat: &ast::Pat,
        expr: &ast::Expr,
        elab: &mut Vec<Decl<'a>>,
    ) {
        self.with_tyvars(|ctx| {
            ctx.tyvar_rank += 1;
            for tyvar in tyvars {
                ctx.tyvars
                    .push((*tyvar, ctx.arena.types.fresh_type_var(ctx.tyvar_rank)));
            }

            let expr = ctx.elaborate_expr(expr);

            let (pat, bindings) = ctx.elaborate_pat(pat, false);
            ctx.tyvar_rank -= 1;

            ctx.unify(pat.ty, expr.ty, &|c| {
                c.span(expr.span)
                    .message("pattern and expression have different types in `val` declaration")
            });

            let dontgeneralize = !expr.non_expansive() || pat.flexible();
            for (var, tv) in bindings {
                let sch = match dontgeneralize {
                    false => ctx.generalize(tv),
                    true => {
                        // ctx.elab_errors.push(ElabError::new(pat.span, "type variables not generalized!").kind(ErrorKind::Generalize));
                        Scheme::Mono(tv)
                    }
                };
                ctx.define_value(var, pat.span, sch, IdStatus::Var);
            }

            elab.push(Decl::Val(Rule { pat, expr }));
        })
    }

    fn elaborate_decl_inner(&mut self, decl: &ast::Decl, elab: &mut Vec<Decl<'a>>) {
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

    pub fn elaborate_decl(&mut self, decl: &ast::Decl) -> Vec<Decl<'a>> {
        let mut elab = Vec::new();
        self.elaborate_decl_inner(decl, &mut elab);
        elab
    }
}

impl<'a> Query<ast::Pat> for &Context<'a> {
    fn fixity(&self, t: &ast::Pat) -> Fixity {
        match &t.data {
            ast::PatKind::Variable(s) => self.lookup_infix(s).unwrap_or(Fixity::Nonfix),
            _ => Fixity::Nonfix,
        }
    }

    fn infix(&self, a: ast::Pat, b: ast::Pat, c: ast::Pat) -> Result<ast::Pat, precedence::Error> {
        // We know `a` must be a symbol, since it has a Fixity!
        match a.data {
            ast::PatKind::Variable(s) => {
                let sp_bc = b.span + c.span;
                let sp = a.span + sp_bc;
                let rec = ast::Pat::new(ast::make_record_pat(vec![b, c], false), sp_bc);
                Ok(ast::Pat::new(ast::PatKind::App(s, Box::new(rec)), sp))
            }
            _ => Err(precedence::Error::InvalidOperator),
        }
    }

    fn apply(&self, a: ast::Pat, b: ast::Pat) -> Result<ast::Pat, precedence::Error> {
        match a.data {
            ast::PatKind::Variable(s) => {
                let sp = a.span + b.span;
                Ok(ast::Pat::new(ast::PatKind::App(s, Box::new(b)), sp))
            }
            _ => Err(precedence::Error::InvalidOperator),
        }
    }
}

impl<'a> Query<ast::Expr> for &Context<'a> {
    fn fixity(&self, t: &ast::Expr) -> Fixity {
        match &t.data {
            ast::ExprKind::Var(s) => self.lookup_infix(s).unwrap_or(Fixity::Nonfix),
            _ => Fixity::Nonfix,
        }
    }

    fn infix(
        &self,
        a: ast::Expr,
        b: ast::Expr,
        c: ast::Expr,
    ) -> Result<ast::Expr, precedence::Error> {
        let sp_bc = b.span + c.span;
        let sp = a.span + sp_bc;
        let rec = ast::Expr::new(ast::make_record(vec![b, c]), sp_bc);
        Ok(ast::Expr::new(
            ast::ExprKind::App(Box::new(a), Box::new(rec)),
            sp,
        ))
    }
    fn apply(&self, a: ast::Expr, b: ast::Expr) -> Result<ast::Expr, precedence::Error> {
        let sp = a.span + b.span;
        Ok(ast::Expr::new(
            ast::ExprKind::App(Box::new(a), Box::new(b)),
            sp,
        ))
    }
}

impl<'a> Context<'a> {
    pub(crate) fn expr_precedence(
        &self,
        exprs: Vec<ast::Expr>,
    ) -> Result<ast::Expr, precedence::Error> {
        Precedence::run(self, exprs)
    }

    pub(crate) fn pat_precedence(
        &self,
        exprs: Vec<ast::Pat>,
    ) -> Result<ast::Pat, precedence::Error> {
        Precedence::run(self, exprs)
    }
}
