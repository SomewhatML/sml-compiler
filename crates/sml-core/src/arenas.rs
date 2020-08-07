use super::*;
// use sml_util::arena::Arena;
use std::cell::Cell;
use typed_arena::Arena;

#[derive(Default)]
pub struct OwnedCoreArena<'arena> {
    types: Arena<Type<'arena>>,
    vars: Arena<TypeVar<'arena>>,
    exprs: Arena<ExprKind<'arena>>,
    pats: Arena<PatKind<'arena>>,
}

impl<'arena> OwnedCoreArena<'arena> {
    pub fn new() -> OwnedCoreArena<'arena> {
        OwnedCoreArena {
            types: Arena::with_capacity(4096),
            vars: Arena::with_capacity(4096),
            exprs: Arena::with_capacity(4096),
            pats: Arena::with_capacity(4096),
        }
    }
    pub fn borrow(&'arena self) -> CoreArena<'arena> {
        CoreArena {
            types: TypeArena::new(&self.types, &self.vars),
            exprs: ExprArena::new(&self.exprs),
            pats: PatArena::new(&self.pats),
        }
    }
}

pub struct CoreArena<'ar> {
    pub types: TypeArena<'ar>,
    pub exprs: ExprArena<'ar>,
    pub pats: PatArena<'ar>,
}

impl<'a> CoreArena<'a> {
    /// Create a new pattern tuple from an iterator of (PatKind, Type).
    /// The new tuple will have dummy spans everywhere
    pub fn pat_tuple<I: IntoIterator<Item = (PatKind<'a>, &'a Type<'a>)>>(
        &self,
        iter: I,
    ) -> Pat<'a> {
        let (fields, tys) = iter
            .into_iter()
            .enumerate()
            .map(|(idx, (sym, ty))| {
                (
                    Row {
                        label: Symbol::tuple_field(idx as u32 + 1),
                        data: Pat::new(self.pats.alloc(sym), ty, Span::dummy()),
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
        Pat::new(
            self.pats
                .alloc(PatKind::Record(SortedRecord::new_unchecked(fields))),
            self.types
                .alloc(Type::Record(SortedRecord::new_unchecked(tys))),
            Span::dummy(),
        )
    }

    /// Create a new pattern struct from an iterator of (PatKind, Type).
    /// The new tuple will have dummy spans everywhere
    pub fn pat_record<I: IntoIterator<Item = (Symbol, PatKind<'a>, &'a Type<'a>)>>(
        &self,
        iter: I,
    ) -> Pat<'a> {
        let (fields, tys) = iter
            .into_iter()
            .map(|(sym, data, ty)| {
                (
                    Row {
                        label: sym,
                        data: Pat::new(self.pats.alloc(data), ty, Span::dummy()),
                        span: Span::dummy(),
                    },
                    Row {
                        label: sym,
                        data: ty,
                        span: Span::dummy(),
                    },
                )
            })
            .unzip();
        Pat::new(
            self.pats.alloc(PatKind::Record(SortedRecord::new(fields))),
            self.types.alloc(Type::Record(SortedRecord::new(tys))),
            Span::dummy(),
        )
    }

    /// Create a new expression tuple from an iterator of (PatKind, Type).
    /// The new tuple will have dummy spans everywhere
    pub fn expr_tuple<I: IntoIterator<Item = (ExprKind<'a>, &'a Type<'a>)>>(
        &self,
        iter: I,
    ) -> Expr<'a> {
        let (fields, tys) = iter
            .into_iter()
            .enumerate()
            .map(|(idx, (sym, ty))| {
                (
                    Row {
                        label: Symbol::tuple_field(idx as u32 + 1),
                        data: Expr::new(self.exprs.alloc(sym), ty, Span::dummy()),
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
        Expr::new(
            self.exprs.alloc(ExprKind::Record(fields)),
            self.types
                .alloc(Type::Record(SortedRecord::new_unchecked(tys))),
            Span::dummy(),
        )
    }

    /// Create a new expression record from an iterator of (PatKind, Type).
    /// The new tuple will have dummy spans everywhere
    pub fn expr_record<I: IntoIterator<Item = (Symbol, ExprKind<'a>, &'a Type<'a>)>>(
        &self,
        iter: I,
    ) -> Expr<'a> {
        let (fields, tys) = iter
            .into_iter()
            .map(|(sym, data, ty)| {
                (
                    Row {
                        label: sym,
                        data: Expr::new(self.exprs.alloc(data), ty, Span::dummy()),
                        span: Span::dummy(),
                    },
                    Row {
                        label: sym,
                        data: ty,
                        span: Span::dummy(),
                    },
                )
            })
            .unzip();
        Expr::new(
            self.exprs.alloc(ExprKind::Record(fields)),
            self.types.alloc(Type::Record(SortedRecord::new(tys))),
            Span::dummy(),
        )
    }

    pub fn ty_tuple<I: IntoIterator<Item = &'a Type<'a>>>(&self, iter: I) -> &'a Type<'a> {
        let tys = iter
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| Row {
                label: Symbol::tuple_field(idx as u32 + 1),
                data: ty,
                span: Span::dummy(),
            })
            .collect();
        self.types
            .alloc(Type::Record(SortedRecord::new_unchecked(tys)))
    }

    pub fn pat_var(&self, var: Symbol, ty: &'a Type<'a>) -> Pat<'a> {
        Pat::new(self.pats.alloc(PatKind::Var(var)), ty, Span::dummy())
    }

    pub fn expr_var(&self, var: Symbol, ty: &'a Type<'a>, tyvec: Vec<&'a Type<'a>>) -> Expr<'a> {
        Expr::new(
            self.exprs.alloc(ExprKind::Var(var, tyvec)),
            ty,
            Span::dummy(),
        )
    }

    /// Create a `let val var_name : (ty1, ty2, ty3) = (s1, ... sN) in expr`
    /// expression
    // pub fn let_tuple<I: IntoIterator<Item = (Symbol, &'a Type<'a>)>>(
    //     &self,
    //     iter: I,
    //     var_name: Symbol,
    //     body: Expr<'a>,
    //     tyvar_rank: usize,
    // ) -> Expr<'a> {
    //     let expr = self.expr_tuple(iter.into_iter().map(|(sym, ty)| (ExprKind::Var(sym, Vec::new()), ty)));
    //     let tyvars = expr.ty.ftv_rank(tyvar_rank);
    //     let decl = Decl::Val(
    //         tyvars,
    //         Rule {
    //             pat: self.pat_var(var_name, expr.ty),
    //             expr,
    //         },
    //     );
    //     Expr::new(
    //         self.exprs.alloc(ExprKind::Let(vec![decl], body)),
    //         body.ty,
    //         body.span,
    //     )
    // }

    /// Create a `let val (s1, ..., sN) = var_name : (ty1, ty2, ty3) in expr`
    /// expression
    pub fn let_detuple<I: IntoIterator<Item = (Symbol, &'a Type<'a>)>>(
        &self,
        iter: I,
        var_name: Symbol,
        body: Expr<'a>,
        tyvar_rank: usize,
    ) -> Expr<'a> {
        let pat = self.pat_tuple(iter.into_iter().map(|(sym, ty)| (PatKind::Var(sym), ty)));
        let tyvars = pat.ty.ftv_rank(tyvar_rank);
        let decl = Decl::Val(
            tyvars,
            Rule {
                pat,
                expr: self.expr_var(var_name, pat.ty, Vec::new()),
            },
        );
        Expr::new(
            self.exprs.alloc(ExprKind::Let(vec![decl], body)),
            body.ty,
            body.span,
        )
    }

    /// Create a `let val {s11 : s21, ..., } = var_name : (ty1, ty2, ty3) in
    /// expr` expression
    pub fn let_derecord<I: IntoIterator<Item = (Symbol, Symbol, &'a Type<'a>)>>(
        &self,
        iter: I,
        var_name: Symbol,
        body: Expr<'a>,
        tyvar_rank: usize,
    ) -> Expr<'a> {
        let pat = self.pat_record(
            iter.into_iter()
                .map(|(field, sym, ty)| (field, PatKind::Var(sym), ty)),
        );

        let tyvars = pat.ty.ftv_rank(tyvar_rank);
        let decl = Decl::Val(
            tyvars,
            Rule {
                pat,
                expr: self.expr_var(var_name, pat.ty, Vec::new()),
            },
        );
        Expr::new(
            self.exprs.alloc(ExprKind::Let(vec![decl], body)),
            body.ty,
            body.span,
        )
    }
}

pub struct ExprArena<'ar> {
    arena: &'ar Arena<ExprKind<'ar>>,
    fresh: Cell<u32>,
}

impl<'ar> ExprArena<'ar> {
    pub fn new(arena: &'ar Arena<ExprKind<'ar>>) -> ExprArena<'ar> {
        ExprArena {
            arena,
            fresh: Cell::new(0),
        }
    }

    pub fn alloc(&self, pk: ExprKind<'ar>) -> &'ar ExprKind<'ar> {
        self.arena.alloc(pk)
    }

    pub fn fresh_var(&self) -> &'ar ExprKind<'ar> {
        self.arena
            .alloc(ExprKind::Var(self.allocate_id(), Vec::new()))
    }

    pub fn allocate_id(&self) -> Symbol {
        let x = self.fresh.get();
        self.fresh.set(x + 1);
        Symbol::Gensym(x)
    }

    pub fn tuple<I: IntoIterator<Item = Expr<'ar>>>(&self, iter: I) -> &'ar ExprKind<'ar> {
        let rows = iter
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| Row {
                label: Symbol::tuple_field(idx as u32 + 1),
                data: ty,
                span: Span::dummy(),
            })
            .collect();

        self.alloc(ExprKind::Record(rows))
    }
}

pub struct PatArena<'ar> {
    arena: &'ar Arena<PatKind<'ar>>,
    _wild: &'ar PatKind<'ar>,
}

impl<'ar> PatArena<'ar> {
    pub fn new(arena: &'ar Arena<PatKind<'ar>>) -> PatArena<'ar> {
        PatArena {
            arena,
            _wild: arena.alloc(PatKind::Wild),
        }
    }

    pub fn alloc(&self, pk: PatKind<'ar>) -> &'ar PatKind<'ar> {
        self.arena.alloc(pk)
    }

    pub fn wild(&self) -> &'ar PatKind<'ar> {
        self._wild
    }

    pub fn tuple<I: IntoIterator<Item = Pat<'ar>>>(&self, iter: I) -> &'ar PatKind<'ar> {
        let rows = iter
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| Row {
                label: Symbol::tuple_field(idx as u32 + 1),
                data: ty,
                span: Span::dummy(),
            })
            .collect();

        self.alloc(PatKind::Record(SortedRecord::new_unchecked(rows)))
    }
}

pub struct TypeArena<'ar> {
    types: &'ar Arena<Type<'ar>>,
    vars: &'ar Arena<TypeVar<'ar>>,
    fresh: Cell<usize>,

    // We cache the builtin nullary type constructors
    _exn: &'ar Type<'ar>,
    _bool: &'ar Type<'ar>,
    _int: &'ar Type<'ar>,
    _str: &'ar Type<'ar>,
    _char: &'ar Type<'ar>,
    _unit: &'ar Type<'ar>,
}

impl<'ar> TypeArena<'ar> {
    pub fn new(types: &'ar Arena<Type<'ar>>, vars: &'ar Arena<TypeVar<'ar>>) -> TypeArena<'ar> {
        let _exn = types.alloc(Type::Con(builtin::tycons::T_EXN, Vec::new()));
        let _bool = types.alloc(Type::Con(builtin::tycons::T_BOOL, Vec::new()));
        let _int = types.alloc(Type::Con(builtin::tycons::T_INT, Vec::new()));
        let _str = types.alloc(Type::Con(builtin::tycons::T_STRING, Vec::new()));
        let _char = types.alloc(Type::Con(builtin::tycons::T_CHAR, Vec::new()));
        let _unit = types.alloc(Type::Con(builtin::tycons::T_UNIT, Vec::new()));

        TypeArena {
            types,
            vars,
            fresh: Cell::new(0),
            _exn,
            _bool,
            _int,
            _str,
            _char,
            _unit,
        }
    }

    pub fn alloc(&self, ty: Type<'ar>) -> &'ar Type<'ar> {
        self.types.alloc(ty)
    }

    pub fn fresh_var(&self, rank: usize) -> &'ar Type<'ar> {
        let tvar = self.fresh_type_var(rank);
        self.types.alloc(Type::Var(tvar))
    }

    pub fn fresh_type_var(&self, rank: usize) -> &'ar TypeVar<'ar> {
        let x = self.fresh.get();
        self.fresh.set(x + 1);
        self.vars.alloc(TypeVar::new(x, rank))
    }

    pub fn alloc_tuple<I: IntoIterator<Item = Type<'ar>>>(&self, iter: I) -> &'ar Type<'ar> {
        let rows = iter
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| Row {
                label: Symbol::tuple_field(idx as u32 + 1),
                data: self.alloc(ty),
                span: Span::dummy(),
            })
            .collect();

        self.alloc(Type::Record(SortedRecord::new_unchecked(rows)))
    }

    pub fn tuple<I: IntoIterator<Item = &'ar Type<'ar>>>(&self, iter: I) -> &'ar Type<'ar> {
        let rows = iter
            .into_iter()
            .enumerate()
            .map(|(idx, ty)| Row {
                label: Symbol::tuple_field(idx as u32 + 1),
                data: ty,
                span: Span::dummy(),
            })
            .collect();

        self.alloc(Type::Record(SortedRecord::new_unchecked(rows)))
    }

    pub fn exn(&self) -> &'ar Type<'ar> {
        self._exn
    }

    pub fn unit(&self) -> &'ar Type<'ar> {
        self._unit
    }

    pub fn char(&self) -> &'ar Type<'ar> {
        self._char
    }

    pub fn int(&self) -> &'ar Type<'ar> {
        self._int
    }

    pub fn bool(&self) -> &'ar Type<'ar> {
        self._bool
    }

    pub fn string(&self) -> &'ar Type<'ar> {
        self._str
    }

    pub fn reff(&self, ty: &'ar Type<'ar>) -> &'ar Type<'ar> {
        self.types
            .alloc(Type::Con(builtin::tycons::T_REF, vec![ty]))
    }

    pub fn list(&self, ty: &'ar Type<'ar>) -> &'ar Type<'ar> {
        self.types
            .alloc(Type::Con(builtin::tycons::T_LIST, vec![ty]))
    }

    pub fn arrow(&self, dom: &'ar Type<'ar>, rng: &'ar Type<'ar>) -> &'ar Type<'ar> {
        self.types
            .alloc(Type::Con(builtin::tycons::T_ARROW, vec![dom, rng]))
    }
}
