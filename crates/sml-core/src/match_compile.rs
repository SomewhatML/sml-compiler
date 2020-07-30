use super::*;
use elaborate::Context;
use std::collections::{HashMap, HashSet};

// #[derive(Debug)]
pub struct Matrix<'a, 'ctx> {
    // ref to the context so we can allocate stuff in arenas
    ctx: &'ctx Context<'a>,
    // return type
    ret_ty: &'a Type<'a>,

    pub pats: Vec<Vec<Pat<'a>>>,
    pub exprs: Vec<Expr<'a>>,

    // These are *only* ExprKind::Var
    vars: Vec<Expr<'a>>,
}

impl<'a> Pat<'a> {
    fn wild(&self) -> bool {
        match self.pat {
            PatKind::Wild | PatKind::Var(_) => true,
            _ => false,
        }
    }
}

impl<'a, 'ctx> Matrix<'a, 'ctx> {
    /// Create a shallow clone with empty `pats` and `vars`
    /// For internal use only
    fn shallow(&self) -> Matrix<'a, 'ctx> {
        Matrix {
            ctx: self.ctx,
            ret_ty: self.ret_ty,
            vars: self.vars.clone(),

            pats: Vec::with_capacity(self.pats.len()),
            exprs: Vec::with_capacity(self.exprs.len()),
        }
    }

    /// Build a new pattern matrix.
    ///
    /// # Invariants:
    ///
    /// * Type safety - the case expression that is being transformed
    ///     should have been previously verified to be well typed
    /// * Eta conversion - expressions in the case arms should converted
    ///     into abstractions that take bound vars as arguments
    /// * `arg` should be a fresh variable of the same type of the
    ///     match rules
    pub fn new(
        ctx: &'ctx Context<'a>,
        ret_ty: &'a Type<'a>,
        vars: Vec<Expr<'a>>,
        rules: &[Rule<'a>],
    ) -> Matrix<'a, 'ctx> {
        let mut mat = Matrix::build(ctx, ret_ty, vars, rules.len());
        for rule in rules {
            mat.pats.push(vec![rule.pat]);
            mat.exprs.push(rule.expr);
        }
        mat
    }

    /// We have this separate for elaborating function bindings
    pub fn build(
        ctx: &'ctx Context<'a>,
        ret_ty: &'a Type<'a>,
        vars: Vec<Expr<'a>>,
        cap: usize,
    ) -> Matrix<'a, 'ctx> {
        Matrix {
            ctx,
            ret_ty,
            vars,
            pats: Vec::with_capacity(cap),
            exprs: Vec::with_capacity(cap),
        }
    }

    fn mk_wild(&self, ty: &'a Type<'a>) -> Pat<'a> {
        Pat::new(self.ctx.arena.pats.wild(), ty, Span::dummy())
    }

    fn mk_pvar(&self, name: Symbol, ty: &'a Type<'a>) -> Pat<'a> {
        Pat::new(
            self.ctx.arena.pats.alloc(PatKind::Var(name)),
            ty,
            Span::dummy(),
        )
    }

    fn mk_evar(&self, name: Symbol, ty: &'a Type<'a>) -> Expr<'a> {
        Expr::new(
            self.ctx.arena.exprs.alloc(ExprKind::Var(name)),
            ty,
            Span::dummy(),
        )
    }

    fn mk_let(&self, pat: Pat<'a>, expr: Expr<'a>, body: Expr<'a>) -> Expr<'a> {
        Expr::new(
            self.ctx
                .arena
                .exprs
                .alloc(ExprKind::Let(vec![Decl::Val(Rule { pat, expr })], body)),
            self.ret_ty,
            body.span,
        )
    }

    /// Deconstruct a record or tuple pattern, binding each field to a fresh
    /// variable, and flattening all of the record patterns in the first column
    /// [{a, b, c}, ...] --> [a, b, c, ...]
    fn record_rule(&self, fields: &SortedRecord<Pat<'a>>) -> Expr<'a> {
        // This part is a little tricky. We need to generate a fresh variable
        // for every field in the pattern
        let mut vars = self.vars.clone();
        let base = vars.remove(0);

        // Lots of work to just create a new pattern to bind
        let mut record = Vec::new();
        let mut tys = Vec::new();
        let mut span = fields[0].span;
        for row in fields.iter() {
            let fresh = self.ctx.fresh_var();
            let bind = self.mk_pvar(fresh, row.data.ty);
            let expr = self.mk_evar(fresh, row.data.ty);

            record.push(row.fmap(|_| bind));
            tys.push(row.fmap(|p| p.ty));
            vars.push(expr);
            span.end = row.span.end;
        }

        // fields are already ordered, `new_unchecked` is OK
        let pat_ty = self
            .ctx
            .arena
            .types
            .alloc(Type::Record(SortedRecord::new_unchecked(tys)));
        let pat = Pat::new(
            self.ctx
                .arena
                .pats
                .alloc(PatKind::Record(SortedRecord::new_unchecked(record))),
            pat_ty,
            span,
        );

        let mut mat = self.shallow();
        for (idx, row) in self.pats.iter().enumerate() {
            let mut new_row: Vec<Pat> = row.iter().skip(1).cloned().collect();

            match &row[0].pat {
                PatKind::Record(bound) => {
                    for (idx, row) in bound.iter().enumerate() {
                        new_row.insert(idx, row.data);
                    }
                }
                PatKind::Var(_) | PatKind::Wild => {
                    for (idx, row) in fields.iter().enumerate() {
                        new_row.insert(idx, self.mk_wild(row.data.ty));
                    }
                }
                _ => continue,
            }
            mat.exprs.push(self.exprs[idx].clone());
            mat.pats.push(new_row);
        }
        mat.vars = vars;
        // We now have `let val ($x0, $x1... fresh vars) = x in case [$x0, $x1...]
        self.mk_let(pat, base, mat.compile())
    }

    /// This is basically the same thing as the record rule, but for data
    /// constructors. We want to select all of the rows in the first column
    /// that will match the constructor `head` (e.g. `head` itself, and wildcard)
    fn specialize(&self, head: &Constructor, arity: Option<(Symbol, &'a Type<'a>)>) -> Expr<'a> {
        let mut mat = self.shallow();
        for (idx, row) in self.pats.iter().enumerate() {
            let mut new_row: Vec<Pat> = row.iter().skip(1).copied().collect();
            match &row[0].pat {
                PatKind::App(con, Some(arg)) if con == head => {
                    new_row.insert(0, *arg);
                }
                PatKind::App(con, None) if con == head => {}
                PatKind::Wild | PatKind::Var(_) => {
                    if let Some((name, ty)) = arity {
                        new_row.insert(0, self.mk_pvar(name, ty));
                    }
                }
                _ => continue,
            }
            mat.exprs.push(self.exprs[idx]);
            mat.pats.push(new_row);
        }

        match arity {
            Some((name, ty)) => {
                // is this correct?
                let _ = std::mem::replace(&mut mat.vars[0], self.mk_evar(name, ty));
            }
            None => {
                mat.vars.remove(0);
            }
        }

        mat.compile()
    }

    /// Generate a case expression for the data constructors in the first column
    fn sum_rule(&self) -> Expr<'a> {
        // Generate the set of constructors appearing in the column
        let mut set = HashMap::new();
        let mut type_arity = 0;
        for row in &self.pats {
            if let PatKind::App(con, p) = &row[0].pat {
                set.insert(con, p.map(|p| p.ty));
                type_arity = con.type_arity;
            }
        }

        // We only use `true` and `false` or `cons` and `nil`, so we know
        // there are only 2 constructors in each datatype. Otherwise we
        // would need to query a context to determine this
        let exhaustive = set.len() == type_arity as usize;

        let mut rules = Vec::new();
        for (con, arg_ty) in set {
            // In a real system, we would have some context to pull the number
            // of data constructors for a datatype, and the arity of each
            // data constructor. We just mock it instead
            let fresh = self.ctx.fresh_var();
            let expr = self.specialize(con, arg_ty.map(|ty| (fresh, ty)));

            let arg = match arg_ty {
                Some(ty) => Some(self.mk_pvar(fresh, ty)),
                None => None,
            };
            let pat = Pat::new(
                self.ctx.arena.pats.alloc(PatKind::App(*con, arg)),
                self.pats[0][0].ty,
                Span::dummy(),
            );
            rules.push(Rule { pat, expr });
        }

        // If we don't have an exhaustive match, generate a default matrix
        if !exhaustive {
            let pat = self.mk_wild(self.pats[0][0].ty);
            let expr = self.default_matrix();
            rules.push(Rule { pat, expr });
        }
        Expr::new(
            self.ctx
                .arena
                .exprs
                .alloc(ExprKind::Case(self.vars[0], rules)),
            self.ret_ty,
            Span::dummy(),
        )
    }

    /// Generate a case expression for the constants in the first column
    fn const_rule(&self) -> Expr<'a> {
        // Generate the set of constants appearing in the column
        let mut set = HashSet::new();
        let mut rules = Vec::new();
        for (row, expr) in self.pats.iter().zip(&self.exprs) {
            if let PatKind::Const(con) = &row[0].pat {
                if set.insert(con) {
                    rules.push(Rule {
                        pat: row[0],
                        expr: *expr,
                    });
                }
            }
        }

        // Constants are _always_ non-exhaustive
        let pat = self.mk_wild(self.pats[0][0].ty);
        let expr = self.default_matrix();
        rules.push(Rule { pat, expr });

        Expr::new(
            self.ctx
                .arena
                .exprs
                .alloc(ExprKind::Case(self.vars[0], rules)),
            self.ret_ty,
            Span::dummy(),
        )
    }

    /// Compute the "default" matrix
    fn default_matrix(&self) -> Expr<'a> {
        let mut mat = self.shallow();
        mat.vars.remove(0);

        for (idx, row) in self.pats.iter().enumerate() {
            if let Some(true) = row.first().map(Pat::wild) {
                mat.pats.push(row.iter().skip(1).cloned().collect());
                mat.exprs.push(self.exprs[idx].clone());
            }
        }
        mat.compile()
    }

    /// Compile a [`Matrix`] into a source-level expression
    pub fn compile(&mut self) -> Expr<'a> {
        dbg!(&self);
        if self.pats.is_empty() {
            // We have an in-exhaustive case expression
            let matchh = Expr::new(
                self.ctx
                    .arena
                    .exprs
                    .alloc(ExprKind::Con(crate::builtin::constructors::C_MATCH, vec![])),
                self.ret_ty,
                Span::zero(),
            );
            Expr::new(
                self.ctx.arena.exprs.alloc(ExprKind::Raise(matchh)),
                self.ret_ty,
                Span::zero(),
            )
        } else if self.pats[0].iter().all(Pat::wild) {
            // Every pattern in the first row is a variable or wildcard,
            // so the it matches. return the body of the match rule
            self.exprs[0].clone()
        } else {
            // There is at least one non-wild pattern in the matrix somewhere
            for row in &self.pats {
                match &row[0].pat {
                    PatKind::Record(fields) => return self.record_rule(fields),
                    PatKind::App(_, _) => return self.sum_rule(),
                    PatKind::List(_) => todo!(),
                    PatKind::Const(_) => return self.const_rule(),
                    PatKind::Wild | PatKind::Var(_) => continue,
                    // _ => continue,
                }
            }

            // The first column contains only wildcard patterns. Search the
            // matrix until we find a column that has a non-wildcard pattern,
            // and swap columns with column 0
            let sz = self.pats[0].len();
            let mut col = 1;
            'outer: while col < sz {
                for row in &self.pats {
                    match row.get(col) {
                        Some(x) if x.wild() => continue,
                        _ => break 'outer,
                    }
                }
                col += 1;
            }

            if col < sz {
                for row in self.pats.iter_mut() {
                    row.swap(0, col);
                }
                self.compile()
            } else {
                self.default_matrix()
            }
        }
    }
}

impl fmt::Debug for Matrix<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "matrix {:?}\n", self.vars)?;
        for (pats, exprs) in self.pats.iter().zip(self.exprs.iter()) {
            writeln!(
                f,
                "{:?} => {:?}",
                pats.iter()
                    .map(|pat| format!("{:?}", pat))
                    .collect::<Vec<String>>()
                    .join(","),
                exprs
            )?;
        }
        // write!(f, "")
        Ok(())
    }
}
