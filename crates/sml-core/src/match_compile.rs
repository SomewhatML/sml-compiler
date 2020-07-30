use super::*;
use elaborate::Context;
use std::collections::HashMap;

// Internal representation of a variable-less pattern
pub enum Pattern {
    Wild,
    Record(SortedRecord<Pattern>),
}

#[derive(Default, Debug)]
pub struct Matrix<'a> {
    pats: Vec<Vec<Pat<'a>>>,
    exprs: Vec<Expr<'a>>,

    // These are only ExprKind::Var
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

impl<'a> Matrix<'a> {
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
    pub fn build(arg: Expr<'a>, rules: &[Rule<'a>]) -> Matrix<'a> {
        let mut mat = Matrix::default();
        mat.vars = vec![arg];
        for rule in rules {
            mat.pats.push(vec![rule.pat]);
            mat.exprs.push(rule.expr);
        }
        mat
    }

    fn mk_wild(&self, ctx: &mut Context<'a>, ty: &'a Type<'a>) -> Pat<'a> {
        Pat::new(ctx.arena.pats.wild(), ty, Span::dummy())
    }

    /// Deconstruct a record or tuple pattern, binding each field to a fresh
    /// variable, and flattening all of the record patterns in the first column
    /// [{a, b, c}, ...] --> [a, b, c, ...]
    fn record_rule(
        &self,
        ctx: &mut Context<'a>,
        ty: &'a Type<'a>,
        fields: &SortedRecord<Pat<'a>>,
    ) -> Expr<'a> {
        dbg!(&self);
        // This part is a little tricky. We need to generate a fresh variable
        // for every field in the pattern
        let mut vars = self.vars.clone();
        let base = vars.remove(0);

        // Lots of work to just create a new pattern to bind
        let mut record = Vec::new();
        let mut tys = Vec::new();
        let mut span = fields[0].span;
        for row in fields.iter() {
            let fresh = ctx.fresh_var();
            let bind = Pat::new(
                ctx.arena.pats.alloc(PatKind::Var(fresh)),
                row.data.ty,
                row.data.span,
            );
            record.push(row.fmap(|_| bind));
            tys.push(row.fmap(|p| p.ty));
            vars.push(Expr::new(
                ctx.arena.exprs.alloc(ExprKind::Var(fresh)),
                row.data.ty,
                row.data.span,
            ));
            span.end = row.span.end;
        }

        // fields are already ordered, `new_unchecked` is OK
        let pat_ty = ctx
            .arena
            .types
            .alloc(Type::Record(SortedRecord::new_unchecked(tys)));
        let pat = Pat::new(
            ctx.arena
                .pats
                .alloc(PatKind::Record(SortedRecord::new_unchecked(record))),
            pat_ty,
            span,
        );

        let mut mat = Matrix::default();
        for (idx, row) in self.pats.iter().enumerate() {
            let mut new_row: Vec<Pat> = row.iter().skip(1).cloned().collect();

            match &row[0].pat {
                PatKind::Record(fields) => {
                    for (idx, row) in fields.iter().enumerate() {
                        new_row.insert(idx, row.data);
                    }
                }
                PatKind::Var(_) | PatKind::Wild => {
                    for idx in 0..fields.len() {
                        new_row.insert(idx, self.mk_wild(ctx, row[0].ty));
                    }
                }
                _ => continue,
            }
            mat.exprs.push(self.exprs[idx].clone());
            mat.pats.push(new_row);
        }
        mat.vars = vars;
        // We now have `let val ($x0, $x1... fresh vars) = x in case [$x0, $x1...]
        let decl = Decl::Val(Rule { pat, expr: base });

        let res = mat.compile(ctx, ty);
        let sp = res.span;
        Expr::new(
            ctx.arena.exprs.alloc(ExprKind::Let(vec![decl], res)),
            ty,
            sp,
        )
    }

    /// This is basically the same thing as the record rule, but for data
    /// constructors. We want to select all of the rows in the first column
    /// that will match the constructor `head` (e.g. `head` itself, and wildcard)
    fn specialize(
        &self,
        ctx: &mut Context<'a>,
        ty: &'a Type<'a>,
        head: &Constructor,
        arity: bool,
    ) -> Expr<'a> {
        dbg!(&self);

        let mut mat = Matrix::default();
        for (idx, row) in self.pats.iter().enumerate() {
            let mut new_row: Vec<Pat> = row.iter().skip(1).cloned().collect();
            match &row[0].pat {
                PatKind::App(con, Some(arg)) if con == head => {
                    new_row.insert(0, *arg);
                }
                PatKind::App(con, None) if con == head => {}
                PatKind::Wild => {
                    if arity {
                        new_row.insert(0, self.mk_wild(ctx, row[0].ty));
                    }
                }
                _ => continue,
            }
            mat.exprs.push(self.exprs[idx].clone());
            mat.pats.push(new_row);
        }
        mat.vars = self.vars.clone();
        if !arity {
            mat.vars.remove(0);
        }
        // do we need to mess with mat.vars more?
        mat.compile(ctx, ty)
    }

    /// Generate a case expression for the data constructors in the first column
    fn sum_rule(&self, ctx: &mut Context<'a>, ty: &'a Type<'a>) -> Expr<'a> {
        // Generate the set of constructors appearing in the column
        let mut set = HashMap::new();
        for row in &self.pats {
            if let PatKind::App(con, p) = &row[0].pat {
                set.insert(con, p.map(|p| p.ty));
            }
        }

        // We only use `true` and `false` or `cons` and `nil`, so we know
        // there are only 2 constructors in each datatype. Otherwise we
        // would need to query a context to determine this
        let exhaustive = set.len() == 2;

        let mut rules = Vec::new();
        for (con, arg_ty) in set {
            // In a real system, we would have some context to pull the number
            // of data constructors for a datatype, and the arity of each
            // data constructor. We just mock it instead
            let expr = self.specialize(ctx, ty, con, arg_ty.is_some());

            let arg = match arg_ty {
                Some(ty) => Some(self.mk_wild(ctx, ty)),
                None => None,
            };
            let pat = Pat::new(
                ctx.arena.pats.alloc(PatKind::App(*con, arg)),
                self.pats[0][0].ty,
                Span::dummy(),
            );
            rules.push(Rule { pat, expr });
        }

        // If we don't have an exhaustive match, generate a default matrix
        if !exhaustive {
            let pat = self.mk_wild(ctx, self.pats[0][0].ty);
            let expr = self.default_matrix(ctx, ty);
            rules.push(Rule { pat, expr });
        }
        Expr::new(
            ctx.arena.exprs.alloc(ExprKind::Case(self.vars[0], rules)),
            ty,
            Span::dummy(),
        )
        // Expr::Case(Box::new(Expr::Var(self.vars[0].clone())), rules)
    }

    /// Compute the "default" matrix
    fn default_matrix(&self, ctx: &mut Context<'a>, ty: &'a Type<'a>) -> Expr<'a> {
        let mut mat = Matrix::default();
        mat.vars = self.vars.clone();
        mat.vars.remove(0);

        for (idx, row) in self.pats.iter().enumerate() {
            if let Some(true) = row.first().map(Pat::wild) {
                mat.pats.push(row.iter().skip(1).cloned().collect());
                mat.exprs.push(self.exprs[idx].clone());
            }
        }
        mat.compile(ctx, ty)
    }

    /// Compile a [`Matrix`] into a source-level expression
    pub fn compile(&mut self, ctx: &mut Context<'a>, ty: &'a Type<'a>) -> Expr<'a> {
        dbg!(&self);

        if self.pats.is_empty() {
            // We have an in-exhaustive case expression
            let matchh = Expr::new(
                ctx.arena
                    .exprs
                    .alloc(ExprKind::Con(crate::builtin::constructors::C_MATCH, vec![])),
                ty,
                Span::zero(),
            );
            Expr::new(
                ctx.arena.exprs.alloc(ExprKind::Raise(matchh)),
                ty,
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
                    PatKind::Record(fields) => return self.record_rule(ctx, ty, fields),
                    PatKind::App(_, _) => return self.sum_rule(ctx, ty),
                    _ => continue,
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
                self.compile(ctx, ty)
            } else {
                self.default_matrix(ctx, ty)
            }
        }
    }
}
