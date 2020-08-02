//! Notes on building a new pattern matrix.
//!
//! # Invariants:
//!
//! * Type safety - the case expression that is being transformed should have
//!   been previously verified to be well typed
//! * `test` should be a fresh variable of the domain type of the match rules
//! * `pats` is a mutable 'pattern matrix', where things might be expanded and
//!   contracted
//! * `rules` contains the original pattern in the AST, and the abstracted
//!   expression
//!     - abstraction is done in `preflight`, where case expression bodies are
//!       lifted to an enclosing level and converted to functions
//! * `vars` contains the current "in-scope" destructured variables

use super::*;
use elaborate::Context;
use sml_util::diagnostics::Diagnostic;
use std::collections::{HashMap, HashSet, VecDeque};

pub type Var<'a> = (Symbol, &'a Type<'a>);

pub fn case<'a>(
    ctx: &Context<'a>,
    scrutinee: Expr<'a>,
    ret_ty: &'a Type<'a>,
    rules: Vec<Rule<'a>>,
    span: Span,
) -> Expr<'a> {
    let test = ctx.fresh_var();
    let pats = rules.iter().map(|r| vec![r.pat]).collect();
    let (mut decls, rules) = preflight(ctx, rules);

    decls.push(Decl::Val(Rule {
        pat: ctx.arena.pat_var(test, scrutinee.ty),
        expr: scrutinee,
    }));
    let mut mat = Matrix {
        ctx,
        pats,
        rules,
        ret_ty,
        span,
        test,
        vars: vec![(test, scrutinee.ty)],
    };

    let mut facts = Facts::default();
    let expr = mat.compile(&mut facts);
    Expr::new(
        ctx.arena.exprs.alloc(ExprKind::Let(decls, expr)),
        expr.ty,
        expr.span,
    )
}

pub fn fun<'a>(
    ctx: &Context<'a>,
    ret_ty: &'a Type<'a>,
    vars: Vec<Var<'a>>,
    pats: Vec<Vec<Pat<'a>>>,
    rules: Vec<Rule<'a>>,
    span: Span,
) -> Expr<'a> {
    let test = ctx.fresh_var();
    let (decls, rules) = preflight(ctx, rules);

    let rec = SortedRecord::new_unchecked(
        vars.iter()
            .enumerate()
            .map(|(idx, (s, _))| Row {
                label: Symbol::tuple_field(idx as u32 + 1),
                data: *s,
                span: Span::dummy(),
            })
            .collect(),
    );
    let mut facts = Facts::default();
    let fact = crate::match_compile::Fact::Record(rec);
    facts.add(test, fact);

    let mut mat = Matrix {
        ctx,
        pats,
        rules,
        ret_ty,
        span,
        test,
        vars,
    };

    let expr = mat.compile(&mut facts);
    Expr::new(
        ctx.arena.exprs.alloc(ExprKind::Let(decls, expr)),
        expr.ty,
        expr.span,
    )
}

/// Abstract match bodies into functions, to be declared prior to the
/// body of the case expression
///
/// # Example
/// from MLton
/// ```sml
///   case x of
///        (_, C1 a)    => e1
///      | (C2 b, C3 c) => e2
/// ```
///
/// Translated to
///
/// ```sml    
///   let
///      fun f1 a = e1
///      fun f2 (b, c) = e2
///   in
///     case x of
///        ...
/// ```
fn preflight<'a>(ctx: &Context<'a>, rules: Vec<Rule<'a>>) -> (Vec<Decl<'a>>, Vec<Rule<'a>>) {
    let mut finished = Vec::new();
    let mut decls = Vec::new();
    for Rule { pat, expr } in rules {
        let vars = collect_vars(pat);
        let arg = ctx.fresh_var();

        let (body, ty) = match vars.len() {
            0 => (expr, ctx.arena.types.unit()),
            1 => {
                let (var, ty) = vars[0];
                let pat = ctx.arena.pat_var(var, ty);
                let ex = ctx.arena.expr_var(arg, ty);
                let decl = Decl::Val(Rule { pat, expr: ex });
                (
                    Expr::new(
                        ctx.arena.exprs.alloc(ExprKind::Let(vec![decl], expr)),
                        expr.ty,
                        expr.span,
                    ),
                    ty,
                )
            }
            _ => {
                let body = ctx.arena.let_detuple(vars.clone(), arg, expr);
                let ty = ctx.arena.ty_tuple(vars.into_iter().map(|(_, t)| t));
                (body, ty)
            }
        };

        // assign the tuple of bound pattern vars to a fresh var, which we will de-tuple
        // inside of the lambda body
        let lambda = Lambda { arg, body, ty };

        let ty = ctx.arena.types.arrow(lambda.ty, expr.ty);
        let name = ctx.fresh_var();
        decls.push(Decl::Fun(Vec::new(), vec![(name, lambda)]));

        finished.push(Rule {
            pat,
            expr: ctx.arena.expr_var(name, ty),
        })
    }
    (decls, finished)
}

#[derive(Debug, Clone)]
pub enum Fact {
    Con(Constructor, Option<Symbol>),
    Record(SortedRecord<Symbol>),
}

#[derive(Default, Debug, Clone)]
pub struct Facts {
    v: Vec<(Symbol, Fact)>,
}

impl Facts {
    pub fn add(&mut self, var: Symbol, fact: Fact) {
        self.v.push((var, fact))
    }

    pub fn bind<'a>(&self, var: Symbol, pat: Pat<'a>) -> HashMap<Symbol, Var<'a>> {
        let mut map = HashMap::new();
        let mut facts = HashMap::new();
        // let mut vec = Vec::new();
        for (sym, fact) in self.v.iter().rev() {
            facts.insert(sym, fact);
        }

        let mut queue = VecDeque::new();
        queue.push_back((&var, &pat));
        while let Some((var, pat)) = queue.pop_front() {
            match pat.pat {
                PatKind::Var(x) => {
                    if let Some(_) = map.insert(*x, (*var, pat.ty)) {
                        panic!("Bug: Facts.bind rebinding of {:?} => {:?}", var, x)
                    }
                }
                PatKind::App(_, Some(pat)) => match facts.get(var) {
                    Some(Fact::Con(_, Some(x))) => {
                        queue.push_back((x, pat));
                    }
                    x => panic!("Bug: Facts.bind constructor {:?} {:?}", var, x),
                },
                PatKind::Record(rp) => match facts.get(var) {
                    Some(Fact::Record(rx)) => {
                        for (rp, rx) in rp.iter().zip(rx.iter()) {
                            queue.push_back((&rx.data, &rp.data));
                        }
                    }
                    x => panic!("Bug: Facts.bind record {:?} {:?}", var, x),
                },
                _ => continue,
            }
        }

        map
    }
}

pub struct Matrix<'a, 'ctx> {
    // ref to the context so we can allocate stuff in arenas
    ctx: &'ctx Context<'a>,
    // return type
    ret_ty: &'a Type<'a>,
    // Span of the original case expression
    span: Span,

    pub pats: Vec<Vec<Pat<'a>>>,
    // Store the original rule
    pub rules: Vec<Rule<'a>>,

    test: Symbol,
    pub vars: Vec<Var<'a>>,
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
            test: self.test,
            span: self.span,
            pats: Vec::with_capacity(self.pats.len()),
            rules: Vec::with_capacity(self.rules.len()),
        }
    }
    fn mk_wild(&self, ty: &'a Type<'a>) -> Pat<'a> {
        Pat::new(self.ctx.arena.pats.wild(), ty, Span::dummy())
    }

    /// Deconstruct a record or tuple pattern, binding each field to a fresh
    /// variable, and flattening all of the record patterns in the first column
    /// [{a, b, c}, ...] --> [a, b, c, ...]
    fn record_rule(&self, facts: &mut Facts, fields: &SortedRecord<Pat<'a>>) -> Expr<'a> {
        // This part is a little tricky. We need to generate a fresh variable
        // for every field in the pattern
        let mut vars = self.vars.clone();
        let base = vars.remove(0);

        // Lots of work to just create a new pattern to bind
        let mut record = Vec::new();
        let mut fact_r = Vec::new();

        for (idx, row) in fields.iter().enumerate() {
            let fresh = self.ctx.fresh_var();
            fact_r.push(row.fmap(|_| fresh));
            record.push((row.label, fresh, row.data.ty));
            // insert the new variables into the matrice's variable
            vars.insert(idx, (fresh, row.data.ty));
        }

        facts.add(
            self.vars[0].0,
            Fact::Record(SortedRecord::new_unchecked(fact_r)),
        );

        let mut mat = self.shallow();
        for (idx, row) in self.pats.iter().enumerate() {
            let mut new_row: Vec<Pat> = row.iter().skip(1).copied().collect();

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
            mat.rules.push(self.rules[idx]);
            mat.pats.push(new_row);
        }
        mat.vars = vars;
        self.ctx
            .arena
            .let_derecord(record, base.0, mat.compile(facts))
    }

    /// This is basically the same thing as the record rule, but for data
    /// constructors. We want to select all of the rows in the first column
    /// that will match the constructor `head` (e.g. `head` itself, and
    /// wildcard)
    fn specialize(
        &self,
        facts: &mut Facts,
        head: &Constructor,
        arity: Option<Var<'a>>,
    ) -> Expr<'a> {
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
                        new_row.insert(0, self.ctx.arena.pat_var(name, ty));
                    }
                }
                _ => continue,
            }
            mat.rules.push(self.rules[idx]);
            mat.pats.push(new_row);
        }

        match arity {
            Some((name, _)) => {
                facts.add(mat.vars[0].0, Fact::Con(*head, Some(name)));
                mat.vars[0].0 = name;
            }
            None => {
                mat.vars.remove(0);
            }
        }
        // mat.test = mat.vars[0].0;
        mat.compile(facts)
    }

    /// Generate a case expression for the data constructors in the first column
    fn sum_rule(&self, facts: &mut Facts) -> Expr<'a> {
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
            let mut f = facts.clone();
            let expr = self.specialize(&mut f, con, arg_ty.map(|ty| (fresh, ty)));

            let arg = match arg_ty {
                Some(ty) => Some(self.ctx.arena.pat_var(fresh, ty)),
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
            let expr = self.default_matrix(facts);
            rules.push(Rule { pat, expr });
        }

        Expr::new(
            self.ctx.arena.exprs.alloc(ExprKind::Case(
                self.ctx.arena.expr_var(self.vars[0].0, self.vars[0].1),
                rules,
            )),
            self.ret_ty,
            Span::dummy(),
        )
    }

    /// This is basically the same thing as the record rule, but for data
    /// constructors. We want to select all of the rows in the first column
    /// that will match the constructor `head` (e.g. `head` itself, and
    /// wildcard)
    fn specialize_const(&self, facts: &mut Facts, head: &Const) -> Expr<'a> {
        let mut mat = self.shallow();
        for (idx, row) in self.pats.iter().enumerate() {
            match &row[0].pat {
                PatKind::Const(c) if c == head => {}
                PatKind::Wild | PatKind::Var(_) => {}
                _ => continue,
            }
            let new_row: Vec<Pat> = row.iter().skip(1).copied().collect();
            mat.rules.push(self.rules[idx]);
            mat.pats.push(new_row);
        }
        mat.vars.remove(0);
        mat.compile(facts)
    }

    /// Generate a case expression for the data constructors in the first column
    fn const_rule(&self, facts: &mut Facts) -> Expr<'a> {
        // Generate the set of constructors appearing in the column
        let mut set = HashSet::new();
        for row in &self.pats {
            match &row[0].pat {
                PatKind::Const(con) => {
                    set.insert(con);
                }
                _ => continue,
            }
        }

        let mut rules = Vec::new();
        for con in set {
            // Clone facts so we don't polute other branches with identical bound
            let mut f = facts.clone();
            let expr = self.specialize_const(&mut f, con);

            let pat = Pat::new(
                self.ctx.arena.pats.alloc(PatKind::Const(*con)),
                self.pats[0][0].ty,
                Span::dummy(),
            );
            rules.push(Rule { pat, expr });
        }

        let pat = self.mk_wild(self.pats[0][0].ty);
        let expr = self.default_matrix(facts);
        rules.push(Rule { pat, expr });

        Expr::new(
            self.ctx.arena.exprs.alloc(ExprKind::Case(
                self.ctx.arena.expr_var(self.vars[0].0, self.vars[0].1),
                rules,
            )),
            self.ret_ty,
            Span::dummy(),
        )
    }

    /// Compute the "default" matrix
    fn default_matrix(&self, facts: &mut Facts) -> Expr<'a> {
        let mut mat = self.shallow();
        mat.vars.remove(0);

        for (idx, row) in self.pats.iter().enumerate() {
            if let Some(true) = row.first().map(Pat::wild) {
                mat.pats.push(row.iter().skip(1).copied().collect());
                mat.rules.push(self.rules[idx]);
            }
        }
        // mat.test = mat.vars[0].0;
        mat.compile(facts)
    }

    /// Compile a [`Matrix`] into a source-level expression
    fn compile(&mut self, facts: &mut Facts) -> Expr<'a> {
        if self.pats.is_empty() {
            // We have an in-exhaustive case expression
            // TODO: Emit better diagnostics
            // self.ctx.diags.push(Diagnostic::error(self.span, "inexhaustive pattern
            // matching"));
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
            // so it matches. return the body of the match rule with
            // renamed variable applied to it, if necessary

            let map = facts.bind(self.test, self.rules[0].pat);
            let mut vars = collect_vars(self.rules[0].pat);

            // Generate arguments to the abstracted match arm bodies
            let args = match vars.len() {
                0 => Expr::new(
                    self.ctx.arena.exprs.alloc(ExprKind::Const(Const::Unit)),
                    self.ctx.arena.types.unit(),
                    self.rules[0].expr.span,
                ),
                1 => {
                    let (var, ty) = vars.pop().unwrap();
                    let (bound, _) = map.get(&var).expect("Bug: Facts.bind");
                    self.ctx.arena.expr_var(*bound, ty)
                }
                _ => self.ctx.arena.expr_tuple(vars.into_iter().map(|(sym, ty)| {
                    let (bound, _) = map.get(&sym).expect("Bug: Facts.bind");
                    (ExprKind::Var(*bound), ty)
                })),
            };

            // TODO: Check types just in case
            Expr::new(
                self.ctx
                    .arena
                    .exprs
                    .alloc(ExprKind::App(self.rules[0].expr, args)),
                self.ret_ty,
                self.rules[0].expr.span,
            )
        } else {
            // There is at least one non-wild pattern in the matrix somewhere
            for row in &self.pats {
                match &row[0].pat {
                    PatKind::Record(fields) => return self.record_rule(facts, fields),
                    PatKind::App(_, _) => return self.sum_rule(facts),
                    PatKind::Const(_) => return self.const_rule(facts),
                    PatKind::Wild | PatKind::Var(_) => continue,
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
                // Swap variables as well
                self.vars.swap(0, col);
                self.compile(facts)
            } else {
                self.default_matrix(facts)
            }
        }
    }
}

impl fmt::Debug for Matrix<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "matrix {:?}\n", self.vars)?;
        for (pats, exprs) in self.pats.iter().zip(self.rules.iter()) {
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
        Ok(())
    }
}

fn collect_vars<'a>(pat: Pat<'a>) -> Vec<Var<'a>> {
    let mut v = Vec::new();
    let mut queue = VecDeque::new();
    queue.push_back(pat);
    while let Some(pat) = queue.pop_front() {
        match pat.pat {
            PatKind::Var(s) => v.push((*s, pat.ty)),
            PatKind::Record(fields) => queue.extend(fields.iter().map(|row| row.data)),
            PatKind::App(_, Some(pat)) => queue.push_back(*pat),
            _ => {}
        }
    }
    v
}
