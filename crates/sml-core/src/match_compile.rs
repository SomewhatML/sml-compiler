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

use crate::builtin::constructors::{C_BIND, C_MATCH};
use crate::elaborate::{Context, ElabError, ErrorKind};
use crate::types::{Constructor, Type};
use crate::{Decl, Expr, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord, Var};
use rustc_hash::{FxHashMap, FxHashSet};
use sml_util::diagnostics::Level;
use sml_util::interner::Symbol;
use sml_util::span::Span;
use sml_util::Const;
use std::collections::VecDeque;

pub struct MatchRule<'a> {
    pub pat: Pat<'a>,
    pub expr: Expr<'a>,
    pub sym: Symbol,
    pub bindings: Vec<Var<'a>>,
}

pub fn case<'a>(
    ctx: &mut Context<'a>,
    scrutinee: Expr<'a>,
    ret_ty: &'a Type<'a>,
    rules: Vec<MatchRule<'a>>,
    span: Span,
) -> Expr<'a> {
    let test = ctx.fresh_var();
    let pats = rules.iter().map(|r| vec![r.pat]).collect();

    let mut diags = MatchDiags::with_capacity(span, rules.len(), C_MATCH);
    let (mut decls, rules) = preflight(ctx, rules, &mut diags);

    let tyvars = scrutinee.ty.ftv_rank(ctx.tyvar_rank + 1);
    decls.push(Decl::Val(tyvars, test, scrutinee));
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
    let expr = mat.compile(&mut facts, &mut diags);
    diags.emit_diagnostics(ctx);
    Expr::new(
        ctx.arena.exprs.alloc(ExprKind::Let(decls, expr)),
        expr.ty,
        expr.span,
    )
}

pub fn fun<'a>(
    ctx: &mut Context<'a>,
    ret_ty: &'a Type<'a>,
    vars: Vec<Var<'a>>,
    pats: Vec<Vec<Pat<'a>>>,
    rules: Vec<MatchRule<'a>>,
    span: Span,
) -> Expr<'a> {
    let test = ctx.fresh_var();
    let mut diags = MatchDiags::with_capacity(span, rules.len(), C_MATCH);
    let (decls, rules) = preflight(ctx, rules, &mut diags);

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

    let expr = mat.compile(&mut facts, &mut diags);
    diags.emit_diagnostics(ctx);
    Expr::new(
        ctx.arena.exprs.alloc(ExprKind::Let(decls, expr)),
        expr.ty,
        expr.span,
    )
}

pub fn val<'a>(ctx: &mut Context<'a>, tyvars: Vec<usize>, rule: MatchRule<'a>) -> Vec<Decl<'a>> {
    let span = rule.pat.span + rule.expr.span;
    let test = ctx.fresh_var();
    let result = ctx.fresh_var();

    let MatchRule {
        pat,
        expr,
        bindings,
        sym,
    } = rule;

    let expr = match bindings.len() {
        0 => expr,
        1 => ctx.arena.expr_var(bindings[0].0, bindings[0].1, Vec::new()),
        _ => ctx.arena.expr_tuple(bindings.iter().copied()),
    };

    let mut decls = match bindings.len() {
        0 => Vec::new(),
        1 => {
            let expr = ctx.arena.expr_var(result, bindings[0].1, Vec::new());
            vec![Decl::Val(Vec::new(), bindings[0].0, expr)]
        }
        _ => {
            let te = ctx.arena.expr_var(result, expr.ty, Vec::new());
            bindings
                .iter()
                .enumerate()
                .map(|(idx, (var, ty))| {
                    let expr = Expr::new(
                        ctx.arena
                            .exprs
                            .alloc(ExprKind::Selector(te, Symbol::tuple_field(idx as u32 + 1))),
                        ty,
                        Span::dummy(),
                    );
                    Decl::Val(Vec::new(), *var, expr)
                })
                .collect()
        }
    };

    let pats = vec![vec![rule.pat]];
    let mut diags = MatchDiags::with_capacity(span, 1, C_BIND);

    let (mut letdecls, rules) = preflight(
        ctx,
        vec![MatchRule {
            pat,
            expr,
            bindings,
            sym,
        }],
        &mut diags,
    );

    letdecls.push(Decl::Val(Vec::new(), test, rule.expr));

    let mut mat = Matrix {
        ctx,
        pats,
        rules,
        ret_ty: expr.ty,
        span,
        test,
        vars: vec![(test, rule.expr.ty)],
    };

    let mut facts = Facts::default();
    let expr = Expr::new(
        ctx.arena
            .exprs
            .alloc(ExprKind::Let(letdecls, mat.compile(&mut facts, &mut diags))),
        expr.ty,
        span,
    );
    diags.emit_diagnostics(ctx);
    decls.insert(0, Decl::Val(Vec::new(), result, expr));
    decls
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
fn preflight<'a>(
    ctx: &Context<'a>,
    rules: Vec<MatchRule<'a>>,
    diags: &mut MatchDiags,
) -> (Vec<Decl<'a>>, Vec<Rule<'a>>) {
    let mut finished = Vec::new();
    let mut decls = Vec::new();
    for MatchRule {
        pat,
        expr,
        bindings,
        sym,
    } in rules
    {
        let lambda = match bindings.len() {
            0 => Lambda {
                arg: ctx.fresh_var(),
                body: expr,
                ty: ctx.arena.types.unit(),
            },
            1 => {
                let (arg, ty) = bindings[0];
                Lambda {
                    arg,
                    body: expr,
                    ty,
                }
            }
            _ => {
                let arg = ctx.fresh_var();
                let ty = ctx.arena.ty_tuple(bindings.iter().map(|(_, t)| *t));
                let var_expr = ctx.arena.expr_var(arg, ty, Vec::new());

                let decls = bindings
                    .into_iter()
                    .enumerate()
                    .map(|(idx, (var, ty))| {
                        let expr = Expr::new(
                            ctx.arena.exprs.alloc(ExprKind::Selector(
                                var_expr,
                                Symbol::tuple_field(idx as u32 + 1),
                            )),
                            ty,
                            var_expr.span,
                        );
                        Decl::Val(Vec::new(), var, expr)
                    })
                    .collect();

                let body = Expr::new(
                    ctx.arena.exprs.alloc(ExprKind::Let(decls, expr)),
                    expr.ty,
                    expr.span,
                );

                // assign the tuple of bound pattern vars to a fresh var, which we will de-tuple
                // inside of the lambda body
                // let body = ctx
                //     .arena
                //     .let_detuple(vars.clone(), arg, expr, ctx.tyvar_rank + 1);
                Lambda { arg, body, ty }
            }
        };

        let ty = ctx.arena.types.arrow(lambda.ty, lambda.body.ty);
        let name = ctx.fresh_var();
        decls.push(Decl::Fun(Vec::new(), vec![(name, lambda)]));

        finished.push(Rule {
            pat,
            expr: ctx.arena.expr_var(name, ty, Vec::new()),
        });

        diags.renamed.push((expr.span, name));
    }
    (decls, finished)
}

#[derive(Clone)]
pub enum Fact {
    Con(Constructor, Option<Symbol>),
    Record(SortedRecord<Symbol>),
}

#[derive(Default, Clone)]
pub struct Facts {
    v: Vec<(Symbol, Fact)>,
}

impl Facts {
    pub fn add(&mut self, var: Symbol, fact: Fact) {
        self.v.push((var, fact))
    }

    pub fn bind<'a>(&self, var: Symbol, pat: Pat<'a>) -> FxHashMap<Symbol, Var<'a>> {
        let mut map = FxHashMap::default();
        let mut facts = FxHashMap::default();
        // let mut vec = Vec::new();
        for (sym, fact) in self.v.iter().rev() {
            facts.insert(sym, fact);
        }

        let mut queue = VecDeque::new();
        queue.push_back((&var, &pat));
        while let Some((var, pat)) = queue.pop_front() {
            match pat.kind {
                PatKind::Var(x) => {
                    if map.insert(*x, (*var, pat.ty)).is_some() {
                        panic!("Bug: Facts.bind rebinding")
                    }
                }
                PatKind::App(_, Some(pat)) => match facts.get(var) {
                    Some(Fact::Con(_, Some(x))) => {
                        queue.push_back((x, pat));
                    }
                    _ => panic!("Bug: Facts.bind constructor"),
                },
                PatKind::Record(rp) => match facts.get(var) {
                    Some(Fact::Record(rx)) => {
                        for (rp, rx) in rp.iter().zip(rx.iter()) {
                            queue.push_back((&rx.data, &rp.data));
                        }
                    }
                    _ => panic!("Bug: Facts.bind record"),
                },
                _ => continue,
            }
        }

        map
    }
}

pub struct MatchDiags {
    span: Span,
    // mapping from match arm index to renamed/abstracted arms
    renamed: Vec<(Span, Symbol)>,
    // Which arms were reached
    reached: FxHashSet<Symbol>,
    constr: Constructor,
    // Did we emit a `raise Match`?
    inexhaustive: bool,
}

impl MatchDiags {
    pub fn with_capacity(span: Span, capacity: usize, constr: Constructor) -> MatchDiags {
        MatchDiags {
            span,
            renamed: Vec::with_capacity(capacity),
            reached: FxHashSet::default(),
            constr,
            inexhaustive: false,
        }
    }

    pub fn emit_diagnostics(self, ctx: &mut Context<'_>) {
        for (sp, sym) in self.renamed {
            if !self.reached.contains(&sym) {
                ctx.elab_errors
                    .push(ElabError::new(sp, "unreachable match arm").kind(ErrorKind::Redundant));
            }
        }
        if self.inexhaustive {
            match self.constr {
                C_BIND => {
                    let level = match ctx.scope_depth() {
                        0 => Level::Warn,
                        _ => Level::Error,
                    };
                    ctx.elab_errors.push(
                        ElabError::new(self.span, "inexhaustive `val` binding")
                            .kind(ErrorKind::Inexhaustive)
                            .level(level),
                    );
                }
                _ => {
                    ctx.elab_errors.push(
                        ElabError::new(self.span, "inexhaustive `case` expression")
                            .kind(ErrorKind::Inexhaustive),
                    );
                }
            }
        }
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
        match self.kind {
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
    fn record_rule(
        &self,
        facts: &mut Facts,
        diags: &mut MatchDiags,
        fields: &SortedRecord<Pat<'a>>,
    ) -> Expr<'a> {
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

            match &row[0].kind {
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

        let base_expr = self.ctx.arena.expr_var(base.0, base.1, Vec::new());
        let decls = record
            .into_iter()
            .map(|(label, var, ty)| {
                let expr = Expr::new(
                    self.ctx
                        .arena
                        .exprs
                        .alloc(ExprKind::Selector(base_expr, label)),
                    ty,
                    Span::dummy(),
                );
                Decl::Val(Vec::new(), var, expr)
            })
            .collect();

        Expr::new(
            self.ctx
                .arena
                .exprs
                .alloc(ExprKind::Let(decls, mat.compile(facts, diags))),
            self.ret_ty,
            Span::dummy(),
        )

        // self.ctx.arena.let_derecord(
        //     record,
        //     base.0,
        //     mat.compile(facts, diags),
        //     self.ctx.tyvar_rank + 1,
        // )
    }

    /// This is basically the same thing as the record rule, but for data
    /// constructors. We want to select all of the rows in the first column
    /// that will match the constructor `head` (e.g. `head` itself, and
    /// wildcard)
    fn specialize(
        &self,
        facts: &mut Facts,
        diags: &mut MatchDiags,
        head: &Constructor,
        arity: Option<Var<'a>>,
    ) -> Expr<'a> {
        let mut mat = self.shallow();
        for (idx, row) in self.pats.iter().enumerate() {
            let mut new_row: Vec<Pat> = row.iter().skip(1).copied().collect();
            match &row[0].kind {
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
        mat.compile(facts, diags)
    }

    /// Generate a case expression for the data constructors in the first column
    fn sum_rule(&self, facts: &mut Facts, diags: &mut MatchDiags) -> Expr<'a> {
        // Generate the set of constructors appearing in the column
        let mut set = FxHashMap::default();
        let mut type_arity = 0;
        for row in &self.pats {
            if let PatKind::App(con, p) = &row[0].kind {
                set.insert(con, p.map(|p| p.ty));
                type_arity = con.type_arity;
            }
        }
        let mut set = set.into_iter().collect::<Vec<_>>();
        set.sort_by(|a, b| a.0.name.cmp(&b.0.name));

        let exhaustive = set.len() == type_arity as usize;
        let mut rules = Vec::new();
        for (con, arg_ty) in set {
            let fresh = self.ctx.fresh_var();
            let mut f = facts.clone();
            let expr = self.specialize(&mut f, diags, con, arg_ty.map(|ty| (fresh, ty)));

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
            let expr = self.default_matrix(facts, diags);
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

    /// This is basically the same thing as the record rule, but for data
    /// constructors. We want to select all of the rows in the first column
    /// that will match the constructor `head` (e.g. `head` itself, and
    /// wildcard)
    fn specialize_const(
        &self,
        facts: &mut Facts,
        diags: &mut MatchDiags,
        head: &Const,
    ) -> Expr<'a> {
        let mut mat = self.shallow();
        for (idx, row) in self.pats.iter().enumerate() {
            match &row[0].kind {
                PatKind::Const(c) if c == head => {}
                PatKind::Wild | PatKind::Var(_) => {}
                _ => continue,
            }
            let new_row: Vec<Pat> = row.iter().skip(1).copied().collect();
            mat.rules.push(self.rules[idx]);
            mat.pats.push(new_row);
        }
        mat.vars.remove(0);
        mat.compile(facts, diags)
    }

    /// Generate a case expression for the data constructors in the first column
    fn const_rule(&self, facts: &mut Facts, diags: &mut MatchDiags) -> Expr<'a> {
        // Generate the set of constructors appearing in the column
        let mut set = FxHashSet::default();
        for row in &self.pats {
            match &row[0].kind {
                PatKind::Const(con) => {
                    set.insert(con);
                }
                _ => continue,
            }
        }
        let mut set = set.into_iter().collect::<Vec<_>>();
        set.sort_by(|a, b| a.cmp(&b));

        let mut rules = Vec::new();
        for &con in &set {
            // Clone facts so we don't polute other branches with identical bound
            let mut f = facts.clone();
            let expr = self.specialize_const(&mut f, diags, con);

            let pat = Pat::new(
                self.ctx.arena.pats.alloc(PatKind::Const(*con)),
                self.pats[0][0].ty,
                Span::dummy(),
            );
            rules.push(Rule { pat, expr });
        }

        if set.len() == 1 && set[0] == &Const::Unit {
            // Unit is exhaustive
        } else {
            let pat = self.mk_wild(self.pats[0][0].ty);
            let expr = self.default_matrix(facts, diags);
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

    /// Compute the "default" matrix
    fn default_matrix(&self, facts: &mut Facts, diags: &mut MatchDiags) -> Expr<'a> {
        let mut mat = self.shallow();
        mat.vars.remove(0);

        for (idx, row) in self.pats.iter().enumerate() {
            if let Some(true) = row.first().map(Pat::wild) {
                mat.pats.push(row.iter().skip(1).copied().collect());
                mat.rules.push(self.rules[idx]);
            }
        }
        // mat.test = mat.vars[0].0;
        mat.compile(facts, diags)
    }

    /// Compile a [`Matrix`] into a source-level expression
    fn compile(&mut self, facts: &mut Facts, diags: &mut MatchDiags) -> Expr<'a> {
        if self.pats.is_empty() {
            let matchh = Expr::new(
                self.ctx
                    .arena
                    .exprs
                    .alloc(ExprKind::Con(diags.constr, vec![])),
                self.ret_ty,
                Span::zero(),
            );

            diags.inexhaustive = true;

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
                    self.ctx.arena.expr_var(*bound, ty, Vec::new())
                }
                _ => self.ctx.arena.expr_tuple(vars.into_iter().map(|(sym, ty)| {
                    let (bound, _) = map.get(&sym).expect("Bug: Facts.bind");
                    (*bound, ty)
                })),
            };

            diags.reached.insert(self.rules[0].expr.as_symbol());

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
                match &row[0].kind {
                    PatKind::Record(fields) => return self.record_rule(facts, diags, fields),
                    PatKind::App(_, _) => return self.sum_rule(facts, diags),
                    PatKind::Const(_) => return self.const_rule(facts, diags),
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
                self.compile(facts, diags)
            } else {
                self.default_matrix(facts, diags)
            }
        }
    }
}

fn collect_vars<'a>(pat: Pat<'a>) -> Vec<Var<'a>> {
    let mut v = Vec::new();
    let mut queue = VecDeque::new();
    queue.push_back(pat);
    while let Some(pat) = queue.pop_front() {
        match pat.kind {
            PatKind::Var(s) => v.push((*s, pat.ty)),
            PatKind::Record(fields) => queue.extend(fields.iter().map(|row| row.data)),
            PatKind::App(_, Some(pat)) => queue.push_back(*pat),
            _ => {}
        }
    }
    v
}
