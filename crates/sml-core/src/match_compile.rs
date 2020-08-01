use super::*;
use elaborate::Context;
use std::collections::{HashMap, HashSet, VecDeque};

pub type Var<'a> = (Symbol, &'a Type<'a>);

#[derive(Debug, Clone)]
enum Fact {
    Con(Constructor, Option<Symbol>),
    Record(SortedRecord<Symbol>),
}

#[derive(Default, Debug, Clone)]
struct Facts {
    v: Vec<(Symbol, Fact)>,
}

impl Facts {
    pub fn add(&mut self, var: Symbol, fact: Fact) {
        println!("bind {:?} {:?}", var, fact);
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
            println!("try bind {:?} {:?}", var, pat);
            match pat.pat {
                PatKind::Var(x) => {
                    if let Some(prev) = map.insert(*x, (*var, pat.ty)) {
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

    pub pats: Vec<Vec<Pat<'a>>>,
    // Store the original rule
    pub exprs: Vec<Rule<'a>>,

    test: Symbol,
    vars: Vec<Var<'a>>,
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
            // test: self.vars[0].0,
            test: self.test,
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
        test: Var<'a>,
        // vars: Vec<Var<'a>>,
        rules: Vec<Rule<'a>>,
    ) -> Matrix<'a, 'ctx> {
        let mut mat = Matrix::build(ctx, ret_ty, test, rules.len());
        for rule in rules {
            mat.pats.push(vec![mat.delist(rule.pat)]);
            mat.exprs.push(rule);
        }
        mat
    }

    /// We have this separate for elaborating function bindings
    pub fn build(
        ctx: &'ctx Context<'a>,
        ret_ty: &'a Type<'a>,
        test: Var<'a>,
        // vars: Vec<Var<'a>>,
        cap: usize,
    ) -> Matrix<'a, 'ctx> {
        Matrix {
            ctx,
            ret_ty,
            vars: vec![test],
            test: test.0,
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

    fn mk_let(&self, pat: Pat<'a>, var: Var<'a>, body: Expr<'a>) -> Expr<'a> {
        let (name, ty) = var;
        let expr = self.mk_evar(name, ty);
        Expr::new(
            self.ctx
                .arena
                .exprs
                .alloc(ExprKind::Let(vec![Decl::Val(Rule { pat, expr })], body)),
            self.ret_ty,
            body.span,
        )
    }

    // fn mk_app(&self, expr: Expr<'a>) -> Expr<'a> {
    //     self.vars.iter().copied().fold(expr, |acc, v| {
    //         // TODO: eta-convert expression first so that this works
    //         let ty = acc.ty.de_arrow().map(|(_, t)| t).unwrap_or(self.ctx.arena.types.unit());
    //         Expr::new(self.ctx.arena.exprs.alloc(ExprKind::App(acc, v)), ty, expr.span)
    //     })
    // }

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
        let mut tys = Vec::new();
        let mut span = fields[0].span;

        for (idx, row) in fields.iter().enumerate() {
            let fresh = self.ctx.fresh_var();
            let bind = self.mk_pvar(fresh, row.data.ty);
            // let expr = self.mk_evar(fresh, row.data.ty);
            record.push(row.fmap(|_| bind));
            fact_r.push(row.fmap(|_| fresh));
            tys.push(row.fmap(|p| p.ty));
            vars.push((fresh, row.data.ty));
            println!("binding {:?} {:?}", fresh, row.data);
            vars.insert(idx, (fresh, row.data.ty));
            span.end = row.span.end;
        }
        facts.add(
            self.vars[0].0,
            Fact::Record(SortedRecord::new_unchecked(fact_r)),
        );

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
            mat.exprs.push(self.exprs[idx]);
            mat.pats.push(new_row);
        }
        mat.vars = vars;

        // We now have `let val ($x0, $x1... fresh vars) = x in case [$x0, $x1...]
        self.mk_let(pat, base, mat.compile(facts))
    }

    /// This is basically the same thing as the record rule, but for data
    /// constructors. We want to select all of the rows in the first column
    /// that will match the constructor `head` (e.g. `head` itself, and wildcard)
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
                        new_row.insert(0, self.mk_pvar(name, ty));
                        // new_row.insert(0, self.mk_wild(ty));
                    }
                }
                _ => continue,
            }
            mat.exprs.push(self.exprs[idx]);
            mat.pats.push(new_row);
        }

        match arity {
            Some((name, ty)) => {
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
            println!("spec {:?} {:?}", fresh, con);
            let mut f = facts.clone();
            let expr = self.specialize(&mut f, con, arg_ty.map(|ty| (fresh, ty)));

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
            let expr = self.default_matrix(facts);
            rules.push(Rule { pat, expr });
        }

        Expr::new(
            self.ctx.arena.exprs.alloc(ExprKind::Case(
                self.mk_evar(self.vars[0].0, self.vars[0].1),
                rules,
            )),
            self.ret_ty,
            Span::dummy(),
        )
    }

    /// This is basically the same thing as the record rule, but for data
    /// constructors. We want to select all of the rows in the first column
    /// that will match the constructor `head` (e.g. `head` itself, and wildcard)
    fn specialize_const(&self, facts: &mut Facts, head: &Const) -> Expr<'a> {
        let mut mat = self.shallow();
        for (idx, row) in self.pats.iter().enumerate() {
            match &row[0].pat {
                PatKind::Const(c) if c == head => {}
                PatKind::Wild | PatKind::Var(_) => {}
                _ => continue,
            }
            let new_row: Vec<Pat> = row.iter().skip(1).copied().collect();
            mat.exprs.push(self.exprs[idx]);
            mat.pats.push(new_row);
        }
        mat.vars.remove(0);
        mat.compile(facts)
    }

    /// Generate a case expression for the data constructors in the first column
    fn const_rule2(&self, facts: &mut Facts) -> Expr<'a> {
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
                self.mk_evar(self.vars[0].0, self.vars[0].1),
                rules,
            )),
            self.ret_ty,
            Span::dummy(),
        )
    }

    /// Generate a case expression for the constants in the first column
    fn const_rule(&self, facts: &mut Facts) -> Expr<'a> {
        // Generate the set of constants appearing in the column
        let mut set = HashSet::new();
        let mut rules = Vec::new();
        for (row, rule) in self.pats.iter().zip(&self.exprs) {
            if let PatKind::Const(con) = &row[0].pat {
                if set.insert(con) {
                    // println!("CONST patbind {:?} {:?} {:?}", self.test, rule.pat, facts);

                    // let map = facts.bind(self.test, rule.pat);

                    // let rec = map.iter().map(|(k, v)| Row { label: *k, data: self.mk_evar(*v, self.ctx.arena.types.unit()), span: Span::dummy() }).collect();
                    // let rec = SortedRecord::new(rec);
                    // let expr = Expr::new(self.ctx.arena.exprs.alloc(ExprKind::Record(rec)), self.ctx.arena.types.unit(), Span::dummy());
                    // let expr = Expr::new(self.ctx.arena.exprs.alloc(ExprKind::App(rule.expr, expr)), self.ctx.arena.types.unit(), Span::dummy());
                    let mut matrix = self.shallow();
                    matrix.pats.push(row.iter().skip(1).copied().collect());
                    matrix.exprs.push(*rule);
                    matrix.vars = self.vars.iter().skip(1).copied().collect();
                    let mut f = facts.clone();
                    rules.push(Rule {
                        pat: row[0],
                        expr: matrix.compile(&mut f),
                    });
                }
            }
        }

        // Constants are _always_ non-exhaustive
        let pat = self.mk_wild(self.pats[0][0].ty);
        let expr = self.default_matrix(facts);
        rules.push(Rule { pat, expr });
        dbg!(&rules);
        Expr::new(
            self.ctx.arena.exprs.alloc(ExprKind::Case(
                self.mk_evar(self.vars[0].0, self.vars[0].1),
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
                mat.exprs.push(self.exprs[idx]);
            }
        }
        // mat.test = mat.vars[0].0;
        mat.compile(facts)
    }

    /// Compile a [`Matrix`] into a source-level expression
    fn compile(&mut self, facts: &mut Facts) -> Expr<'a> {
        // dbg!(&self);
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
            // dbg!(facts.bind(self.vars[0].0, pat))
            println!(
                "patbind {:?} {:?} {:?}",
                self.test, self.exprs[0].pat, facts
            );
            let map = facts.bind(self.test, self.exprs[0].pat);
            let vars = collect_vars(self.exprs[0].pat);

            // TODO: Check types just in case
            let args = self.ctx.arena.expr_tuple(vars.into_iter().map(|(sym, ty)| {
                let (bound, _) = map.get(&sym).expect("Bug: Facts.bind");
                (ExprKind::Var(*bound), ty)
            }));

            Expr::new(
                self.ctx
                    .arena
                    .exprs
                    .alloc(ExprKind::App(self.exprs[0].expr, args)),
                self.ret_ty,
                self.exprs[0].expr.span,
            )
        // let rec = map
        //     .iter()
        //     .map(|(k, (name, ty))| Row {
        //         label: *k,
        //         data: self.mk_evar(*name, ty),
        //         span: Span::dummy(),
        //     })
        //     .collect();

        // let rec = SortedRecord::new(rec);

        // let expr = Expr::new(
        //     self.ctx.arena.exprs.alloc(ExprKind::Record(rec)),
        //     self.ctx.arena.types.unit(),
        //     Span::dummy(),
        // );
        // let expr = Expr::new(
        //     self.ctx
        //         .arena
        //         .exprs
        //         .alloc(ExprKind::App(self.exprs[0].expr, expr)),
        //     self.ctx.arena.types.unit(),
        //     Span::dummy(),
        // );
        // println!("map {:?} {:#?}", self.exprs[0], map);
        // self.exprs[0].expr
        // expr
        } else {
            // There is at least one non-wild pattern in the matrix somewhere
            for row in &self.pats {
                match &row[0].pat {
                    PatKind::Record(fields) => return self.record_rule(facts, fields),
                    PatKind::App(_, _) => return self.sum_rule(facts),
                    PatKind::List(_) => todo!(),
                    PatKind::Const(_) => return self.const_rule2(facts),
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
                self.vars.swap(0, col);
                self.compile(facts)
            } else {
                self.default_matrix(facts)
            }
        }
    }

    fn delist(&self, pat: Pat<'a>) -> Pat<'a> {
        match pat.pat {
            PatKind::List(pats) => {
                let nil = Pat::new(
                    self.ctx
                        .arena
                        .pats
                        .alloc(PatKind::App(crate::builtin::constructors::C_NIL, None)),
                    pat.ty,
                    pat.span,
                );
                dbg!(pats.into_iter().fold(nil, |xs, x| {
                    let cons = Pat::new(
                        self.ctx.arena.pats.tuple([*x, xs].iter().copied()),
                        pat.ty,
                        x.span,
                    );
                    Pat::new(
                        self.ctx.arena.pats.alloc(PatKind::App(
                            crate::builtin::constructors::C_CONS,
                            Some(cons),
                        )),
                        pat.ty,
                        pat.span,
                    )
                }))
            }
            _ => pat,
        }
    }

    fn preflight(&self, rules: Vec<Rule<'a>>) -> (Vec<Decl<'a>>, Vec<Rule<'a>>) {
        let mut finished = Vec::new();
        let mut decls = Vec::new();
        for Rule { pat, expr } in rules {
            let vars = collect_vars(pat);
            let arg = self.ctx.fresh_var();

            // assign the tuple of bound pattern vars to a fresh var, which we will de-tuple
            // inside of the lambda body
            let body = self.ctx.arena.let_detuple(vars.clone(), arg, expr);
            let lambda = Lambda {
                arg,
                body,
                ty: self.ctx.arena.ty_tuple(vars.into_iter().map(|(_, t)| t)),
            };

            let ty = self.ctx.arena.types.arrow(lambda.ty, expr.ty);
            // let body = Expr::new(self.ctx.arena.exprs.alloc(ExprKind::Lambda(lambda)), ty, expr.span);

            let name = self.ctx.fresh_var();
            decls.push(Decl::Fun(Vec::new(), vec![(name, lambda)]));

            finished.push(Rule {
                pat,
                expr: self.ctx.arena.expr_var(name, ty),
            })
        }
        (decls, finished)
    }

    pub fn compile_top(&mut self) -> Expr<'a> {
        let mut facts = Facts::default();

        let rules = std::mem::replace(&mut self.exprs, Vec::new());
        let (decls, rules) = self.preflight(rules);
        let _ = std::mem::replace(&mut self.exprs, rules);
        let expr = self.compile(&mut facts);

        Expr::new(
            self.ctx.arena.exprs.alloc(ExprKind::Let(decls, expr)),
            expr.ty,
            expr.span,
        ) // expr
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

fn collect_vars<'a>(pat: Pat<'a>) -> Vec<Var<'a>> {
    let mut v = Vec::new();
    let mut queue = VecDeque::new();
    queue.push_back(pat);
    while let Some(pat) = queue.pop_front() {
        match pat.pat {
            PatKind::Var(s) => v.push((*s, pat.ty)),
            PatKind::List(pats) => queue.extend(pats.iter()),
            PatKind::Record(fields) => queue.extend(fields.iter().map(|row| row.data)),
            PatKind::App(_, Some(pat)) => queue.push_back(*pat),
            _ => {}
        }
    }
    v
}
