use super::*;

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
        let (pat, _) = self.elaborate_pat(&rule.pat, bind)?;
        let expr = self.elaborate_expr(&rule.expr)?;
        Ok(Rule { pat, expr })
    }

    pub fn elab_rules(
        &mut self,
        sp: Span,
        rules: &[ast::Rule],
    ) -> Result<(Vec<Rule>, Type), Diagnostic> {
        self.with_scope(|f| {
            let rules = rules
                .into_iter()
                .map(|r| f.elab_rule(r, true))
                .collect::<Result<Vec<Rule>, _>>()?;

            let mut rtys = rules
                .iter()
                .map(|r| Type::arrow(r.pat.ty.clone(), r.expr.ty.clone()))
                .collect::<Vec<Type>>();

            f.unify_list(sp, &rtys)?;
            let fst = rtys.remove(0);
            Ok((rules, fst))
        })
    }

    pub fn elaborate_expr(&mut self, expr: &ast::Expr) -> Result<Expr, Diagnostic> {
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

                let f = self.fresh_tyvar();
                self.unify(
                    expr.span,
                    &e1.ty,
                    &Type::arrow(e2.ty.clone(), Type::Var(f.clone())),
                )
                .map_err(|diag| {
                    diag.message(e1.span, format!("'{:?}' has type {:?}", e1, e1.ty))
                        .message(e2.span, format!("'{:?}' has type {:?}", e2, e2.ty))
                })?;
                Ok(Expr::new(
                    ExprKind::App(Box::new(e1), Box::new(e2)),
                    Type::Var(f),
                    expr.span,
                ))
            }
            ast::ExprKind::Case(scrutinee, rules) => {
                let casee = self.elaborate_expr(scrutinee)?;

                let (rules, ty) = self.elab_rules(expr.span, rules)?;

                let (arg, res) = ty.de_arrow().ok_or_else(|| {
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
            ast::ExprKind::Constraint(ex, ty) => {
                let ex = self.elaborate_expr(ex)?;
                let ty = self.elaborate_type(ty, false)?;
                self.unify(expr.span, &ex.ty, &ty)?;
                Ok(ex)
            }
            ast::ExprKind::FlatApp(exprs) => {
                let p = match self.expr_precedence(exprs.clone()) {
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
            ast::ExprKind::Fn(rules) => {
                let (rules, ty) = self.elab_rules(expr.span, rules)?;

                let (arg, res) = ty.de_arrow().ok_or_else(|| {
                    Diagnostic::bug(expr.span, "match rules should have arrow type!")
                })?;

                let gensym = self.fresh_var();
                let sym = Expr::new(ExprKind::Var(gensym), arg.clone(), Span::dummy());

                let body = Expr::new(ExprKind::Case(Box::new(sym), rules), res.clone(), expr.span);

                Ok(Expr::new(
                    ExprKind::Lambda(Box::new(Lambda {
                        arg: gensym,
                        ty: arg.clone(),
                        body,
                    })),
                    ty,
                    expr.span,
                ))
            }
            ast::ExprKind::Handle(ex, rules) => {
                let ex = self.elaborate_expr(ex)?;
                let (rules, ty) = self.elab_rules(expr.span, rules)?;

                let (arg, res) = ty.de_arrow().ok_or_else(|| {
                    Diagnostic::bug(expr.span, "match rules should have arrow type!")
                })?;

                self.unify(expr.span, &ex.ty, res)?;
                self.unify(expr.span, arg, &Type::exn())?;

                Ok(Expr::new(
                    ExprKind::Handle(Box::new(ex), rules),
                    res.clone(),
                    expr.span,
                ))
            }
            ast::ExprKind::If(e1, e2, e3) => {
                let e1 = self.elaborate_expr(e1)?;
                let e2 = self.elaborate_expr(e2)?;
                let e3 = self.elaborate_expr(e3)?;
                self.unify(e1.span, &e1.ty, &Type::bool())?;
                self.unify(expr.span, &e2.ty, &e3.ty)?;

                let ty = e2.ty.clone();
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
                    ty,
                    expr.span,
                ))
            }
            ast::ExprKind::Let(decls, body) => {
                let mut elab = Vec::new();
                let body = self.with_scope(|ctx| {
                    for decl in decls {
                        ctx.elaborate_decl_inner(decl, &mut elab)?;
                    }
                    ctx.elaborate_expr(body)
                })?;
                let ty = body.ty.clone();
                self.check_type_names(body.span, &ty)?;
                Ok(Expr::new(
                    ExprKind::Let(elab, Box::new(body)),
                    ty,
                    expr.span,
                ))
            }
            ast::ExprKind::List(exprs) => {
                let exprs = exprs
                    .into_iter()
                    .map(|ex| self.elaborate_expr(ex))
                    .collect::<Result<Vec<_>, _>>()?;
                let tys = exprs.iter().map(|ex| &ex.ty).collect::<Vec<&Type>>();
                self.unify_list_ref(expr.span, &tys)?;
                let ty = Type::Con(builtin::tycons::T_LIST, vec![tys[0].clone()]);
                Ok(Expr::new(ExprKind::List(exprs), ty, expr.span))
            }
            ast::ExprKind::Orelse(e1, e2) => {
                let e1 = self.elaborate_expr(e1)?;
                let e2 = self.elaborate_expr(e2)?;
                self.unify(e1.span, &e1.ty, &Type::bool())?;
                self.unify(e2.span, &e2.ty, &Type::bool())?;

                let tru = Expr::new(ExprKind::Con(C_TRUE, vec![]), Type::bool(), expr.span);
                self.elab_if(expr.span, e1, tru, e2)
            }
            ast::ExprKind::Primitive(prim) => {
                let name = prim.sym;
                let ty = self.elaborate_type(&prim.ty, false)?;

                Ok(Expr::new(ExprKind::Primitive(name), ty, expr.span))
            }
            ast::ExprKind::Raise(expr) => {
                let ty = Type::Var(self.fresh_tyvar());
                let ex = self.elaborate_expr(expr)?;
                self.unify(expr.span, &ex.ty, &Type::exn())?;
                Ok(Expr::new(ExprKind::Raise(Box::new(ex)), ty, expr.span))
            }
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
            ast::ExprKind::Selector(s) => {
                let row = ast::Row {
                    label: *s,
                    data: ast::Pat::new(ast::PatKind::Variable(*s), Span::dummy()),
                    span: Span::dummy(),
                };
                let pat = ast::Pat::new(ast::PatKind::Record(vec![row]), Span::dummy());
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
                    .into_iter()
                    .map(|ex| self.elaborate_expr(ex))
                    .collect::<Result<Vec<_>, _>>()?;
                // exprs.len() >= 2, but we'll use saturating_sub just to be safe
                for ex in &exprs[..exprs.len().saturating_sub(2)] {
                    self.unify(ex.span, &ex.ty, &Type::unit())?;
                }
                let ty = exprs.last().unwrap().ty.clone();
                Ok(Expr::new(ExprKind::Seq(exprs), ty, expr.span))
            }
            ast::ExprKind::Var(sym) => match self.lookup_value(sym) {
                Some((scheme, _)) => {
                    let ty = self.instantiate(scheme.clone());
                    // println!("inst {:?} [{:?}] -> {:?}", sym, scheme, ty);
                    Ok(Expr::new(ExprKind::Var(*sym), ty, expr.span))
                }
                None => Err(Diagnostic::error(
                    expr.span,
                    format!("unbound variable {:?}", sym),
                )),
            },
            _ => Err(Diagnostic::error(
                expr.span,
                format!("unknown expr {:?}", expr),
            )),
        }
    }
}
