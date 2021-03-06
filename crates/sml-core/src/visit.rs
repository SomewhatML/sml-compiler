use super::*;
use types::Type;

pub trait Visitor<'a>: Sized {
    fn arena(&self) -> &'a crate::arenas::CoreArena<'a>;

    fn visit_decl(&mut self, decl: &Decl<'a>) -> Decl<'a> {
        self.walk_decl(decl)
    }
    fn visit_expr(&mut self, expr: Expr<'a>) -> Expr<'a> {
        self.walk_expr(expr)
    }
    fn visit_type(&mut self, _: &'a Type<'a>) -> &'a Type<'a>;

    fn visit_pat(&mut self, pat: Pat<'a>) -> Pat<'a> {
        self.walk_pat(pat)
    }

    fn visit_vars(&mut self, vars: &[usize]) -> Vec<usize> {
        vars.into()
    }

    fn visit_sym(&mut self, sym: &Symbol) -> Symbol {
        *sym
    }

    fn visit_con(&mut self, con: Constructor) -> Constructor {
        Constructor {
            name: self.visit_sym(&con.name),
            tycon: self.visit_sym(&con.tycon),
            ..con
        }
    }

    fn visit_decl_val(&mut self, vars: &[usize], sym: &Symbol, expr: Expr<'a>) -> Decl<'a> {
        Decl::Val(
            self.visit_vars(vars),
            self.visit_sym(sym),
            self.visit_expr(expr),
        )
    }

    fn visit_decl_fun(&mut self, vars: &[usize], funs: &[(Symbol, Lambda<'a>)]) -> Decl<'a> {
        let vars = self.visit_vars(vars);
        let mut funs_ = Vec::new();
        for (name, lambda) in funs {
            funs_.push((self.visit_sym(name), self.visit_lambda(lambda)));
        }
        Decl::Fun(vars, funs_)
    }

    fn visit_decl_dt(&mut self, dts: &[Datatype<'a>]) -> Decl<'a> {
        let mut dts_ = Vec::new();
        for dt in dts {
            dts_.push(Datatype {
                tycon: Tycon {
                    name: self.visit_sym(&dt.tycon.name),
                    arity: dt.tycon.arity,
                    scope_depth: dt.tycon.scope_depth,
                },
                tyvars: self.visit_vars(&dt.tyvars),
                constructors: dt
                    .constructors
                    .iter()
                    .map(|(con, ty)| (self.visit_con(*con), ty.map(|ty| self.visit_type(ty))))
                    .collect(),
            });
        }
        Decl::Datatype(dts_)
    }

    fn visit_decl_exn(&mut self, con: Constructor, arg: Option<&'a Type<'a>>) -> Decl<'a> {
        Decl::Exn(self.visit_con(con), arg.map(|ty| self.visit_type(ty)))
    }

    fn visit_lambda(&mut self, lambda: &Lambda<'a>) -> Lambda<'a> {
        Lambda {
            arg: self.visit_sym(&lambda.arg),
            ty: self.visit_type(&lambda.ty),
            body: self.visit_expr(lambda.body),
        }
    }

    fn walk_decl(&mut self, decl: &Decl<'a>) -> Decl<'a> {
        match decl {
            Decl::Val(vars, sym, expr) => self.visit_decl_val(vars, sym, *expr),
            Decl::Fun(vars, funs) => self.visit_decl_fun(vars, funs),
            Decl::Datatype(dts) => self.visit_decl_dt(dts),
            Decl::Exn(con, arg) => self.visit_decl_exn(*con, *arg),
        }
    }

    fn visit_rule(&mut self, rule: Rule<'a>) -> Rule<'a> {
        Rule {
            pat: self.visit_pat(rule.pat),
            expr: self.visit_expr(rule.expr),
        }
    }

    fn visit_pat_app(&mut self, con: Constructor, arg: Option<Pat<'a>>) -> PatKind<'a> {
        PatKind::App(self.visit_con(con), arg.map(|p| self.visit_pat(p)))
    }

    fn visit_pat_record(&mut self, record: &SortedRecord<Pat<'a>>) -> PatKind<'a> {
        PatKind::Record(record.fmap(|pat| self.visit_pat(*pat)))
    }

    fn visit_pat_var(&mut self, var: &Symbol) -> PatKind<'a> {
        PatKind::Var(self.visit_sym(var))
    }

    fn walk_pat(&mut self, pat: Pat<'a>) -> Pat<'a> {
        let ty = self.visit_type(pat.ty);
        let kind = match pat.kind {
            PatKind::App(con, arg) => self.visit_pat_app(*con, *arg),
            PatKind::Const(c) => PatKind::Const(*c),
            PatKind::Record(record) => self.visit_pat_record(record),
            PatKind::Var(s) => self.visit_pat_var(s),
            PatKind::Wild => PatKind::Wild,
        };

        Pat::new(self.arena().pats.alloc(kind), ty, pat.span)
    }

    fn visit_expr_app(&mut self, a: Expr<'a>, b: Expr<'a>) -> ExprKind<'a> {
        ExprKind::App(self.visit_expr(a), self.visit_expr(b))
    }

    fn visit_expr_case(&mut self, scrutinee: Var<'a>, rules: &[Rule<'a>]) -> ExprKind<'a> {
        let rules = rules
            .into_iter()
            .map(|Rule { pat, expr }| Rule {
                pat: self.visit_pat(*pat),
                expr: self.visit_expr(*expr),
            })
            .collect();
        ExprKind::Case(
            (self.visit_sym(&scrutinee.0), self.visit_type(scrutinee.1)),
            rules,
        )
    }

    fn visit_expr_con(&mut self, con: Constructor, targs: &[&'a Type<'a>]) -> ExprKind<'a> {
        ExprKind::Con(
            self.visit_con(con),
            targs.into_iter().map(|ty| self.visit_type(*ty)).collect(),
        )
    }

    fn visit_expr_const(&mut self, c: Const) -> ExprKind<'a> {
        ExprKind::Const(c)
    }

    fn visit_expr_handle(
        &mut self,
        expr: Expr<'a>,
        sym: &Symbol,
        handle: Expr<'a>,
    ) -> ExprKind<'a> {
        ExprKind::Handle(
            self.visit_expr(expr),
            self.visit_sym(sym),
            self.visit_expr(handle),
        )
    }

    fn visit_expr_lambda(&mut self, lambda: Lambda<'a>) -> ExprKind<'a> {
        ExprKind::Lambda(Lambda {
            arg: self.visit_sym(&lambda.arg),
            ty: self.visit_type(lambda.ty),
            body: self.visit_expr(lambda.body),
        })
    }

    fn visit_expr_let(&mut self, decls: &[Decl<'a>], body: Expr<'a>) -> ExprKind<'a> {
        ExprKind::Let(
            decls.into_iter().map(|d| self.visit_decl(d)).collect(),
            self.visit_expr(body),
        )
    }

    fn visit_expr_list(&mut self, list: &[Expr<'a>]) -> ExprKind<'a> {
        ExprKind::List(list.into_iter().map(|ex| self.visit_expr(*ex)).collect())
    }

    fn visit_expr_primitive(&mut self, prim: Symbol) -> ExprKind<'a> {
        ExprKind::Primitive(prim)
    }

    fn visit_expr_raise(&mut self, expr: Expr<'a>) -> ExprKind<'a> {
        ExprKind::Raise(self.visit_expr(expr))
    }

    fn visit_expr_record(&mut self, fields: &[Row<Expr<'a>>]) -> ExprKind<'a> {
        ExprKind::Record(
            fields
                .into_iter()
                .map(|row| Row {
                    label: row.label,
                    data: self.visit_expr(row.data),
                    span: row.span,
                })
                .collect(),
        )
    }

    fn visit_expr_selector(&mut self, expr: Expr<'a>, sym: Symbol) -> ExprKind<'a> {
        ExprKind::Selector(self.visit_expr(expr), sym)
    }

    fn visit_expr_seq(&mut self, seq: &[Expr<'a>]) -> ExprKind<'a> {
        ExprKind::Seq(seq.into_iter().map(|ex| self.visit_expr(*ex)).collect())
    }

    fn visit_expr_var(&mut self, sym: Symbol, targs: &[&'a Type<'a>]) -> ExprKind<'a> {
        ExprKind::Var(
            self.visit_sym(&sym),
            targs.into_iter().map(|ty| self.visit_type(*ty)).collect(),
        )
    }

    fn walk_expr(&mut self, expr: Expr<'a>) -> Expr<'a> {
        let ty = self.visit_type(expr.ty);
        let kind = match expr.kind {
            ExprKind::App(a, b) => self.visit_expr_app(*a, *b),
            ExprKind::Case(scrutinee, rules) => self.visit_expr_case(*scrutinee, rules),
            ExprKind::Con(con, targs) => self.visit_expr_con(*con, targs),
            ExprKind::Const(c) => self.visit_expr_const(*c),
            ExprKind::Handle(expr, sym, handle) => self.visit_expr_handle(*expr, sym, *handle),
            ExprKind::Lambda(lambda) => self.visit_expr_lambda(*lambda),
            ExprKind::Let(decls, body) => self.visit_expr_let(decls, *body),
            ExprKind::List(list) => self.visit_expr_list(list),
            ExprKind::Primitive(prim) => self.visit_expr_primitive(*prim),
            ExprKind::Raise(expr) => self.visit_expr_raise(*expr),
            ExprKind::Record(fields) => self.visit_expr_record(fields),
            ExprKind::Selector(expr, sym) => self.visit_expr_selector(*expr, *sym),
            ExprKind::Seq(seq) => self.visit_expr_seq(seq),
            ExprKind::Var(var, targs) => self.visit_expr_var(*var, targs),
        };
        Expr::new(self.arena().exprs.alloc(kind), ty, expr.span)
    }
}
