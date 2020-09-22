use super::*;
use types::Type;

pub trait Visitor<'a>: Sized {
    fn visit_decl(&mut self, decl: &Decl<'a>) -> Decl<'a> {
        self.walk_decl(decl)
    }
    fn visit_expr(&mut self, _: &Expr<'a>) -> Expr<'a>;
    fn visit_type(&mut self, _: &Type<'a>) -> &'a Type<'a>;
    fn visit_pat(&mut self, _: &Pat<'a>) -> Pat<'a>;

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

    fn visit_decl_val(&mut self, vars: &[usize], sym: &Symbol, expr: &Expr<'a>) -> Decl<'a> {
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
            body: self.visit_expr(&lambda.body),
        }
    }

    fn walk_decl(&mut self, decl: &Decl<'a>) -> Decl<'a> {
        match decl {
            Decl::Val(vars, sym, expr) => self.visit_decl_val(vars, sym, expr),
            Decl::Fun(vars, funs) => self.visit_decl_fun(vars, funs),
            Decl::Datatype(dts) => self.visit_decl_dt(dts),
            Decl::Exn(con, arg) => self.visit_decl_exn(*con, *arg),
        }
    }
}
