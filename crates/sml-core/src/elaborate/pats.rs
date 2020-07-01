use super::*;

pub struct Binding {
    pub var: Symbol,
    pub tv: TypeVar,
}

impl Context {
    pub fn elaborate_pat(&mut self, pat: &ast::Pat, bind: bool) -> (Pat, Vec<Binding>) {
        let mut bindings = Vec::new();
        (self.elaborate_pat_inner(pat, bind, &mut bindings), bindings)
    }

    pub(crate) fn elaborate_pat_inner(
        &mut self,
        pat: &ast::Pat,
        bind: bool,
        bindings: &mut Vec<Binding>,
    ) -> Pat {
        use ast::PatKind::*;
        match &pat.data {
            App(con, p) => {
                let p = self.elaborate_pat_inner(p, bind, bindings);
                match self.lookup_value(con).cloned() {
                    Some((scheme, IdStatus::Con(constr))) => {
                        // TODO: Scheme instantiation
                        let inst = self.instantiate(scheme);

                        // let (arg, res) = inst.de_arrow().ok_or_else(|| {
                        //     Diagnostic::error(pat.span, "constant constructor applied to pattern")
                        //         .message(p.span, format!("constructor: {:?} ", con))
                        // })?;

                        let arr = Type::arrow(
                            Type::Var(self.fresh_tyvar()),
                            Type::Var(self.fresh_tyvar()),
                        );
                        let (arg, res) = match inst.de_arrow() {
                            Some((a, r)) => (a, r),
                            None => {
                                self.unify(pat.span, &inst, &arr);
                                arr.de_arrow().unwrap()
                            }
                        };

                        self.unify(pat.span, arg, &p.ty);
                        Pat::new(
                            PatKind::App(constr, Some(Box::new(p))),
                            res.clone(),
                            pat.span,
                        )
                    }
                    _ => {
                        self.diags.push(Diagnostic::error(
                            pat.span,
                            format!("Non-constructor {:?} applied to pattern {:?}", con, p),
                        ));
                        Pat::new(PatKind::Wild, Type::Var(self.fresh_tyvar()), pat.span)
                    }
                }
            }
            Ascribe(p, ty) => {
                let p = self.elaborate_pat_inner(p, bind, bindings);
                let ty = self.elaborate_type(ty, true);
                self.unify(pat.span, &p.ty, &ty);
                p
            }
            Const(c) => {
                let ty = self.const_ty(c);
                Pat::new(PatKind::Const(*c), ty, pat.span)
            }
            FlatApp(pats) => {
                let p = match self.pat_precedence(pats.clone()) {
                    Ok(p) => p,
                    Err(err) => {
                        match err {
                            precedence::Error::EndsInfix => self.diags.push(Diagnostic::error(
                                pat.span,
                                "application pattern ends with an infix operator",
                            )),
                            precedence::Error::InfixInPrefix => self.diags.push(Diagnostic::error(
                                pat.span,
                                "application pattern starts with an infix operator",
                            )),
                            precedence::Error::SamePrecedence => {
                                self.diags.push(Diagnostic::error(
                                    pat.span,
                                    "application pattern mixes operators of equal precedence",
                                ))
                            }
                            precedence::Error::InvalidOperator => {
                                self.diags.push(Diagnostic::error(
                                    pat.span,
                                    "application pattern doesn't contain infix operator",
                                ))
                            }
                        }
                        let (fst, start) = match &pats[0].data {
                            ast::PatKind::Variable(s) => (*s, 1),
                            _ => (self.fresh_var(), 0),
                        };
                        // attempt error recovery
                        ast::Pat::new(
                            ast::PatKind::App(
                                fst,
                                Box::new(ast::Pat::new(
                                    ast::PatKind::List(pats[start..].into()),
                                    pat.span,
                                )),
                            ),
                            pat.span,
                        )
                    }
                };
                self.elaborate_pat_inner(&p, bind, bindings)
            }
            List(pats) => {
                let pats: Vec<Pat> = pats
                    .into_iter()
                    .map(|p| self.elaborate_pat_inner(p, bind, bindings))
                    .collect::<Vec<Pat>>();

                let tys = pats.iter().map(|p| &p.ty).collect::<Vec<&Type>>();
                self.unify_list_ref(pat.span, &tys);

                let ty = tys[0].clone();

                Pat::new(PatKind::List(pats), Type::Con(T_LIST, vec![ty]), pat.span)
            }
            Record(rows) => {
                let pats: Vec<Row<Pat>> = rows
                    .into_iter()
                    .map(|r| self.elab_row(|f, rho| f.elaborate_pat_inner(rho, bind, bindings), r))
                    .collect::<Vec<_>>();

                let tys = pats
                    .iter()
                    .map(|p| Row {
                        label: p.label,
                        span: p.span,
                        data: p.data.ty.clone(),
                    })
                    .collect::<Vec<Row<Type>>>();

                Pat::new(PatKind::Record(pats), Type::Record(tys), pat.span)
            }
            Variable(sym) => match self.lookup_value(sym).cloned() {
                // Rule 35
                Some((scheme, IdStatus::Exn(c))) | Some((scheme, IdStatus::Con(c))) => {
                    let ty = self.instantiate(scheme.clone());
                    Pat::new(PatKind::App(c, None), ty, pat.span)
                }
                _ => {
                    // Rule 34
                    let tv = self.fresh_tyvar();
                    if bind {
                        self.define_value(*sym, Scheme::Mono(Type::Var(tv.clone())), IdStatus::Var);
                    }
                    bindings.push(Binding {
                        var: *sym,
                        tv: tv.clone(),
                    });
                    Pat::new(PatKind::Var(*sym), Type::Var(tv), pat.span)
                }
            },
            Wild => Pat::new(PatKind::Wild, Type::Var(self.fresh_tyvar()), pat.span),
        }
    }
}
