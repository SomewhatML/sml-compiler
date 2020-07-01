use super::*;

/// Note that this can only be called once!
fn bind(sp: Span, var: &TypeVar, ty: &Type) -> Result<(), Diagnostic> {
    if let Type::Var(v2) = ty {
        if v2 == var {
            return Ok(());
        }
    }
    if ty.occurs_check(var) {
        return Err(Diagnostic::error(
            sp,
            format!("Cyclic type detected: {:?}", ty),
        ));
    }

    var.data.set(ty.clone()).unwrap();
    Ok(())
}

impl Context {
    pub fn unify(&self, sp: Span, a: &Type, b: &Type) -> Result<(), Diagnostic> {
        // println!("unify [{:?}] [{:?}]", a, b);
        match (a, b) {
            (Type::Var(a1), Type::Var(b1)) => match (a1.ty(), b1.ty()) {
                (Some(a), Some(b)) => self.unify(sp, a, b),
                (Some(a), None) => self.unify(sp, a, b),
                (None, Some(b)) => self.unify(sp, a, b),
                (None, None) => bind(sp, a1, b),
            },
            (Type::Var(a), b) => match a.ty() {
                Some(ty) => self.unify(sp, ty, b),
                None => bind(sp, a, b),
            },
            (a, Type::Var(b)) => match b.ty() {
                Some(ty) => self.unify(sp, a, ty),
                None => bind(sp, b, a),
            },
            (Type::Con(a, a_args), Type::Con(b, b_args)) => {
                if a != b {
                    Err(Diagnostic::error(
                        sp,
                        format!(
                            "Can't unify type constructors {:?} and {:?}",
                            a.name, b.name
                        ),
                    ))
                } else if a_args.len() != b_args.len() {
                    Err(Diagnostic::error(
                        sp,
                        "Can't unify type constructors with different argument lengths",
                    )
                    .message(sp, format!("{:?} has arguments: {:?}", a, a_args))
                    .message(sp, format!("and {:?} has arguments: {:?}", b, b_args)))
                } else {
                    for (c, d) in a_args.into_iter().zip(b_args) {
                        self.unify(sp, c, d)?;
                    }
                    Ok(())
                }
            }
            (Type::Record(r1), Type::Record(r2)) => {
                let mut r1 = r1.clone();
                let mut r2 = r2.clone();
                r1.sort_by(|a, b| a.label.cmp(&b.label));
                r2.sort_by(|a, b| a.label.cmp(&b.label));

                for (ra, rb) in r1.into_iter().zip(r2.into_iter()) {
                    if ra.label != rb.label {
                        return Err(Diagnostic::error(sp, "Can't unify record types")
                            .message(ra.span, format!("label '{:?}' from type {:?}", ra.label, a))
                            .message(
                                rb.span,
                                format!("doesn't match label '{:?}' from type {:?}", rb.label, b),
                            ));
                    }
                    self.unify(sp, &ra.data, &rb.data).map_err(|diag| {
                        diag.message(
                            ra.span,
                            format!("field '{:?}' has type {:?}", ra.label, ra.data),
                        )
                        .message(
                            rb.span,
                            format!("field '{:?}' has type {:?}", rb.label, rb.data),
                        )
                    })?;
                }

                Ok(())
            }
            (a, b) => Err(Diagnostic::error(
                sp,
                format!("Can't unify types {:?} and {:?}", a, b),
            )),
        }
    }

    pub fn unify_list(&self, sp: Span, tys: &[Type]) -> Result<(), Diagnostic> {
        let fst = &tys[0];
        for ty in tys {
            self.unify(sp, ty, fst)?;
        }
        Ok(())
    }

    pub fn unify_list_ref(&self, sp: Span, tys: &[&Type]) -> Result<(), Diagnostic> {
        let fst = &tys[0];
        for ty in tys {
            self.unify(sp, ty, fst)?;
        }
        Ok(())
    }

    fn bound_ty_slow(&self) -> HashSet<usize> {
        let mut set = HashSet::new();
        for ns in self.namespace_iter() {
            for (sym, id) in &ns.values {
                let (sch, _) = &self[*id];
                // println!("bound: {:?} {:?}", sym, sch);
                let var = match sch {
                    Scheme::Mono(ty) => ty.ftv_no_rank(),
                    Scheme::Poly(_, ty) => ty.ftv_no_rank(),
                };
                set.extend(var);
            }
        }
        set
    }

    pub fn generalize(&self, ty: Type) -> Scheme {
        // let ftv = ty.ftv(self.tyvar_rank);
        let bound = self.bound_ty_slow();
        let ftv = ty
            .ftv_no_rank()
            .drain(..)
            .filter(|x| !bound.contains(x))
            .collect::<Vec<usize>>();
        match ftv.len() {
            0 => Scheme::Mono(ty),
            _ => Scheme::Poly(ftv, ty),
        }
    }

    pub fn instantiate(&self, scheme: Scheme) -> Type {
        match scheme {
            Scheme::Mono(ty) => ty,
            Scheme::Poly(vars, ty) => {
                let map = vars
                    .into_iter()
                    .map(|v| (v, Type::Var(self.fresh_tyvar())))
                    .collect();
                ty.apply(&map)
            }
        }
    }

    pub fn check_type_names(&self, sp: Span, ty: &Type) -> Result<(), Diagnostic> {
        let mut names = Vec::new();
        ty.visit(|f| match f {
            Type::Con(tc, _) => names.push(*tc),
            _ => {}
        });

        for tycon in names {
            if self.lookup_type(&tycon.name).is_none() {
                return Err(Diagnostic::error(
                    sp,
                    format!("type {:?} escapes inner scope!", tycon.name),
                ));
            }
        }
        Ok(())
    }

    pub fn elaborate_type(
        &mut self,
        ty: &ast::Type,
        allow_unbound: bool,
    ) -> Result<Type, Diagnostic> {
        use ast::TypeKind::*;
        match &ty.data {
            Var(s) => match self.lookup_tyvar(s, allow_unbound) {
                Some(tv) => Ok(Type::Var(tv)),
                None => Err(Diagnostic::error(
                    ty.span,
                    format!("unbound type variable {:?}", s),
                )),
            },
            Con(s, args) => {
                let args = args
                    .iter()
                    .map(|ty| self.elaborate_type(&ty, allow_unbound))
                    .collect::<Result<Vec<Type>, _>>()?;
                let con = self.lookup_type(s).ok_or_else(|| {
                    Diagnostic::error(ty.span, format!("unbound type variable {:?}", s))
                })?;
                if con.arity() != args.len() {
                    Err(Diagnostic::error(
                        ty.span,
                        format!(
                            "type constructor requires {} arguments, but {} are supplied",
                            con.arity(),
                            args.len()
                        ),
                    )
                    .message(ty.span, format!("in type {:?}", ty)))
                } else {
                    Ok(con.apply(args))
                }
            }
            Record(rows) => rows
                .into_iter()
                .map(|row| self.elab_row(|f, r| f.elaborate_type(r, allow_unbound), row))
                .collect::<Result<Vec<Row<Type>>, _>>()
                .map(Type::Record),
        }
    }
}
