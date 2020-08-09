// use crate::types::*;
// use crate::{
//     Datatype, Decl, Expr, ExprId, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord, TypeId,
// };
// use crate::arenas::TypeArena;

// use sml_util::hasher::SymHashMap;
// use sml_util::interner::Symbol;
// use sml_util::pretty_print::PrettyPrinter;
// use sml_util::span::Span;

// pub struct TyCheckCtx<'a> {
//     stack: Vec<Scope<'a>>,
//     arena: TypeArena<'a>,
// }

// #[derive(Default)]
// pub struct Scope<'a> {
//     tyvars: &'a [usize],
//     defs: SymHashMap<&'a Type<'a>>
// }

// pub struct Error<'a> {
//     sp: Span,
//     ty1: &'a Type<'a>,
//     ty2: &'a Type<'a>,
// }

// impl<'a> TyCheckCtx<'a> {

//     fn new(arena: TypeArena<'a>) -> TyCheckCtx<'a> {
//         TyCheckCtx {
//             stack: vec![Scope::default()],
//             arena
//         }
//     }

//     fn with_scope<F>(&mut self, tyvars: &'a [usize], f: F)
//         where F: Fn(&TyCheckCtx<'a>)
//     {
//         let scope = Scope {
//             tyvars,
//             ..Scope::default()
//         };
//         self.stack.push(scope);
//         let r = f(self);
//         self.stack.pop();
//         r
//     }

//     fn check_tyvar_scope(&self, id: usize) -> bool {
//         // must always be valid
//         let mut idx = self.stack.len() - 1;
//         while let Some(ptr) = self.stack.get(idx) {
//             if ptr.tyvars.contains(&id) {
//                 return true
//             }
//             idx = idx.saturating_sub(1);
//         }
//         false
//     }

//     fn add(&mut self, sym: Symbol, ty: &'a Type<'a>) {
//         self.stack.last_mut().unwrap().defs.insert(sym, ty);
//     }

//     fn get(&mut self, sym: &Symbol) -> Option<&'a Type<'a>> {
//         self.stack.last()?.defs.get(sym).copied()
//     }

//     pub fn visit_decl(&mut self, decl: &'a Decl<'a>) {
//         match decl {
//             Decl::Val(vars, sym, expr) => {
//                 self.add(*sym, expr.ty);
//                 self.with_scope(&vars, |ctx| ctx.check_expr(&expr))
//             }
//             Decl::Fun(vars, funs) => {
//                 for (sym, lam) in funs {
//                     self.add(*sym, self.arena.arrow(lam.ty, lam.body.ty));
//                 }
//                 self.with_scope(&vars, |ctx| {
//                     for (_, lam) in funs {
//                         self.add(lam.arg, lam.ty);
//                         self.check_expr(&lam.body);
//                     }
//                 })
//             }
//             Decl::Datatype(dts) => {

//             }
//             Decl::Exn(con, ty) => {

//             }
//         }
//     }

//     fn check_type_wf(&mut self, ty: &'a Type<'a>) {
//         match ty {
//             Type::Var(tyvar) => match tyvar.ty() {
//                 Some(ty) => self.check_type_wf(ty),
//                 None => {
//                     if !self.check_tyvar_scope(tyvar.id) {
//                         panic!("BUG: unscoped tyvar");
//                     }
//                 }
//             },
//             Type::Record(fields) => {
//                 for field in fields.iter() {
//                     self.check_type_wf(&field.data);
//                 }
//             }
//             Type::Flex(flex) => match flex.ty() {
//                 Some(ty) => self.check_type_wf(ty),
//                 None => {
//                     // emit warning for unused type variable
//                     eprintln!("BUG: unused flex var");
//                 }
//             },
//             Type::Con(mut con, args) => {
//                 for field in args.iter() {
//                     self.check_type_wf(&field);
//                 }
//             }
//         }
//     }

//     fn check_expr(&mut self, expr: &Expr<'a>) -> &'a Type<'a> {
//         let ty = self.check_type_wf(expr.ty);
//         let kind = match expr.kind {
//             ExprKind::App(e1, e2) => {
//                 let e1 = self.check_expr(e1);
//                 let e2 = self.check_expr(e2);
//                 match e1.de_arrow() {
//                     Some((ty1, ty2)) => {
//                         if ty1 != e2 {
//                             return ty2
//                         } else {
//                             panic!("")
//                         }
//                     }
//                     _ => panic!("")
//                 }
//             }
//             ExprKind::Case(casee, rules) => {
//                 let (var, ty) = casee;
//                 self.check_type_wf(ty);
//                 let res_ty = expr.ty;
//                 for rule in rules {
//                     if &rule.pat.ty != ty {
//                         panic!("BUG: pattern type and case type mismatch")
//                     }
//                     if rule.expr.ty != res_ty {
//                         panic!("BUG: pattern return type mismatch")
//                     }
//                 }
//                 res_ty
//             }
//             ExprKind::Con(mut con, tys) => {
//                 for ty in tys.iter() {
//                     self.check_type_wf(ty)
//                 }
//                 expr.ty
//             }
//             ExprKind::Const(c) => expr.ty,
//             ExprKind::Handle(tryy, sym, handler) => {
//                 let tryy = self.check_expr(tryy);
//                 let handler = self.check_expr(handler);
//                 match handler.de_arrow() {
//                     Some((ty1, ty2)) => {
//                         if ty1 != self.arena.exn() && ty2 != tryy {
//                             panic!("BUG: misformed handler")
//                         }
//                      }
//                     _ => panic!()
//                 };
//                 tryy
//             }
//             ExprKind::Lambda(lam) => {
//                 self.check_type_wf(lam.ty);
//                 self.check_expr(&lam.body)

//             }
//             ExprKind::Let(decls, body) => {
//                 // Remove redundant let expressions
//                 // if decls.len() == 1 {
//                 //     match decls.first() {
//                 //         Some(Decl::Val(_, Rule { pat, expr })) if pat.equals_expr(&body) => {
//                 //             return self.check_expr(&expr)
//                 //         }
//                 //         _ => {}
//                 //     }
//                 // }
//                 self.enter();
//                 let decls = decls
//                     .iter()
//                     .map(|d| self.visit_decl(d))
//                     .collect::<Vec<_>>();
//                 let body = self.check_expr(body);
//                 self.leave();
//                 ExprKind::Let(decls, body)
//             }
//             ExprKind::List(exprs) => {
//                 ExprKind::List(exprs.iter().map(|e| self.check_expr(e)).collect())
//             }
//             ExprKind::Primitive(sym) => ExprKind::Primitive(*sym),
//             ExprKind::Raise(e) => ExprKind::Raise(self.check_expr(e)),
//             ExprKind::Record(rows) => ExprKind::Record(
//                 rows.iter()
//                     .map(|row| row.fmap(|ex| self.check_expr(ex)))
//                     .collect(),
//             ),
//             ExprKind::Seq(exprs) => {
//                 for
//             }
//             ExprKind::Var(s, tys) => {

//             }
//         };
//     }
// }
