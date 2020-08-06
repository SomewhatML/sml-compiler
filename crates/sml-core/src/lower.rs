#![allow(unused_imports)]
#![allow(dead_code)]
#![allow(unused_variables)]
use crate::arenas::{CoreArena, TypeArena};
use crate::builtin::{constructors, tycons};
use crate::types::{Constructor, Flex, Scheme, Tycon, Type, TypeVar};
use crate::{
    Datatype, Decl, Expr, ExprId, ExprKind, Lambda, Pat, PatKind, Row, Rule, SortedRecord, TypeId,
};
use sml_util::interner::Symbol;

use ir::Var;
use sml_ir as ir;

pub struct LoweringCtx {}

impl LoweringCtx {
    fn lower_sym(&mut self, sym: &Symbol) -> Symbol {
        todo!()
    }

    fn lower_constructor(&mut self, con: Constructor) -> ir::Constructor {
        ir::Constructor {
            name: self.lower_sym(&con.name),
            tycon: self.lower_tycon(&con.tycon),
            tag: con.tag,
        }
    }

    fn lower_ty(&mut self, ty: &Type<'_>) -> ir::Type {
        match ty {
            Type::Var(tyvar) => match tyvar.ty() {
                Some(ty) => self.lower_ty(ty),
                None => self.lower_tyvar(tyvar.id),
            },
            Type::Record(fields) => {
                let args = fields.iter().map(|ty| self.lower_ty(ty.data)).collect();
                ir::Type::Con(ir::Tycon::Tuple, args)
            }
            Type::Flex(flex) => match flex.ty() {
                Some(ty) => self.lower_ty(ty),
                None => {
                    // This should likely be an error, flexible type never instantiated
                    ir::Type::Con(ir::Tycon::Unit, vec![])
                }
            },
            Type::Con(con, args) => ir::Type::Con(
                self.lower_tycon(&con.name),
                args.iter().map(|ty| self.lower_ty(ty)).collect(),
            ),
        }
    }

    fn lower_tyvar(&mut self, tyvar: usize) -> ir::Type {
        ir::Type::Var(tyvar)
    }

    fn lower_tycon(&mut self, tycon: &Symbol) -> ir::Tycon {
        match tycon {
            &sml_util::interner::S_ARROW => ir::Tycon::Arrow,
            &sml_util::interner::S_UNIT => ir::Tycon::Unit,
            &sml_util::interner::S_CHAR => ir::Tycon::Char,
            &sml_util::interner::S_INT => ir::Tycon::Int,
            &sml_util::interner::S_STRING => ir::Tycon::String,
            &sml_util::interner::S_REF => ir::Tycon::Ref,
            &sml_util::interner::S_LIST => ir::Tycon::List,
            &sml_util::interner::S_BOOL => ir::Tycon::Bool,
            &sml_util::interner::S_EXN => ir::Tycon::Exn,
            _ => ir::Tycon::Datatype(*tycon),
        }
    }

    fn lower_expr(&mut self, expr: &Expr<'_>) -> ir::Block {
        let ty = self.lower_ty(expr.ty);
        match &expr.kind {
            ExprKind::App(e1, e2) => {
                let b1 = self.lower_expr(e1);
                let b2 = self.lower_expr(e2);
                todo!()
            }
            ExprKind::Case(e1, rules) => todo!(),
            ExprKind::Con(con, tys) => todo!(),
            ExprKind::Const(con) => todo!(),
            ExprKind::Handle(e1, sym, e2) => todo!(),
            ExprKind::Lambda(lam) => todo!(),
            ExprKind::Let(decls, e1) => todo!(),
            ExprKind::List(exs) => todo!(),
            ExprKind::Primitive(sym) => todo!(),
            ExprKind::Raise(e1) => todo!(),
            ExprKind::Record(rows) => todo!(),
            ExprKind::Seq(exs) => todo!(),
            ExprKind::Var(sym) => {
                ir::Expr::Var(Var(self.lower_sym(sym), self.lower_ty(expr.ty)));
                todo!()
            }
        }
    }
}
