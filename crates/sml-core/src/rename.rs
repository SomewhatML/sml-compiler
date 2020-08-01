use super::*;
use std::collections::HashMap;
use ExprKind::*;

// pub fn rename<'a>(expr: Expr<'a>, map: &mut HashMap<Symbol, Symbol>) {
//     match expr.expr {
//         App(a, b) => {
//             rename(a, map);
//             rename(b, map);
//         }
//         Case(mut a, mut rules) => {
//             rename(&mut a, map);
//             for Rule { expr, ..} in rules.iter_mut() {
//                 rename(expr, map);
//             }
//         }
//         Con(_, _) => {},
//         Const(_) => {},
//         Handle(mut a, mut rules) => {
//             rename(&mut a, map);
//             for Rule { expr, ..} in rules.iter_mut() {
//                 rename(expr, map);
//             }
//         }
//         Lambda(mut lam) => {
//             let entry = map.remove_entry(&lam.arg);
//             rename(&mut lam.body, map);
//             if let Some((k, v)) = entry {
//                 map.insert(k, v);
//             }
//         }
//         Let(decls, mut expr) => {
//             rename(&mut expr, map);
//         }
//         List(mut exprs) => {
//             for ex in exprs.iter_mut() {
//                 rename(ex, map);
//             }
//         }
//         Primitive(_) => {},
//         Raise(mut ex) => rename(&mut ex, map),
//         Record(mut fields) => {
//             for f in fields.rows.iter_mut() {
//                 rename(&mut f.data, map);
//             }
//         }
//         Seq(mut exprs) => {
//             for ex in exprs.iter_mut() {
//                 rename(ex, map);
//             }
//         },
//         Var(Symbol) => {

//         }
//     }

// }
