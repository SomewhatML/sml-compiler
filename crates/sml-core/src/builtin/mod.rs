pub mod constructors;
pub mod tycons;

use super::*;
use crate::elaborate::*;

fn define_constructor<'arena>(
    ctx: &mut elaborate::Context<'arena>,
    con: Constructor,
    sch: Scheme<'arena>,
) {
    ctx.define_value(con.name, sch, IdStatus::Con(con));
}

/// This is not pretty, but we have to handle builtins for elaboration somehow
pub fn populate_context<'arena>(ctx: &mut elaborate::Context<'arena>) {
    /// Build the initial type environment
    for tc in &tycons::T_BUILTINS {
        ctx.define_type(tc.name, TypeStructure::Tycon(*tc));
    }

    let nil = ctx.arena.types.fresh_var();

    define_constructor(
        ctx,
        constructors::C_NIL,
        Scheme::Poly(vec![nil.as_tyvar().id], ctx.arena.types.list(nil)),
    );

    let cons = ctx.arena.types.fresh_var();

    // The inner types of cons: 'a * 'a list
    let crec = ctx.arena.types.alloc(Type::Record(vec![
        Row {
            label: Symbol::tuple_field(1),
            data: cons,
            span: Span::dummy(),
        },
        Row {
            label: Symbol::tuple_field(2),
            data: ctx.arena.types.list(cons),
            span: Span::dummy(),
        },
    ]));

    define_constructor(
        ctx,
        constructors::C_CONS,
        Scheme::Poly(
            vec![cons.as_tyvar().id],
            ctx.arena.types.arrow(crec, ctx.arena.types.list(cons)),
        ),
    );

    define_constructor(
        ctx,
        constructors::C_TRUE,
        Scheme::Mono(ctx.arena.types.bool()),
    );

    define_constructor(
        ctx,
        constructors::C_FALSE,
        Scheme::Mono(ctx.arena.types.bool()),
    );

    let reff = ctx.arena.types.fresh_var();
    define_constructor(
        ctx,
        constructors::C_REF,
        Scheme::Poly(
            vec![reff.as_tyvar().id],
            ctx.arena.types.arrow(reff, ctx.arena.types.reff(reff)),
        ),
    );
}
