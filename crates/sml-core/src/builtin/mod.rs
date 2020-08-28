pub mod constructors;
pub mod tycons;

use super::*;
use crate::elaborate::*;

fn define_constructor<'arena>(
    ctx: &mut elaborate::Context<'arena>,
    con: Constructor,
    sch: Scheme<'arena>,
) {
    ctx.define_value(con.name, Span::dummy(), sch, IdStatus::Con(con));
}

/// This is not pretty, but we have to handle builtins for elaboration somehow
pub fn populate_context<'arena>(ctx: &mut elaborate::Context<'arena>) {
    // Build the initial type environment
    for tc in &tycons::T_BUILTINS {
        ctx.define_type(tc.name, TypeStructure::Tycon(*tc));
    }

    let list = ctx.arena.types.fresh_var(0);

    define_constructor(
        ctx,
        constructors::C_NIL,
        Scheme::Poly(vec![list.as_tyvar().id], ctx.arena.types.list(list)),
    );

    // The inner types of cons: 'a * 'a list
    let inner = ctx
        .arena
        .types
        .tuple(vec![list, ctx.arena.types.list(list)]);

    define_constructor(
        ctx,
        constructors::C_CONS,
        Scheme::Poly(
            vec![list.as_tyvar().id],
            ctx.arena.types.arrow(inner, ctx.arena.types.list(list)),
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

    define_constructor(
        ctx,
        constructors::C_BIND,
        Scheme::Mono(ctx.arena.types.exn()),
    );

    define_constructor(
        ctx,
        constructors::C_MATCH,
        Scheme::Mono(ctx.arena.types.exn()),
    );

    let reff = ctx.arena.types.fresh_var(0);
    define_constructor(
        ctx,
        constructors::C_REF,
        Scheme::Poly(
            vec![reff.as_tyvar().id],
            ctx.arena.types.arrow(reff, ctx.arena.types.reff(reff)),
        ),
    );

    let eq = ctx.arena.types.fresh_var(0);
    let eq_ty = ctx.arena.types.tuple(vec![eq, eq]);

    let eq_sch = Scheme::Poly(
        vec![eq.as_tyvar().id],
        ctx.arena.types.arrow(eq_ty, ctx.arena.types.bool()),
    );
    ctx.define_value(
        sml_util::interner::S_EQUAL,
        Span::dummy(),
        eq_sch,
        IdStatus::Var,
    );
}
