use super::*;
use sml_frontend::ast;
use sml_frontend::parser::precedence::{self, Fixity, Precedence, Query};
use sml_util::{span::*, stack::Stack};
use std::collections::HashMap;

pub enum Error {
    UnboundTyvar(Symbol, Span),
    UnboundTycon(Symbol, Span),
    UnboundVar(Symbol, Span),

    TyconArg(Symbol, Span, usize, usize),
}

/// Identifier status for the Value Environment, as defined in the Defn.
pub enum IdStatus {
    Exn(Constructor),
    Con(Constructor),
    Var(Symbol),
}

/// Essentially a minimized Value Environment (VE) containing only datatype
/// constructors, and without the indirection of going from names->id->def
pub struct Cons {
    name: Symbol,
    scheme: Scheme,
}

/// TyStr, a [`TypeStructure`] from the Defn. This is a component of the
/// Type Environment, TE
pub enum TypeStructure {
    /// TyStr (t, VE), a datatype
    Datatype(Tycon, Vec<Cons>),
    /// TyStr (_, VE), a definition. Rather than include a whole VE hashmap,
    /// we can include just a single entry
    Scheme(Scheme),
    /// TyStr (t, {}), a name
    Tycon(Tycon),
}

impl TypeStructure {
    pub fn arity(&self) -> usize {
        match self {
            TypeStructure::Tycon(con) | TypeStructure::Datatype(con, _) => con.arity,
            TypeStructure::Scheme(s) => s.arity(),
        }
    }

    pub fn apply(&self, args: Vec<Type>) -> Type {
        match self {
            TypeStructure::Tycon(con) | TypeStructure::Datatype(con, _) => Type::Con(*con, args),
            TypeStructure::Scheme(s) => s.apply(args),
        }
    }
}

/// An environment scope, that can hold a collection of type and expr bindings
#[derive(Default)]
pub struct Namespace {
    parent: Option<usize>,
    types: HashMap<Symbol, TypeId>,
    values: HashMap<Symbol, ExprId>,
    infix: HashMap<Symbol, Fixity>,
}

pub struct Context {
    tmvars: Stack<Symbol>,
    tyvars: Stack<Symbol>,

    namespaces: Vec<Namespace>,
    current: usize,

    types: Vec<TypeStructure>,
    values: Vec<(Scheme, IdStatus)>,

    decls: Vec<Decl>,
}

impl Namespace {
    pub fn with_parent(id: usize) -> Namespace {
        Namespace {
            parent: Some(id),
            types: HashMap::with_capacity(32),
            values: HashMap::with_capacity(64),
            infix: HashMap::with_capacity(16),
        }
    }
}

impl Context {
    /// Keep track of the type variable stack, while executing the combinator
    /// function `f` on `self`. Any stack growth is popped off after `f`
    /// returns.
    fn with_tyvars<T, F: FnMut(&mut Context) -> T>(&mut self, mut f: F) -> T {
        let n = self.tyvars.len();
        let r = f(self);
        let to_pop = self.tyvars.len() - n;
        self.tyvars.popn(to_pop);
        r
    }

    /// Keep track of the term variable stack, while executing the combinator
    /// function `f` on `self`. Any stack growth is popped off after `f`
    /// returns.
    fn with_tmvars<T, F: FnMut(&mut Context) -> T>(&mut self, mut f: F) -> T {
        let n = self.tmvars.len();
        let r = f(self);
        let to_pop = self.tmvars.len() - n;
        self.tmvars.popn(to_pop);
        r
    }

    /// Handle namespacing. The method creates a new child namespace, enters it
    /// and then calls `f`. After `f` has returned, the current scope is returned
    /// to it's previous value
    fn with_scope<T, F: FnMut(&mut Context) -> T>(&mut self, mut f: F) -> T {
        let prev = self.current;
        let next = self.namespaces.len();
        self.namespaces.push(Namespace::with_parent(prev));
        self.current = next;
        let r = f(self);

        self.current = prev;
        r
    }

    fn define_type(&mut self, sym: Symbol, tystr: TypeStructure) -> TypeId {
        let id = TypeId(self.types.len() as u32);
        self.types.push(tystr);
        self.namespaces[self.current].types.insert(sym, id);
        id
    }

    fn define_value(&mut self, sym: Symbol, scheme: Scheme, is: IdStatus) -> ExprId {
        let id = ExprId(self.values.len() as u32);
        self.values.push((scheme, is));
        self.namespaces[self.current].values.insert(sym, id);
        id
    }

    /// Starting from the current [`Namespace`], search for a bound name.
    /// If it's not found, then recursively search parent namespaces
    fn lookup_infix(&self, s: Symbol) -> Option<Fixity> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.infix.get(&s) {
                Some(idx) => return Some(*idx),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }

    fn lookup_type(&self, sym: Symbol) -> Option<&TypeStructure> {
        let mut ptr = &self.namespaces[self.current];
        loop {
            match ptr.types.get(&sym) {
                Some(idx) => return Some(&self[*idx]),
                None => ptr = &self.namespaces[ptr.parent?],
            }
        }
    }
}

impl Context {
    fn elaborate_type(&mut self, ty: &ast::Type, allow_unbound: bool) -> Result<Type, Error> {
        use ast::TypeKind::*;
        match &ty.data {
            Var(s) => match (self.tyvars.lookup(s), allow_unbound) {
                (Some(idx), _) => Ok(Type::Var(Local { name: *s, idx })),
                // TODO
                (None, true) => Ok(Type::Var(Local { name: *s, idx: 0 })),
                (None, false) => Err(Error::UnboundTyvar(*s, ty.span)),
            },
            Con(s, args) => {
                let args = args
                    .iter()
                    .map(|ty| self.elaborate_type(&ty, allow_unbound))
                    .collect::<Result<Vec<Type>, _>>()?;
                let con = self
                    .lookup_type(*s)
                    .ok_or(Error::UnboundTycon(*s, ty.span))?;
                if con.arity() != args.len() {
                    Err(Error::TyconArg(*s, ty.span, con.arity(), args.len()))
                } else {
                    Ok(con.apply(args))
                }
            }
            Record(rows) => rows
                .into_iter()
                .map(|row| {
                    Ok(Row {
                        label: row.label,
                        data: self.elaborate_type(&row.data, allow_unbound)?,
                    })
                })
                .collect::<Result<Vec<Row<Type>>, Error>>()
                .map(Type::Record),
        }
    }
}

impl Context {
    fn elab_decl_fixity(&mut self, fixity: &ast::Fixity, bp: u8, sym: Symbol) -> Result<(), Error> {
        let fix = match fixity {
            ast::Fixity::Infix => Fixity::Infix(bp, bp + 1),
            ast::Fixity::Infixr => Fixity::Infix(bp + 1, bp),
            ast::Fixity::Nonfix => Fixity::Nonfix,
        };
        self.namespaces[self.current].infix.insert(sym, fix);
        Ok(())
    }

    fn elab_decl_local(&mut self, decls: &ast::Decl, body: &ast::Decl) -> Result<(), Error> {
        self.with_scope(|f| {
            f.elaborate_decl(decls)?;
            f.elaborate_decl(body)
        })
    }

    fn elab_decl_seq(&mut self, decls: &[ast::Decl]) -> Result<(), Error> {
        for d in decls {
            self.elaborate_decl(d)?;
        }
        Ok(())
    }

    fn elab_decl_type(&mut self, tbs: &[ast::Typebind]) -> Result<(), Error> {
        for typebind in tbs {
            let scheme = if !typebind.tyvars.is_empty() {
                let ty = self.with_tyvars(|f| f.elaborate_type(&typebind.ty, false))?;
                Scheme::Poly(ty, typebind.tyvars.clone())
            } else {
                Scheme::Mono(self.elaborate_type(&typebind.ty, false)?)
            };
            self.define_type(typebind.tycon, TypeStructure::Scheme(scheme));
        }
        Ok(())
    }

    fn elaborate_decl(&mut self, decl: &ast::Decl) -> Result<(), Error> {
        use ast::DeclKind::*;
        match &decl.data {
            Datatype(dbs) => unimplemented!(),
            Type(tbs) => unimplemented!(),
            Function(tyvars, fbs) => unimplemented!(),
            Value(pat, expr) => unimplemented!(),
            Exception(exns) => unimplemented!(),
            Fixity(fixity, bp, sym) => self.elab_decl_fixity(fixity, *bp, *sym),
            Local(decls, body) => self.elab_decl_local(decls, body),
            Seq(decls) => self.elab_decl_seq(decls),
            Do(expr) => unimplemented!(),
        }
    }
}

impl std::ops::Index<TypeId> for Context {
    type Output = TypeStructure;
    fn index(&self, index: TypeId) -> &Self::Output {
        &self.types[index.0 as usize]
    }
}

impl std::ops::Index<ExprId> for Context {
    type Output = (Scheme, IdStatus);
    fn index(&self, index: ExprId) -> &Self::Output {
        &self.values[index.0 as usize]
    }
}
