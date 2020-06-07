/// This is likely not the best way to do this, but I've tried to translate
/// the precedence parsing code from MLton as much as possible. Since we can't
/// pattern match on Boxed values, we use an explicit stack instead of how MLton
/// does it.

/// Hold left and right binding power
#[derive(Copy, Clone, Debug)]
pub enum Fixity {
    Infix(u8, u8),
    Nonfix,
}

#[derive(Debug)]
pub enum Element<T: std::fmt::Debug> {
    Infix(u8, T),
    Nonfix(T),
}

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Error {
    /// Expression begins with an infix operator
    InfixInPrefix,
    /// Two operators of the same precedence
    SamePrecedence,
    /// Expression ends with an infix operator
    EndsInfix,
}

pub trait Query<T> {
    fn fixity(&self, t: &T) -> Fixity;
    fn infix(&self, a: T, b: T, c: T) -> T;
    fn apply(&self, a: T, b: T) -> T;
}

pub struct Prec<T: std::fmt::Debug, Q: Query<T>> {
    stack: Vec<Element<T>>,
    query: Q,
}

impl<T: std::fmt::Debug, Q: Query<T>> Prec<T, Q> {
    fn parse(&mut self, item: T) -> Result<(), Error> {
        use Element::*;
        let f = self.query.fixity(&item);

        // Stack must never be empty
        let top = self.stack.pop().unwrap();

        match (top, f) {
            (Nonfix(ele), Fixity::Nonfix) => {
                self.stack.push(Nonfix(self.query.apply(ele, item)));
                Ok(())
            }

            (Nonfix(e1), Fixity::Infix(lbp, rbp)) => {
                let e2 = self.stack.pop();
                let e3 = self.stack.pop();
                if let Some(Infix(bp, e2)) = e2 {
                    if let Some(Nonfix(e3)) = e3 {
                        if lbp > bp {
                            self.stack.push(Nonfix(e3));
                            self.stack.push(Infix(bp, e2));
                            self.stack.push(Nonfix(e1));
                            self.stack.push(Infix(rbp, item));
                            Ok(())
                        } else if lbp == bp {
                            Err(Error::SamePrecedence)
                        } else {
                            self.stack.push(Nonfix(self.query.infix(e2, e3, e1)));
                            self.parse(item)
                        }
                    } else {
                        if let Some(e) = e3 {
                            self.stack.push(e);
                        }
                        self.stack.push(Infix(bp, e2));
                        self.stack.push(Nonfix(e1));
                        self.stack.push(Infix(rbp, item));
                        Ok(())
                    }
                } else {
                    if let Some(e) = e3 {
                        self.stack.push(e);
                    }
                    if let Some(e) = e2 {
                        self.stack.push(e);
                    }
                    self.stack.push(Nonfix(e1));
                    self.stack.push(Infix(rbp, item));
                    Ok(())
                }
            }
            (Infix(bp, ele), Fixity::Nonfix) => {
                self.stack.push(Infix(bp, ele));
                self.stack.push(Nonfix(item));
                Ok(())
            }
            (Infix(_, _), Fixity::Infix(_, _)) => Err(Error::InfixInPrefix),
        }
    }

    fn finish(&mut self) -> Result<T, Error> {
        // MLton has Error.bugs here, so I assume that it's safe to unwrap here
        let e1 = self.stack.pop().expect("parser::precedence");
        match e1 {
            Element::Nonfix(e) => {
                if self.stack.is_empty() {
                    Ok(e)
                } else {
                    let e2 = self.stack.pop().expect("parser::precedence");
                    let e3 = self.stack.pop().expect("parser::precedence");
                    match (e2, e3) {
                        (Element::Infix(_, e2), Element::Nonfix(e3)) => {
                            self.stack
                                .push(Element::Nonfix(self.query.infix(e2, e3, e)));
                            self.finish()
                        }
                        _ => panic!("parser::precedence"),
                    }
                }
            }
            Element::Infix(_, e) => Err(Error::EndsInfix),
        }
    }

    pub fn run(q: Q, mut items: Vec<T>) -> Result<T, Error> {
        let mut prec = Prec {
            stack: Vec::new(),
            query: q,
        };

        let first = items.remove(0);
        match prec.query.fixity(&first) {
            Fixity::Infix(_, _) => return Err(Error::InfixInPrefix),
            _ => {}
        }
        prec.stack.push(Element::Nonfix(first));

        for item in items {
            prec.parse(item)?;
        }
        prec.finish()
    }
}
