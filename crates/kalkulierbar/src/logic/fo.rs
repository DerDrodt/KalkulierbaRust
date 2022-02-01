use std::fmt;

use serde::{Deserialize, Serialize};

use crate::symbol::Symbol;

#[derive(Clone, Debug, Serialize)]
pub struct Relation {
    pub spelling: Symbol,
    pub args: Vec<FOTerm>,
}

impl Relation {
    pub fn new(spelling: Symbol, args: Vec<FOTerm>) -> Self {
        Self { spelling, args }
    }
}

impl<'de: 'l, 'l> Deserialize<'de> for Relation {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        todo!()
    }
}

impl<'l> fmt::Display for Relation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut arg_str = String::new();

        for (i, a) in self.args.iter().enumerate() {
            if i > 0 {
                arg_str.push_str(", ");
            }
            arg_str.push_str(&a.to_string());
        }

        write!(f, "{}({})", self.spelling, arg_str)
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum FOTerm {
    QuantifiedVar(Symbol),
    Const(Symbol),
    Function(Symbol, Vec<FOTerm>),
}

impl FOTerm {
    pub fn syn_eq(&self, t: &FOTerm) -> bool {
        match (self, t) {
            (FOTerm::QuantifiedVar(s1), FOTerm::QuantifiedVar(s2)) => *s1 == *s2,
            (FOTerm::Const(s1), FOTerm::Const(s2)) => *s1 == *s2,
            (FOTerm::Function(s1, args1), FOTerm::Function(s2, args2)) => {
                *s1 == *s2
                    && args1.len() == args2.len()
                    && args1.iter().zip(args2).all(|(t1, t2)| t1.syn_eq(t2))
            }
            _ => false,
        }
    }

    pub fn is_var(&self) -> bool {
        match self {
            FOTerm::QuantifiedVar(_) => true,
            _ => false,
        }
    }

    pub fn is_const(&self) -> bool {
        match self {
            FOTerm::Const(_) => true,
            _ => false,
        }
    }

    pub fn is_fn(&self) -> bool {
        match self {
            FOTerm::Function(_, _) => true,
            _ => false,
        }
    }
}

impl Serialize for FOTerm {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        todo!()
    }
}

impl<'de> Deserialize<'de> for FOTerm {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        todo!()
    }
}

impl<'l> fmt::Display for FOTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FOTerm::QuantifiedVar(name) => write!(f, "{}", name),
            FOTerm::Const(c) => write!(f, "{}", c),
            FOTerm::Function(name, args) => {
                let mut arg_str = String::new();

                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        arg_str.push_str(", ");
                    }
                    arg_str.push_str(&a.to_string());
                }

                write!(f, "{}({})", name, arg_str)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{parse::fo::parse_fo_term, session};

    #[test]
    fn eq_terms() {
        session(|| {
            for (a, b) in &[
                ("f(g(f(q)), c)", "f(g(f(q)), c)"),
                ("a", "a"),
                ("f(X)", "f(X)"),
            ] {
                let (a, b) = (parse_fo_term(a).unwrap(), parse_fo_term(b).unwrap());
                assert!(a.syn_eq(&b))
            }
        })
    }

    #[test]
    fn neq_terms() {
        session(|| {
            for (a, b) in &[
                ("f(g(f(q)), c)", "f(g(f(q)), d)"),
                ("a", "d"),
                ("f(X)", "f(X, X)"),
                ("f(g(f(c)))", "f(g(f(g(c))))"),
                ("X", "Y"),
                ("X", "x"),
            ] {
                let (a, b) = (parse_fo_term(a).unwrap(), parse_fo_term(b).unwrap());
                assert!(!a.syn_eq(&b), "{}={}", a, b)
            }
        })
    }
}
