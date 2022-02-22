use std::fmt;

use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{symbol::Symbol, SynEq};

use super::{
    transform::{term_manipulator::VariableInstantiator, visitor::FOTermVisitor},
    unify::Unifier,
};

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Relation {
    pub spelling: Symbol,
    #[serde(rename = "arguments")]
    pub args: Vec<FOTerm>,
}

impl Relation {
    pub fn new(spelling: Symbol, args: Vec<FOTerm>) -> Self {
        Self { spelling, args }
    }

    pub fn syn_eq(&self, r: &Relation) -> bool {
        self.spelling == r.spelling
            && self.args.len() == r.args.len()
            && self.args.iter().zip(&r.args).all(|(t1, t2)| t1.syn_eq(t2))
    }

    pub fn apply_unifier(&mut self, u: &Unifier) {
        let instantiator = VariableInstantiator(u);
        self.args = self.args.iter().map(|a| instantiator.visit(a)).collect();
    }
}

impl SynEq for Relation {
    fn syn_eq(&self, r: &Relation) -> bool {
        self.spelling == r.spelling
            && self.args.len() == r.args.len()
            && self.args.iter().zip(&r.args).all(|(t1, t2)| t1.syn_eq(t2))
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
        matches!(self, FOTerm::QuantifiedVar(_))
    }

    pub fn is_const(&self) -> bool {
        matches!(self, FOTerm::Const(_))
    }

    pub fn is_fn(&self) -> bool {
        matches!(self, FOTerm::Function(_, _))
    }

    pub fn spelling(&self) -> Symbol {
        match self {
            FOTerm::QuantifiedVar(c) => *c,
            FOTerm::Const(c) => *c,
            FOTerm::Function(c, _) => *c,
        }
    }
}

impl Serialize for FOTerm {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let num_fields = if self.is_fn() { 3 } else { 2 };
        let mut state = serializer.serialize_struct("FirstOrderTerm", num_fields)?;
        let ty = match self {
            FOTerm::QuantifiedVar(_) => "QuantifiedVariable",
            FOTerm::Const(_) => "Constant",
            FOTerm::Function(..) => "Function",
        };
        state.serialize_field("type", ty)?;
        state.serialize_field("spelling", &self.spelling())?;
        if let FOTerm::Function(_, args) = self {
            state.serialize_field("arguments", args)?;
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for FOTerm {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "type")]
            Ty,
            #[serde(rename = "spelling")]
            Spelling,
            #[serde(rename = "arguments")]
            Args,
        }

        struct TermVisitor;

        impl<'de> Visitor<'de> for TermVisitor {
            type Value = FOTerm;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct FOTerm")
            }

            fn visit_map<V>(self, mut map: V) -> Result<FOTerm, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut spelling: Option<Symbol> = None;
                let mut arguments: Option<Vec<FOTerm>> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Ty => {
                            if ty.is_some() {
                                return Err(de::Error::duplicate_field("type"));
                            }
                            ty = Some(map.next_value()?);
                        }
                        Field::Spelling => {
                            if spelling.is_some() {
                                return Err(de::Error::duplicate_field("spelling"));
                            }
                            spelling = Some(map.next_value()?);
                        }
                        Field::Args => {
                            if arguments.is_some() {
                                return Err(de::Error::duplicate_field("arguments"));
                            }
                            arguments = Some(map.next_value()?);
                        }
                    }
                }

                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                let spelling = spelling.ok_or_else(|| de::Error::missing_field("spelling"))?;
                Ok(if ty == "Function" {
                    let args = arguments.ok_or_else(|| de::Error::missing_field("arguments"))?;
                    FOTerm::Function(spelling, args)
                } else {
                    let ty: &str = &ty;
                    match ty {
                        "QuantifiedVariable" => FOTerm::QuantifiedVar(spelling),
                        "Constant" => FOTerm::Const(spelling),
                        _ => todo!(),
                    }
                })
            }
        }
        const FIELDS: &[&str] = &["type", "spelling", "arguments"];
        deserializer.deserialize_struct("FOTerm", FIELDS, TermVisitor)
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
