use std::fmt;

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Serialize)]
pub struct Relation<L> {
    pub spelling: L,
    pub args: Vec<FOTerm<L>>,
}

impl<'l, L> Relation<L> {
    pub fn new(spelling: L, args: Vec<FOTerm<L>>) -> Self {
        Self { spelling, args }
    }
}

impl<'de: 'l, 'l, L> Deserialize<'de> for Relation<L> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        todo!()
    }
}

impl<'l, L> fmt::Display for Relation<L>
where
    L: fmt::Display,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
pub enum FOTerm<L> {
    QuantifiedVar(L),
    Const(L),
    Function(L, Vec<FOTerm<L>>),
}

impl<L> fmt::Display for FOTerm<L>
where
    L: fmt::Display,
{
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
