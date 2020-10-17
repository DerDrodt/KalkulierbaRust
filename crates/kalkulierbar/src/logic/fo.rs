use std::fmt;

use serde::{Deserialize, Serialize};

use crate::KStr;

#[derive(Clone, Debug, Serialize)]
pub struct Relation<'f> {
    pub spelling: &'f str,
    pub args: Vec<FOTerm>,
}

impl<'l> Relation<'l> {
    pub fn new(spelling: &'l str, args: Vec<FOTerm>) -> Self {
        Self { spelling, args }
    }
}

impl<'de: 'l, 'l> Deserialize<'de> for Relation<'l> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        todo!()
    }
}

impl<'l> fmt::Display for Relation<'l> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum FOTerm {
    QuantifiedVar(KStr),
    Const(KStr),
    Function(KStr, Vec<FOTerm>),
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
