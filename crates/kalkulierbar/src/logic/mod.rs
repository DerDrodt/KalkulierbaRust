pub mod fo;
pub mod transform;
pub mod unify;

use std::fmt;

use crate::symbol::Symbol;
use crate::SynEq;

use fo::FOTerm;

use serde::de::{self, MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize};
pub use transform::Lit;

use self::transform::to_basic::ToBasicOps;
use self::transform::transformer::MutLogicNodeTransformer;
use self::unify::Unifier;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LogicNode {
    Var(Symbol),
    Not(Box<LogicNode>),
    And(Box<LogicNode>, Box<LogicNode>),
    Or(Box<LogicNode>, Box<LogicNode>),
    Impl(Box<LogicNode>, Box<LogicNode>),
    Equiv(Box<LogicNode>, Box<LogicNode>),
    Rel(Symbol, Vec<FOTerm>),
    All(Symbol, Box<LogicNode>),
    Ex(Symbol, Box<LogicNode>),
}

impl LogicNode {
    pub fn to_basic_ops(self) -> Self {
        ToBasicOps::new().visit(self)
    }

    pub fn instantiate(&self, u: &Unifier) -> Self {
        match self {
            LogicNode::Var(_) => panic!(),
            LogicNode::Not(c) => Self::Not(c.instantiate(u).into()),
            LogicNode::And(l, r) => Self::And(l.instantiate(u).into(), r.instantiate(u).into()),
            LogicNode::Or(l, r) => Self::Or(l.instantiate(u).into(), r.instantiate(u).into()),
            LogicNode::Impl(l, r) => Self::Impl(l.instantiate(u).into(), r.instantiate(u).into()),
            LogicNode::Equiv(l, r) => Self::Equiv(l.instantiate(u).into(), r.instantiate(u).into()),
            LogicNode::Rel(s, args) => {
                Self::Rel(*s, args.iter().map(|a| a.instantiate(u)).collect())
            }
            LogicNode::All(s, c) => Self::All(*s, c.instantiate(u).into()),
            LogicNode::Ex(s, c) => Self::Ex(*s, c.instantiate(u).into()),
        }
    }
}

impl fmt::Display for LogicNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LogicNode::Var(s) => write!(f, "{}", s),
            LogicNode::Not(c) => write!(f, "¬{}", c),
            LogicNode::And(l, r) => write!(f, "({} ∧ {})", l, r),
            LogicNode::Or(l, r) => write!(f, "({} ∨ {})", l, r),
            LogicNode::Impl(l, r) => write!(f, "({} → {})", l, r),
            LogicNode::Equiv(l, r) => write!(f, "({} <=> {})", l, r),
            LogicNode::Rel(name, args) => {
                let mut arg_str = String::new();

                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        arg_str.push_str(", ");
                    }
                    arg_str.push_str(&a.to_string());
                }

                write!(f, "{}({})", name, arg_str)
            }
            LogicNode::All(var, child) => write!(f, "(∀{}: {})", var, child),
            LogicNode::Ex(var, child) => write!(f, "(∃{}: {})", var, child),
        }
    }
}

impl SynEq for LogicNode {
    fn syn_eq(&self, o: &Self) -> bool {
        match (self, o) {
            (Self::Var(s1), Self::Var(s2)) => s1 == s2,
            (Self::And(l1, r1), Self::And(l2, r2)) => l1.syn_eq(l2) && r1.syn_eq(r2),
            (Self::Or(l1, r1), Self::Or(l2, r2)) => l1.syn_eq(l2) && r1.syn_eq(r2),
            (Self::Impl(l1, r1), Self::Impl(l2, r2)) => l1.syn_eq(l2) && r1.syn_eq(r2),
            (Self::Equiv(l1, r1), Self::Equiv(l2, r2)) => l1.syn_eq(l2) && r1.syn_eq(r2),
            (Self::Rel(s1, args1), Self::Rel(s2, args2)) => {
                s1 == s2
                    && args1.len() == args2.len()
                    && args1.iter().zip(args2).all(|(a1, a2)| a1.syn_eq(a2))
            }
            (Self::All(v1, c1), Self::All(v2, c2)) => v1 == v2 && c1.syn_eq(c2),
            (Self::Ex(v1, c1), Self::Ex(v2, c2)) => v1 == v2 && c1.syn_eq(c2),
            _ => false,
        }
    }
}

impl Serialize for LogicNode {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (ty, len) = match self {
            LogicNode::Var(_) => ("var", 2),
            LogicNode::Not(_) => ("not", 2),
            LogicNode::And(_, _) => ("and", 3),
            LogicNode::Or(_, _) => ("or", 3),
            LogicNode::Impl(_, _) => ("impl", 3),
            LogicNode::Equiv(_, _) => ("equiv", 3),
            LogicNode::Rel(_, _) => ("relation", 3),
            LogicNode::All(_, _) => ("allquant", 3),
            LogicNode::Ex(_, _) => ("exquant", 3),
        };

        let mut state = serializer.serialize_struct("LogicNode", len)?;
        state.serialize_field("type", ty)?;
        match self {
            Self::Var(s) => {
                state.serialize_field("spelling", s)?;
            }
            Self::Not(c) => {
                state.serialize_field("child", c)?;
            }
            Self::And(l, r) | Self::Or(l, r) | Self::Impl(l, r) | Self::Equiv(l, r) => {
                state.serialize_field("leftChild", l)?;
                state.serialize_field("rightChild", r)?;
            }
            Self::Rel(s, args) => {
                state.serialize_field("spelling", s)?;
                state.serialize_field("arguments", args)?;
            }
            Self::All(v, c) | Self::Ex(v, c) => {
                state.serialize_field("varName", v)?;
                state.serialize_field("child", c)?;
            }
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for LogicNode {
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
            #[serde(rename = "child")]
            Child,
            #[serde(rename = "leftChild")]
            LeftChild,
            #[serde(rename = "rightChild")]
            RightChild,
            #[serde(rename = "arguments")]
            Arguments,
            #[serde(rename = "varName")]
            VarName,
            #[serde(rename = "boundVariables")]
            BoundVariables,
        }

        struct NodeVisitor;

        impl<'de> Visitor<'de> for NodeVisitor {
            type Value = LogicNode;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct LogicNode")
            }

            fn visit_map<V>(self, mut map: V) -> Result<LogicNode, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut spelling: Option<Symbol> = None;
                let mut child: Option<LogicNode> = None;
                let mut left: Option<LogicNode> = None;
                let mut right: Option<LogicNode> = None;
                let mut args: Option<Vec<FOTerm>> = None;
                let mut var_name: Option<Symbol> = None;
                let mut bound_vars: Option<Vec<LogicNode>> = None;

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
                        Field::Child => {
                            if child.is_some() {
                                return Err(de::Error::duplicate_field("child"));
                            }
                            child = Some(map.next_value()?);
                        }
                        Field::LeftChild => {
                            if left.is_some() {
                                return Err(de::Error::duplicate_field("leftChild"));
                            }
                            left = Some(map.next_value()?);
                        }
                        Field::RightChild => {
                            if right.is_some() {
                                return Err(de::Error::duplicate_field("rightChild"));
                            }
                            right = Some(map.next_value()?);
                        }
                        Field::Arguments => {
                            if args.is_some() {
                                return Err(de::Error::duplicate_field("arguments"));
                            }
                            args = Some(map.next_value()?);
                        }
                        Field::VarName => {
                            if var_name.is_some() {
                                return Err(de::Error::duplicate_field("varName"));
                            }
                            var_name = Some(map.next_value()?);
                        }
                        Field::BoundVariables => {
                            if bound_vars.is_some() {
                                return Err(de::Error::duplicate_field("boundVars"));
                            }
                            bound_vars = Some(map.next_value()?);
                        }
                    }
                }
                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                let ty: &str = &ty;
                Ok(match ty {
                    "var" => LogicNode::Var(
                        spelling.ok_or_else(|| de::Error::missing_field("spelling"))?,
                    ),
                    "not" => LogicNode::Not(
                        child
                            .ok_or_else(|| de::Error::missing_field("child"))?
                            .into(),
                    ),
                    "and" => LogicNode::And(
                        left.ok_or_else(|| de::Error::missing_field("leftChild"))?
                            .into(),
                        right
                            .ok_or_else(|| de::Error::missing_field("rightChild"))?
                            .into(),
                    ),
                    "or" => LogicNode::Or(
                        left.ok_or_else(|| de::Error::missing_field("leftChild"))?
                            .into(),
                        right
                            .ok_or_else(|| de::Error::missing_field("rightChild"))?
                            .into(),
                    ),
                    "impl" => LogicNode::Impl(
                        left.ok_or_else(|| de::Error::missing_field("leftChild"))?
                            .into(),
                        right
                            .ok_or_else(|| de::Error::missing_field("rightChild"))?
                            .into(),
                    ),
                    "equiv" => LogicNode::Equiv(
                        left.ok_or_else(|| de::Error::missing_field("leftChild"))?
                            .into(),
                        right
                            .ok_or_else(|| de::Error::missing_field("rightChild"))?
                            .into(),
                    ),
                    "relation" => LogicNode::Rel(
                        spelling.ok_or_else(|| de::Error::missing_field("spelling"))?,
                        args.ok_or_else(|| de::Error::missing_field("arguments"))?,
                    ),
                    "allquant" => LogicNode::All(
                        var_name.ok_or_else(|| de::Error::missing_field("varName"))?,
                        child
                            .ok_or_else(|| de::Error::missing_field("child"))?
                            .into(),
                    ),
                    "exquant" => LogicNode::Ex(
                        var_name.ok_or_else(|| de::Error::missing_field("varName"))?,
                        child
                            .ok_or_else(|| de::Error::missing_field("child"))?
                            .into(),
                    ),
                    _ => todo!(),
                })
            }
        }

        const FIELDS: &[&str] = &[
            "type",
            "spelling",
            "child",
            "leftChild",
            "rightChild",
            "arguments",
            "varName",
            "boundVariables",
        ];
        deserializer.deserialize_struct("LogicNode", FIELDS, NodeVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::LogicNode::*;
    use crate::session;
    use crate::symbol::Symbol;

    #[test]
    fn var_to_basic_ops() {
        session(|| {
            assert_eq!(
                Var(Symbol::intern("a")),
                Var(Symbol::intern("a")).to_basic_ops()
            );
            assert_eq!(
                Var(Symbol::intern("MyTestVar")),
                Var(Symbol::intern("MyTestVar")).to_basic_ops()
            );
            assert_eq!(
                Var(Symbol::intern("MyT35tV4r")),
                Var(Symbol::intern("MyT35tV4r")).to_basic_ops()
            );
        })
    }

    #[test]
    fn not_to_basic_ops() {
        session(|| {
            let n1 = Not(Box::new(Var(Symbol::intern("a"))));
            let n2 = Not(Box::new(Equiv(
                Box::new(Not(Box::new(Not(Box::new(Var(Symbol::intern("b"))))))),
                Box::new(Var(Symbol::intern("a"))),
            )));
            let n3 = Not(Box::new(And(
                Box::new(Or(
                    Box::new(Var(Symbol::intern("a"))),
                    Box::new(Not(Box::new(Var(Symbol::intern("a"))))),
                )),
                Box::new(Not(Box::new(Var(Symbol::intern("c"))))),
            )));

            assert_eq!("¬a".to_string(), n1.to_basic_ops().to_string());
            assert_eq!(
                "¬((¬¬¬b ∨ a) ∧ (¬¬b ∨ ¬a))".to_string(),
                n2.to_basic_ops().to_string()
            );
            assert_eq!(
                "¬((a ∨ ¬a) ∧ ¬c)".to_string(),
                n3.to_basic_ops().to_string()
            );
        })
    }

    #[test]
    fn and_to_basic_ops() {
        session(|| {
            let a1 = And(
                Box::new(Not(Box::new(Var(Symbol::intern("a"))))),
                Box::new(And(
                    Box::new(Var(Symbol::intern("b"))),
                    Box::new(Impl(
                        Box::new(Var(Symbol::intern("b"))),
                        Box::new(Var(Symbol::intern("a"))),
                    )),
                )),
            );
            let a2 = And(
                Box::new(Var(Symbol::intern("a"))),
                Box::new(Not(Box::new(Var(Symbol::intern("a"))))),
            );
            let a3 = And(
                Box::new(Or(
                    Box::new(Var(Symbol::intern("a"))),
                    Box::new(Not(Box::new(Var(Symbol::intern("a"))))),
                )),
                Box::new(Var(Symbol::intern("b"))),
            );

            assert_eq!(
                "(¬a ∧ (b ∧ (¬b ∨ a)))".to_string(),
                a1.to_basic_ops().to_string()
            );
            assert_eq!("(a ∧ ¬a)".to_string(), a2.to_basic_ops().to_string());
            assert_eq!("((a ∨ ¬a) ∧ b)".to_string(), a3.to_basic_ops().to_string());
        })
    }

    #[test]
    fn or_to_basic_ops() {
        session(|| {
            let o1 = Or(
                Box::new(Var(Symbol::intern("a"))),
                Box::new(Var(Symbol::intern("b"))),
            );
            let o2 = Or(
                Box::new(Or(
                    Box::new(Var(Symbol::intern("a"))),
                    Box::new(Not(Box::new(Var(Symbol::intern("b"))))),
                )),
                Box::new(Equiv(
                    Box::new(Var(Symbol::intern("a"))),
                    Box::new(Var(Symbol::intern("b"))),
                )),
            );
            let o3 = Or(
                Box::new(Not(Box::new(And(
                    Box::new(Var(Symbol::intern("a"))),
                    Box::new(Var(Symbol::intern("b"))),
                )))),
                Box::new(Not(Box::new(Impl(
                    Box::new(Var(Symbol::intern("b"))),
                    Box::new(Not(Box::new(Var(Symbol::intern("b"))))),
                )))),
            );

            assert_eq!("(a ∨ b)".to_string(), o1.to_basic_ops().to_string());
            assert_eq!(
                "((a ∨ ¬b) ∨ ((¬a ∨ b) ∧ (a ∨ ¬b)))".to_string(),
                o2.to_basic_ops().to_string()
            );
            assert_eq!(
                "(¬(a ∧ b) ∨ ¬(¬b ∨ ¬b))".to_string(),
                o3.to_basic_ops().to_string()
            );
        })
    }
}
