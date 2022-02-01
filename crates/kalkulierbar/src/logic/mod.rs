pub mod fo;
pub mod transform;
pub mod unify;

use std::fmt;

use crate::symbol::Symbol;

use fo::FOTerm;

pub use transform::Lit;

use self::transform::{to_basic::ToBasicOps, visitor::MutLogicNodeVisitor};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LogicNode {
    Var(Symbol),
    Not(Box<LogicNode>),
    And(Box<LogicNode>, Box<LogicNode>),
    Or(Box<LogicNode>, Box<LogicNode>),
    Impl(Box<LogicNode>, Box<LogicNode>),
    Equiv(Box<LogicNode>, Box<LogicNode>),
    Rel(Symbol, Vec<FOTerm>),
    All(Symbol, Box<LogicNode>, Vec<Symbol>),
    Ex(Symbol, Box<LogicNode>, Vec<Symbol>),
}

impl LogicNode {
    pub fn to_basic_ops(self) -> Self {
        ToBasicOps::new().visit(&self)
    }
}

impl fmt::Display for LogicNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LogicNode::Var(s) => write!(f, "{}", s),
            LogicNode::Not(c) => write!(f, "¬{}", c),
            LogicNode::And(l, r) => write!(f, "({} ∧ {})", l, r),
            LogicNode::Or(l, r) => write!(f, "({} ∨ {})", l, r),
            LogicNode::Impl(l, r) => write!(f, "({} -> {})", l, r),
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
            LogicNode::All(var, child, _) => write!(f, "(∀{}: {})", var, child),
            LogicNode::Ex(var, child, _) => write!(f, "(∃{}: {})", var, child),
        }
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
                "¬((¬¬b ∧ a) ∨ (¬¬¬b ∧ ¬a))".to_string(),
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
                "((a ∨ ¬b) ∨ ((a ∧ b) ∨ (¬a ∧ ¬b)))".to_string(),
                o2.to_basic_ops().to_string()
            );
            assert_eq!(
                "(¬(a ∧ b) ∨ ¬(¬b ∨ ¬b))".to_string(),
                o3.to_basic_ops().to_string()
            );
        })
    }
}
