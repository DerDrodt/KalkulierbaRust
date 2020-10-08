pub mod fo;
pub mod transform;

use std::fmt;

use fo::FOTerm;

pub use transform::Lit;

use self::transform::{to_basic::ToBasicOps, visitor::LogicNodeVisitor};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LogicNode<'l> {
    Var(&'l str),
    Not(Box<LogicNode<'l>>),
    And(Box<LogicNode<'l>>, Box<LogicNode<'l>>),
    Or(Box<LogicNode<'l>>, Box<LogicNode<'l>>),
    Impl(Box<LogicNode<'l>>, Box<LogicNode<'l>>),
    Equiv(Box<LogicNode<'l>>, Box<LogicNode<'l>>),
    Rel(&'l str, Vec<FOTerm<'l>>),
    All(&'l str, Box<LogicNode<'l>>, Vec<&'l str>),
    Ex(&'l str, Box<LogicNode<'l>>, Vec<&'l str>),
}

impl<'l> LogicNode<'l> {
    pub fn to_basic_ops(self) -> Self {
        ToBasicOps::new().visit(&self)
    }
}

impl<'l> fmt::Display for LogicNode<'l> {
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

    #[test]
    fn var_to_basic_ops() {
        assert_eq!(Var("a"), Var("a").to_basic_ops());
        assert_eq!(Var("MyTestVar"), Var("MyTestVar").to_basic_ops());
        assert_eq!(Var("MyT35tV4r"), Var("MyT35tV4r").to_basic_ops());
    }

    #[test]
    fn not_to_basic_ops() {
        let n1 = Not(Box::new(Var("a")));
        let n2 = Not(Box::new(Equiv(
            Box::new(Not(Box::new(Not(Box::new(Var("b")))))),
            Box::new(Var("a")),
        )));
        let n3 = Not(Box::new(And(
            Box::new(Or(Box::new(Var("a")), Box::new(Not(Box::new(Var("a")))))),
            Box::new(Not(Box::new(Var("c")))),
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
    }

    #[test]
    fn and_to_basic_ops() {
        let a1 = And(
            Box::new(Not(Box::new(Var("a")))),
            Box::new(And(
                Box::new(Var("b")),
                Box::new(Impl(Box::new(Var("b")), Box::new(Var("a")))),
            )),
        );
        let a2 = And(Box::new(Var("a")), Box::new(Not(Box::new(Var("a")))));
        let a3 = And(
            Box::new(Or(Box::new(Var("a")), Box::new(Not(Box::new(Var("a")))))),
            Box::new(Var("b")),
        );

        assert_eq!(
            "(¬a ∧ (b ∧ (¬b ∨ a)))".to_string(),
            a1.to_basic_ops().to_string()
        );
        assert_eq!("(a ∧ ¬a)".to_string(), a2.to_basic_ops().to_string());
        assert_eq!("((a ∨ ¬a) ∧ b)".to_string(), a3.to_basic_ops().to_string());
    }

    #[test]
    fn or_to_basic_ops() {
        let o1 = Or(Box::new(Var("a")), Box::new(Var("b")));
        let o2 = Or(
            Box::new(Or(Box::new(Var("a")), Box::new(Not(Box::new(Var("b")))))),
            Box::new(Equiv(Box::new(Var("a")), Box::new(Var("b")))),
        );
        let o3 = Or(
            Box::new(Not(Box::new(And(Box::new(Var("a")), Box::new(Var("b")))))),
            Box::new(Not(Box::new(Impl(
                Box::new(Var("b")),
                Box::new(Not(Box::new(Var("b")))),
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
    }
}
