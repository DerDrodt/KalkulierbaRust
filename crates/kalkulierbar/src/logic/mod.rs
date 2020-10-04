pub mod fo;
pub mod transform;

use std::fmt;

use fo::FOTerm;

pub use transform::Lit;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum LogicNode<'l> {
    Var(&'l str),
    Not(Box<LogicNode<'l>>),
    And(Box<LogicNode<'l>>, Box<LogicNode<'l>>),
    Or(Box<LogicNode<'l>>, Box<LogicNode<'l>>),
    Impl(Box<LogicNode<'l>>, Box<LogicNode<'l>>),
    Equiv(Box<LogicNode<'l>>, Box<LogicNode<'l>>),
    //Rel(String, Vec<FOTerm>),
    //All(String, Box<LogicNode>, Vec<String>),
    //Ex(String, Box<LogicNode>, Vec<String>),
}

impl<'l> LogicNode<'l> {
    pub fn to_basic_ops(self) -> Self {
        match self {
            LogicNode::Impl(left, right) => LogicNode::Or(
                Box::new(LogicNode::Not(Box::new(left.to_basic_ops()))),
                Box::new(right.to_basic_ops()),
            ),
            LogicNode::Equiv(left, right) => {
                let left = left.to_basic_ops();
                let right = right.to_basic_ops();

                let both_true = LogicNode::And(Box::new(left.clone()), Box::new(right.clone()));
                let both_false = LogicNode::And(
                    Box::new(LogicNode::Not(Box::new(left))),
                    Box::new(LogicNode::Not(Box::new(right))),
                );

                LogicNode::Or(Box::new(both_true), Box::new(both_false))
            }

            LogicNode::Var(_) => self,
            LogicNode::Not(c) => LogicNode::Not(Box::new(c.to_basic_ops())),
            LogicNode::And(l, r) => {
                LogicNode::And(Box::new(l.to_basic_ops()), Box::new(r.to_basic_ops()))
            }
            LogicNode::Or(l, r) => {
                LogicNode::Or(Box::new(l.to_basic_ops()), Box::new(r.to_basic_ops()))
            }
            //LogicNode::Rel(spelling, args) => todo!(),
            //LogicNode::All(_, _, _) => todo!(),
            //LogicNode::Ex(_, _, _) => todo!(),
        }
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
            //LogicNode::Rel(_, _) => todo!(), //LogicNode::All(_, _, _) => {}
            //LogicNode::Ex(_, _, _) => {}
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
