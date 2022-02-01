use std::collections::HashMap;

use crate::symbol::Symbol;

use super::visitor::{LogicNodeVisitor, MutFOTermVisitor};
use super::{super::LogicNode, term_manipulator::QuantifierLinker};

pub struct ToBasicOps {
    quantifiers: HashMap<Symbol, Vec<Symbol>>,
}

impl ToBasicOps {
    pub fn new() -> Self {
        Self {
            quantifiers: HashMap::new(),
        }
    }
}

impl<'a> LogicNodeVisitor for ToBasicOps {
    type Ret = LogicNode;

    fn visit_var(&mut self, spelling: Symbol) -> Self::Ret {
        LogicNode::Var(spelling)
    }

    fn visit_not(&mut self, child: &LogicNode) -> Self::Ret {
        LogicNode::Not(self.visit(child).into())
    }

    fn visit_and(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        LogicNode::And(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_or(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        LogicNode::Or(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_impl(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        let left = self.visit(left).into();
        let right = self.visit(right).into();
        LogicNode::Or(LogicNode::Not(left).into(), right)
    }

    fn visit_equiv(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        let left = self.visit(left);
        let right = self.visit(right);
        let not_left = LogicNode::Not(left.clone().into()).into();
        let not_right = LogicNode::Not(right.clone().into()).into();

        let both_t = LogicNode::And(left.into(), right.into()).into();
        let both_f = LogicNode::And(not_left, not_right).into();

        LogicNode::Or(both_t, both_f)
    }

    fn visit_rel(&mut self, spelling: Symbol, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        let mut linker = QuantifierLinker::new(&mut self.quantifiers);

        for arg in args {
            linker.visit(arg).unwrap();
        }

        LogicNode::Rel(spelling, args.clone())
    }

    fn visit_all(&mut self, var: Symbol, child: &LogicNode, _: &Vec<Symbol>) -> Self::Ret {
        self.quantifiers.insert(var, Vec::new());
        let child = self.visit(child).into();
        let bound = self.quantifiers.remove(&var).unwrap();
        LogicNode::All(var, child, bound)
    }

    fn visit_ex(&mut self, var: Symbol, child: &LogicNode, _: &Vec<Symbol>) -> Self::Ret {
        self.quantifiers.insert(var, Vec::new());
        let child = self.visit(child).into();
        let bound = self.quantifiers.remove(&var).unwrap();
        LogicNode::Ex(var, child, bound)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session;

    fn var(s: &str) -> LogicNode {
        LogicNode::Var(Symbol::intern(s))
    }

    fn not(n: LogicNode) -> LogicNode {
        LogicNode::Not(Box::new(n))
    }

    fn and(l: LogicNode, r: LogicNode) -> LogicNode {
        LogicNode::And(Box::new(l), Box::new(r))
    }

    fn or(l: LogicNode, r: LogicNode) -> LogicNode {
        LogicNode::Or(Box::new(l), Box::new(r))
    }

    fn imp(l: LogicNode, r: LogicNode) -> LogicNode {
        LogicNode::Impl(Box::new(l), Box::new(r))
    }

    fn equiv(l: LogicNode, r: LogicNode) -> LogicNode {
        LogicNode::Equiv(Box::new(l), Box::new(r))
    }

    fn v1() -> LogicNode {
        var("a")
    }

    fn v2() -> LogicNode {
        var("MyTestVar")
    }

    fn v3() -> LogicNode {
        var("MyT35tV4r")
    }

    fn n1() -> LogicNode {
        not(var("a"))
    }

    fn n2() -> LogicNode {
        not(equiv(not(not(var("b"))), var("a")))
    }

    fn n3() -> LogicNode {
        not(and(or(var("a"), not(var("a"))), not(var("c"))))
    }

    fn a1() -> LogicNode {
        and(not(var("a")), and(var("b"), imp(var("b"), var("a"))))
    }

    fn a2() -> LogicNode {
        and(var("a"), not(var("a")))
    }

    fn a3() -> LogicNode {
        and(or(var("a"), not(var("a"))), var("b"))
    }

    fn o1() -> LogicNode {
        or(var("a"), var("b"))
    }

    fn o2() -> LogicNode {
        or(or(var("a"), not(var("b"))), equiv(var("a"), var("b")))
    }

    fn o3() -> LogicNode {
        or(
            not(and(var("a"), var("b"))),
            not(imp(var("b"), not(var("b")))),
        )
    }

    #[test]
    fn test_var() {
        session(|| {
            assert_eq!("a", format!("{}", v1().to_basic_ops()));
            assert_eq!("MyTestVar", format!("{}", v2().to_basic_ops()));
            assert_eq!("MyT35tV4r", format!("{}", v3().to_basic_ops()));
        })
    }

    #[test]
    fn test_not() {
        session(|| {
            assert_eq!("¬a", format!("{}", n1().to_basic_ops()));
            assert_eq!(
                "¬((¬¬b ∧ a) ∨ (¬¬¬b ∧ ¬a))",
                format!("{}", n2().to_basic_ops())
            );
            assert_eq!("¬((a ∨ ¬a) ∧ ¬c)", format!("{}", n3().to_basic_ops()));
        })
    }

    #[test]
    fn test_and() {
        session(|| {
            assert_eq!("(¬a ∧ (b ∧ (¬b ∨ a)))", format!("{}", a1().to_basic_ops()));
            assert_eq!("(a ∧ ¬a)", format!("{}", a2().to_basic_ops()));
            assert_eq!("((a ∨ ¬a) ∧ b)", format!("{}", a3().to_basic_ops()));
        })
    }

    #[test]
    fn test_or() {
        session(|| {
            assert_eq!("(a ∨ b)", format!("{}", o1().to_basic_ops()));
            assert_eq!(
                "((a ∨ ¬b) ∨ ((a ∧ b) ∨ (¬a ∧ ¬b)))",
                format!("{}", o2().to_basic_ops())
            );
            assert_eq!(
                "(¬(a ∧ b) ∨ ¬(¬b ∨ ¬b))",
                format!("{}", o3().to_basic_ops())
            );
        })
    }
}
