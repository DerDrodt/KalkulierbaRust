use std::collections::HashMap;

use crate::symbol::Symbol;

use super::visitor::{MutFOTermVisitor, MutLogicNodeVisitor};
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

impl<'a> MutLogicNodeVisitor for ToBasicOps {
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
    use crate::{
        logic::{fo::FOTerm, LogicNode},
        session,
    };

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

    macro_rules! rel {
        ($name:expr, $( $arg:expr ),*) => {
            LogicNode::Rel(Symbol::intern($name), vec![$($arg),*])
        };
    }

    macro_rules! all {
        ($name:expr, $child:expr $(, $arg:expr )*) => {
            LogicNode::All(Symbol::intern($name), Box::new($child), vec![$(Symbol::intern($arg)),*])
        };
    }

    macro_rules! ex {
        ($name:expr, $child:expr $(, $arg:expr )*) => {
            LogicNode::Ex(Symbol::intern($name), Box::new($child), vec![$(Symbol::intern($arg)),*])
        };
    }

    macro_rules! func {
        ($name:expr, $( $arg:expr ),*) => {
            FOTerm::Function(Symbol::intern($name), vec![$($arg),*])
        };
    }

    fn q_var(s: &str) -> FOTerm {
        FOTerm::QuantifiedVar(Symbol::intern(s))
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

    fn u1() -> LogicNode {
        all!("X", or(var("X"), not(var("X"))))
    }

    fn u2() -> LogicNode {
        all!(
            "X",
            ex!(
                "Y",
                all!(
                    "Z",
                    and(
                        rel!("R", q_var("X"), q_var("Y")),
                        rel!("R", q_var("Y"), q_var("Z"))
                    )
                )
            )
        )
    }

    fn u3() -> LogicNode {
        all!(
            "Number1",
            ex!(
                "Number2",
                rel!("Greater", q_var("Number1"), q_var("Number2"))
            )
        )
    }

    fn e1() -> LogicNode {
        ex!("C", not(rel!("Q", q_var("C"))))
    }

    fn e2() -> LogicNode {
        ex!(
            "X",
            all!(
                "Y",
                rel!("=", q_var("Y"), func!("m", q_var("X"), q_var("Y")))
            )
        )
    }

    fn e3() -> LogicNode {
        ex!(
            "El",
            imp(rel!("P", q_var("El")), all!("Y", rel!("P", q_var("Y"))))
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

    #[test]
    fn test_all() {
        session(|| {
            assert_eq!("(∀X: (X ∨ ¬X))", format!("{}", u1().to_basic_ops()));
            assert_eq!(
                "(∀X: (∃Y: (∀Z: (R(X, Y) ∧ R(Y, Z)))))",
                format!("{}", u2().to_basic_ops())
            );
            assert_eq!(
                "(∀Number1: (∃Number2: Greater(Number1, Number2)))",
                format!("{}", u3().to_basic_ops())
            );
        })
    }

    #[test]
    fn test_ex() {
        session(|| {
            assert_eq!("(∃C: ¬Q(C))", format!("{}", e1().to_basic_ops()));
            assert_eq!(
                "(∃X: (∀Y: =(Y, m(X, Y))))",
                format!("{}", e2().to_basic_ops())
            );
            assert_eq!(
                "(∃El: (¬P(El) ∨ (∀Y: P(Y))))",
                format!("{}", e3().to_basic_ops())
            );
        })
    }
}
