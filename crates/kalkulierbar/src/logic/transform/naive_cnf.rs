use crate::{
    clause::{Atom, Clause, ClauseSet},
    logic::LogicNode,
    symbol::Symbol,
};

use super::visitor::MutLogicNodeVisitor;

pub struct NaiveCNF;

impl NaiveCNF {
    pub fn new() -> Self {
        Self {}
    }
}

impl Default for NaiveCNF {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug)]
pub struct FormulaConversionErr;

impl MutLogicNodeVisitor for NaiveCNF {
    type Ret = Result<ClauseSet<Symbol>, FormulaConversionErr>;

    fn visit_var(&mut self, spelling: Symbol) -> Self::Ret {
        let a = Atom::new(spelling, false);
        let c = Clause::new(vec![a]);
        Ok(ClauseSet::new(vec![c]))
    }

    fn visit_not(&mut self, child: &crate::logic::LogicNode) -> Self::Ret {
        match child {
            crate::logic::LogicNode::Var(s) => {
                let a = Atom::new(*s, true);
                let c = Clause::new(vec![a]);
                Ok(ClauseSet::new(vec![c]))
            }
            crate::logic::LogicNode::Not(c) => self.visit(c),
            crate::logic::LogicNode::And(l, r) => self.visit(&LogicNode::Or(
                LogicNode::Not(l.clone()).into(),
                LogicNode::Not(r.clone()).into(),
            )),
            crate::logic::LogicNode::Or(l, r) => self.visit(&LogicNode::And(
                LogicNode::Not(l.clone()).into(),
                LogicNode::Not(r.clone()).into(),
            )),
            crate::logic::LogicNode::Impl(l, r) => {
                self.visit(&LogicNode::And(l.clone(), LogicNode::Not(r.clone()).into()))
            }
            crate::logic::LogicNode::Equiv(l, r) => {
                let impl_1 = LogicNode::Impl(l.clone(), r.clone()).into();
                let impl_2 = LogicNode::Impl(r.clone(), l.clone()).into();

                self.visit(&LogicNode::Not(LogicNode::And(impl_1, impl_2).into()))
            }
            _ => panic!("Cannot create CNF of FO formula"),
        }
    }

    fn visit_and(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        let mut left = self.visit(left)?;
        let right = self.visit(right)?;
        left.unite(&right);
        Ok(left)
    }

    fn visit_or(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        let left: Vec<Clause<Symbol>> = self.visit(left)?.into();
        let right: Vec<Clause<Symbol>> = self.visit(right)?.into();

        if left.len() * right.len() > crate::CNF_BLOWUP_LIMIT as usize {
            Err(FormulaConversionErr)
        } else {
            let mut clauses = vec![];
            for lc in left.into_iter() {
                for rc in right.clone().into_iter() {
                    let mut atoms: Vec<Atom<Symbol>> = lc.clone().into();
                    atoms.append(&mut rc.into());
                    let clause = Clause::new(atoms);
                    clauses.push(clause);
                }
            }

            Ok(ClauseSet::new(clauses))
        }
    }

    fn visit_impl(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        let n = LogicNode::Impl(left.clone().into(), right.clone().into()).to_basic_ops();
        self.visit(&n)
    }

    fn visit_equiv(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        let n = LogicNode::Equiv(left.clone().into(), right.clone().into()).to_basic_ops();
        self.visit(&n)
    }

    fn visit_rel(&mut self, _spelling: Symbol, _args: &[crate::logic::fo::FOTerm]) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }

    fn visit_all(&mut self, _var: Symbol, _child: &crate::logic::LogicNode) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }

    fn visit_ex(&mut self, _var: Symbol, _child: &crate::logic::LogicNode) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{logic::fo::FOTerm, session};

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

    fn all(name: &str, child: LogicNode) -> LogicNode {
        LogicNode::All(Symbol::intern(name), Box::new(child))
    }

    fn ex(name: &str, child: LogicNode) -> LogicNode {
        LogicNode::Ex(Symbol::intern(name), Box::new(child))
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
        all("X", or(var("X"), not(var("X"))))
    }

    fn e1() -> LogicNode {
        ex("C", not(rel!("Q", q_var("C"))))
    }

    #[test]
    fn test_var() {
        session(|| {
            assert_eq!("{a}", format!("{}", v1().naive_cnf().unwrap()));
            assert_eq!("{MyTestVar}", format!("{}", v2().naive_cnf().unwrap()));
            assert_eq!("{MyT35tV4r}", format!("{}", v3().naive_cnf().unwrap()));
        })
    }

    #[test]
    fn test_not() {
        session(|| {
            assert_eq!("{!a}", format!("{}", n1().naive_cnf().unwrap()));
            assert_eq!(
                "{b, a}, {b, !b}, {!a, a}, {!a, !b}",
                format!("{}", n2().naive_cnf().unwrap())
            );
            assert_eq!("{!a, c}, {a, c}", format!("{}", n3().naive_cnf().unwrap()));
        })
    }

    #[test]
    fn test_and() {
        session(|| {
            assert_eq!(
                "{!a}, {b}, {!b, a}",
                format!("{}", a1().naive_cnf().unwrap())
            );
            assert_eq!("{a}, {!a}", format!("{}", a2().naive_cnf().unwrap()));
            assert_eq!("{a, !a}, {b}", format!("{}", a3().naive_cnf().unwrap()));
        })
    }

    #[test]
    fn test_or() {
        session(|| {
            assert_eq!("{a, b}", format!("{}", o1().naive_cnf().unwrap()));
            assert_eq!(
                "{a, !b, a, !a}, {a, !b, a, !b}, {a, !b, b, !a}, {a, !b, b, !b}",
                format!("{}", o2().naive_cnf().unwrap())
            );
            assert_eq!(
                "{!a, !b, b}, {!a, !b, b}",
                format!("{}", o3().naive_cnf().unwrap())
            );
        })
    }

    #[test]
    #[should_panic]
    fn test_all() {
        u1().naive_cnf().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_ex() {
        e1().naive_cnf().unwrap();
    }
}
