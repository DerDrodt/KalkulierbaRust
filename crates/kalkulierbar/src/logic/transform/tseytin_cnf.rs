use crate::{
    clause::{Atom, Clause, ClauseSet},
    logic::LogicNode,
    symbol::Symbol,
};

use super::visitor::MutLogicNodeVisitor;

pub struct TseytinCNF {
    pub clause_set: ClauseSet<Symbol>,
    idx: u32,
}

impl TseytinCNF {
    pub fn new() -> Self {
        Self {
            clause_set: ClauseSet::new(Vec::new()),
            idx: 0,
        }
    }

    #[inline]
    fn name<'a>(&self, kind: &'a str) -> Symbol {
        Symbol::intern(&format!("{}{}", kind, self.idx))
    }

    pub fn node_name<'n>(&self, node: &'n LogicNode) -> Symbol {
        let name = match node {
            LogicNode::Not(_) => "not",
            LogicNode::And(..) => "and",
            LogicNode::Or(..) => "or",
            LogicNode::Impl(..) => "impl",
            LogicNode::Equiv(..) => "equiv",
            LogicNode::Var(spelling) => return Symbol::intern(&format!("var{}", spelling)),
            _ => panic!("Cannot create CNF of FO formula"),
        };

        self.name(name)
    }
}

impl MutLogicNodeVisitor for TseytinCNF {
    type Ret = ();

    fn visit_var(&mut self, _: Symbol) -> Self::Ret {
        self.idx += 1;
    }

    fn visit_not(&mut self, child: &LogicNode) -> Self::Ret {
        let self_var = self.name("not");
        self.idx += 1;
        let child_var = self.node_name(child);
        self.visit(child);

        let clause_a: Clause<Symbol> =
            Clause::new(vec![Atom::new(child_var, true), Atom::new(self_var, true)]);

        let clause_b = Clause::new(vec![
            Atom::new(child_var, false),
            Atom::new(self_var, false),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
    }

    fn visit_and(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        let self_var = self.name("and");
        self.idx += 1;
        let left_var = self.node_name(left);
        self.visit(left);
        let right_var = self.node_name(right);
        self.visit(right);

        let clause_a = Clause::new(vec![Atom::new(left_var, false), Atom::new(self_var, true)]);
        let clause_b = Clause::new(vec![Atom::new(right_var, false), Atom::new(self_var, true)]);
        let clause_c = Clause::new(vec![
            Atom::new(left_var, true),
            Atom::new(right_var, true),
            Atom::new(self_var, false),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
        self.clause_set.add(clause_c);
    }

    fn visit_or(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        let self_var = self.name("or");
        self.idx += 1;
        let left_var = self.node_name(left);
        self.visit(left);
        let right_var = self.node_name(right);
        self.visit(right);

        let clause_a = Clause::new(vec![Atom::new(left_var, true), Atom::new(self_var, false)]);
        let clause_b = Clause::new(vec![Atom::new(right_var, true), Atom::new(self_var, false)]);
        let clause_c = Clause::new(vec![
            Atom::new(left_var, false),
            Atom::new(right_var, false),
            Atom::new(self_var, true),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
        self.clause_set.add(clause_c);
    }

    fn visit_impl(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        let self_var = self.name("impl");
        self.idx += 1;
        let left_var = self.node_name(left);
        self.visit(left);
        let right_var = self.node_name(right);
        self.visit(right);

        let clause_a = Clause::new(vec![Atom::new(left_var, false), Atom::new(self_var, false)]);
        let clause_b = Clause::new(vec![Atom::new(right_var, true), Atom::new(self_var, false)]);
        let clause_c = Clause::new(vec![
            Atom::new(left_var, true),
            Atom::new(right_var, false),
            Atom::new(self_var, true),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
        self.clause_set.add(clause_c);
    }

    fn visit_equiv(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        let self_var = self.name("equiv");
        self.idx += 1;
        let left_var = self.node_name(left);
        self.visit(left);
        let right_var = self.node_name(right);
        self.visit(right);

        let clause_a = Clause::new(vec![
            Atom::new(left_var, false),
            Atom::new(right_var, true),
            Atom::new(self_var, true),
        ]);
        let clause_b = Clause::new(vec![
            Atom::new(left_var, true),
            Atom::new(right_var, false),
            Atom::new(self_var, true),
        ]);
        let clause_c = Clause::new(vec![
            Atom::new(left_var, true),
            Atom::new(right_var, true),
            Atom::new(self_var, false),
        ]);
        let clause_d = Clause::new(vec![
            Atom::new(left_var, false),
            Atom::new(right_var, false),
            Atom::new(self_var, false),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
        self.clause_set.add(clause_c);
        self.clause_set.add(clause_d);
    }

    fn visit_rel(&mut self, _spelling: Symbol, _args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }

    fn visit_all(&mut self, _var: Symbol, _child: &LogicNode) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }

    fn visit_ex(&mut self, _var: Symbol, _child: &LogicNode) -> Self::Ret {
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
            assert_eq!("{vara}", format!("{}", v1().tseytin_cnf().unwrap()));
            assert_eq!("{varMyTestVar}", format!("{}", v2().tseytin_cnf().unwrap()));
            assert_eq!("{varMyT35tV4r}", format!("{}", v3().tseytin_cnf().unwrap()));
        })
    }

    #[test]
    fn test_not() {
        session(|| {
            assert_eq!(
                "{not0}, {!vara, !not0}, {vara, not0}",
                format!("{}", n1().tseytin_cnf().unwrap())
            );
            assert_eq!("{not0}, {!varb, !not3}, {varb, not3}, {!not3, !not2}, {not3, not2}, {not2, !vara, !equiv1}, {!not2, vara, !equiv1}, {!not2, !vara, equiv1}, {not2, vara, equiv1}, {!equiv1, !not0}, {equiv1, not0}", format!("{}", n2().tseytin_cnf().unwrap()));
            assert_eq!("{not0}, {!vara, !not4}, {vara, not4}, {!vara, or2}, {!not4, or2}, {vara, not4, !or2}, {!varc, !not6}, {varc, not6}, {or2, !and1}, {not6, !and1}, {!or2, !not6, and1}, {!and1, !not0}, {and1, not0}", format!("{}", n3().tseytin_cnf().unwrap()));
        })
    }

    #[test]
    fn test_and() {
        session(|| {
            assert_eq!(
                "{and0}, {!vara, !not1}, {vara, not1}, {varb, impl5}, {!vara, impl5}, {!varb, vara, !impl5}, {varb, !and3}, {impl5, !and3}, {!varb, !impl5, and3}, {not1, !and0}, {and3, !and0}, {!not1, !and3, and0}",
                format!("{}", a1().tseytin_cnf().unwrap())
            );
            assert_eq!("{and0}, {!vara, !not2}, {vara, not2}, {vara, !and0}, {not2, !and0}, {!vara, !not2, and0}", format!("{}", a2().tseytin_cnf().unwrap()));
            assert_eq!("{and0}, {!vara, !not3}, {vara, not3}, {!vara, or1}, {!not3, or1}, {vara, not3, !or1}, {or1, !and0}, {varb, !and0}, {!or1, !varb, and0}", format!("{}", a3().tseytin_cnf().unwrap()));
        })
    }

    #[test]
    fn test_or() {
        session(|| {
            assert_eq!(
                "{or0}, {!vara, or0}, {!varb, or0}, {vara, varb, !or0}",
                format!("{}", o1().tseytin_cnf().unwrap())
            );
            assert_eq!("{or0}, {!varb, !not3}, {varb, not3}, {!vara, or1}, {!not3, or1}, {vara, not3, !or1}, {vara, !varb, !equiv5}, {!vara, varb, !equiv5}, {!vara, !varb, equiv5}, {vara, varb, equiv5}, {!or1, or0}, {!equiv5, or0}, {or1, equiv5, !or0}", format!("{}", o2().tseytin_cnf().unwrap()));
            assert_eq!("{or0}, {vara, !and2}, {varb, !and2}, {!vara, !varb, and2}, {!and2, !not1}, {and2, not1}, {!varb, !not8}, {varb, not8}, {varb, impl6}, {!not8, impl6}, {!varb, not8, !impl6}, {!impl6, !not5}, {impl6, not5}, {!not1, or0}, {!not5, or0}, {not1, not5, !or0}", format!("{}", o3().tseytin_cnf().unwrap()));
        })
    }

    #[test]
    #[should_panic]
    fn test_all() {
        u1().tseytin_cnf().unwrap();
    }

    #[test]
    #[should_panic]
    fn test_ex() {
        e1().tseytin_cnf().unwrap();
    }
}
