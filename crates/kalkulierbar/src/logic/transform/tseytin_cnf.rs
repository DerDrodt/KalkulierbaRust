use crate::{
    clause::{Atom, Clause, ClauseSet},
    logic::LogicNode,
    symbol::Symbol,
};

use super::visitor::LogicNodeVisitor;

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

impl LogicNodeVisitor for TseytinCNF {
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

    fn visit_all(
        &mut self,
        _var: Symbol,
        _child: &LogicNode,
        _bound_vars: &Vec<Symbol>,
    ) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }

    fn visit_ex(
        &mut self,
        _var: Symbol,
        _child: &LogicNode,
        _bound_vars: &Vec<Symbol>,
    ) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }
}
