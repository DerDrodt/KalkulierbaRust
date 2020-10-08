use std::fmt;

use crate::{
    clause::{Atom, Clause, ClauseSet},
    logic::LogicNode,
};

use super::visitor::LogicNodeVisitor;

pub struct TseytinCNF<L: std::clone::Clone + std::fmt::Display> {
    pub clause_set: ClauseSet<L>,
    idx: u32,
}

impl<'a, L> TseytinCNF<L>
where
    L: fmt::Display + Copy + From<(&'a str, &'a str)> + From<(&'a str, u32)>,
{
    pub fn new() -> Self {
        Self {
            clause_set: ClauseSet::new(Vec::new()),
            idx: 0,
        }
    }

    #[inline]
    fn name(&self, kind: &'a str) -> L {
        (kind, self.idx).into()
    }

    pub fn node_name<'n>(&self, node: &'n LogicNode<'a>) -> L {
        let name = match node {
            LogicNode::Not(_) => "not",
            LogicNode::And(..) => "and",
            LogicNode::Or(..) => "or",
            LogicNode::Impl(..) => "impl",
            LogicNode::Equiv(..) => "equiv",
            LogicNode::Var(spelling) => return ("var", *spelling).into(),
            _ => panic!("Cannot create CNF of FO formula"),
        };

        self.name(name)
    }
}

impl<'a, L> LogicNodeVisitor<'a> for TseytinCNF<L>
where
    L: fmt::Display + Copy + From<(&'a str, &'a str)> + From<(&'a str, u32)>,
{
    type Ret = ();

    fn visit_var(&mut self, _: &'a str) -> Self::Ret {
        self.idx += 1;
    }

    fn visit_not(&mut self, child: &LogicNode<'a>) -> Self::Ret {
        let self_var = self.name("not");
        self.idx += 1;
        let child_var = self.node_name(child);
        self.visit(child);

        let clause_a: Clause<L> =
            Clause::new(vec![Atom::new(child_var, true), Atom::new(self_var, true)]);

        let clause_b = Clause::new(vec![
            Atom::new(child_var, false),
            Atom::new(self_var, false),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
    }

    fn visit_and(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret {
        let self_var = self.name("and");
        self.idx += 1;
        let left_var = self.node_name(left);
        self.visit(left);
        let right_var = self.node_name(right);
        self.visit(right);

        let clause_a = Clause::new(vec![
            Atom::new(left_var.clone(), false),
            Atom::new(self_var.clone(), true),
        ]);
        let clause_b = Clause::new(vec![
            Atom::new(right_var.clone(), false),
            Atom::new(self_var.clone(), true),
        ]);
        let clause_c = Clause::new(vec![
            Atom::new(left_var.clone(), true),
            Atom::new(right_var.clone(), true),
            Atom::new(self_var.clone(), false),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
        self.clause_set.add(clause_c);
    }

    fn visit_or(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret {
        let self_var = self.name("or");
        self.idx += 1;
        let left_var = self.node_name(left);
        self.visit(left);
        let right_var = self.node_name(right);
        self.visit(right);

        let clause_a = Clause::new(vec![
            Atom::new(left_var.clone(), true),
            Atom::new(self_var.clone(), false),
        ]);
        let clause_b = Clause::new(vec![
            Atom::new(right_var.clone(), true),
            Atom::new(self_var.clone(), false),
        ]);
        let clause_c = Clause::new(vec![
            Atom::new(left_var.clone(), false),
            Atom::new(right_var.clone(), false),
            Atom::new(self_var.clone(), true),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
        self.clause_set.add(clause_c);
    }

    fn visit_impl(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret {
        let self_var = self.name("impl");
        self.idx += 1;
        let left_var = self.node_name(left);
        self.visit(left);
        let right_var = self.node_name(right);
        self.visit(right);

        let clause_a = Clause::new(vec![
            Atom::new(left_var.clone(), false),
            Atom::new(self_var.clone(), false),
        ]);
        let clause_b = Clause::new(vec![
            Atom::new(right_var.clone(), true),
            Atom::new(self_var.clone(), false),
        ]);
        let clause_c = Clause::new(vec![
            Atom::new(left_var.clone(), true),
            Atom::new(right_var.clone(), false),
            Atom::new(self_var.clone(), true),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
        self.clause_set.add(clause_c);
    }

    fn visit_equiv(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret {
        let self_var = self.name("equiv");
        self.idx += 1;
        let left_var = self.node_name(left);
        self.visit(left);
        let right_var = self.node_name(right);
        self.visit(right);

        let clause_a = Clause::new(vec![
            Atom::new(left_var.clone(), false),
            Atom::new(right_var.clone(), true),
            Atom::new(self_var.clone(), true),
        ]);
        let clause_b = Clause::new(vec![
            Atom::new(left_var.clone(), true),
            Atom::new(right_var.clone(), false),
            Atom::new(self_var.clone(), true),
        ]);
        let clause_c = Clause::new(vec![
            Atom::new(left_var.clone(), true),
            Atom::new(right_var.clone(), true),
            Atom::new(self_var.clone(), false),
        ]);
        let clause_d = Clause::new(vec![
            Atom::new(left_var.clone(), false),
            Atom::new(right_var.clone(), false),
            Atom::new(self_var.clone(), false),
        ]);
        self.clause_set.add(clause_a);
        self.clause_set.add(clause_b);
        self.clause_set.add(clause_c);
        self.clause_set.add(clause_d);
    }

    fn visit_rel(
        &mut self,
        _spelling: &'a str,
        _args: &Vec<crate::logic::fo::FOTerm<'a>>,
    ) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }

    fn visit_all(
        &mut self,
        _var: &'a str,
        _child: &LogicNode<'a>,
        _bound_vars: &Vec<&'a str>,
    ) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }

    fn visit_ex(
        &mut self,
        _var: &'a str,
        _child: &LogicNode<'a>,
        _bound_vars: &Vec<&'a str>,
    ) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }
}
