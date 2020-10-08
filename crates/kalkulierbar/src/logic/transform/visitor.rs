use super::super::{FOTerm, LogicNode};

pub trait LogicNodeVisitor<'a> {
    type Ret;

    fn visit(&mut self, node: &LogicNode<'a>) -> Self::Ret {
        match node {
            LogicNode::Var(s) => self.visit_var(s),
            LogicNode::Not(c) => self.visit_not(&c),
            LogicNode::And(left, right) => self.visit_and(&left, &right),
            LogicNode::Or(left, right) => self.visit_or(&left, &right),
            LogicNode::Impl(left, right) => self.visit_impl(&left, &right),
            LogicNode::Equiv(left, right) => self.visit_equiv(&left, &right),
            LogicNode::Rel(s, args) => self.visit_rel(s, args),
            LogicNode::All(var, child, bound_vars) => self.visit_all(var, child, bound_vars),
            LogicNode::Ex(var, child, bound_vars) => self.visit_ex(var, child, bound_vars),
        }
    }

    fn visit_var(&mut self, spelling: &'a str) -> Self::Ret;

    fn visit_not(&mut self, child: &LogicNode<'a>) -> Self::Ret;

    fn visit_and(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret;

    fn visit_or(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret;

    fn visit_impl(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret;

    fn visit_equiv(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret;

    fn visit_rel(&mut self, spelling: &'a str, args: &Vec<FOTerm<'a>>) -> Self::Ret;

    fn visit_all(
        &mut self,
        var: &'a str,
        child: &LogicNode<'a>,
        bound_vars: &Vec<&'a str>,
    ) -> Self::Ret;

    fn visit_ex(
        &mut self,
        var: &'a str,
        child: &LogicNode<'a>,
        bound_vars: &Vec<&'a str>,
    ) -> Self::Ret;
}

pub trait FOTermVisitor<'a> {
    type Ret;

    fn visit(&mut self, term: &FOTerm<'a>) -> Self::Ret {
        match term {
            FOTerm::QuantifiedVar(s) => self.visit_quantified_var(s),
            FOTerm::Const(s) => self.visit_const(s),
            FOTerm::Function(name, args) => self.visit_fn(name, args),
        }
    }

    fn visit_quantified_var(&mut self, s: &'a str) -> Self::Ret;

    fn visit_const(&mut self, s: &'a str) -> Self::Ret;

    fn visit_fn(&mut self, name: &'a str, args: &Vec<FOTerm<'a>>) -> Self::Ret;
}
