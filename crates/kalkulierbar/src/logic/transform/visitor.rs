use super::super::{FOTerm, LogicNode};

use crate::symbol::Symbol;

pub trait LogicNodeVisitor {
    type Ret;

    fn visit(&mut self, node: &LogicNode) -> Self::Ret {
        match node {
            LogicNode::Var(s) => self.visit_var(*s),
            LogicNode::Not(c) => self.visit_not(&c),
            LogicNode::And(left, right) => self.visit_and(&left, &right),
            LogicNode::Or(left, right) => self.visit_or(&left, &right),
            LogicNode::Impl(left, right) => self.visit_impl(&left, &right),
            LogicNode::Equiv(left, right) => self.visit_equiv(&left, &right),
            LogicNode::Rel(s, args) => self.visit_rel(*s, args),
            LogicNode::All(var, child, bound_vars) => self.visit_all(*var, child, bound_vars),
            LogicNode::Ex(var, child, bound_vars) => self.visit_ex(*var, child, bound_vars),
        }
    }

    fn visit_var(&mut self, spelling: Symbol) -> Self::Ret;

    fn visit_not(&mut self, child: &LogicNode) -> Self::Ret;

    fn visit_and(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret;

    fn visit_or(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret;

    fn visit_impl(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret;

    fn visit_equiv(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret;

    fn visit_rel(&mut self, spelling: Symbol, args: &Vec<FOTerm>) -> Self::Ret;

    fn visit_all(&mut self, var: Symbol, child: &LogicNode, bound_vars: &Vec<Symbol>) -> Self::Ret;

    fn visit_ex(&mut self, var: Symbol, child: &LogicNode, bound_vars: &Vec<Symbol>) -> Self::Ret;
}

pub trait FOTermVisitor {
    type Ret;

    fn visit(&mut self, term: &FOTerm) -> Self::Ret {
        match term {
            FOTerm::QuantifiedVar(s) => self.visit_quantified_var(*s),
            FOTerm::Const(s) => self.visit_const(*s),
            FOTerm::Function(name, args) => self.visit_fn(*name, args),
        }
    }

    fn visit_quantified_var(&mut self, s: Symbol) -> Self::Ret;

    fn visit_const(&mut self, s: Symbol) -> Self::Ret;

    fn visit_fn(&mut self, name: Symbol, args: &Vec<FOTerm>) -> Self::Ret;
}
