use crate::{
    logic::{fo::FOTerm, LogicNode},
    Symbol,
};

pub trait LogicNodeTransformer {
    type Ret;

    fn visit(&self, node: LogicNode) -> Self::Ret {
        match node {
            LogicNode::Var(s) => self.visit_var(s),
            LogicNode::Not(c) => self.visit_not(*c),
            LogicNode::And(left, right) => self.visit_and(*left, *right),
            LogicNode::Or(left, right) => self.visit_or(*left, *right),
            LogicNode::Impl(left, right) => self.visit_impl(*left, *right),
            LogicNode::Equiv(left, right) => self.visit_equiv(*left, *right),
            LogicNode::Rel(s, args) => self.visit_rel(s, args),
            LogicNode::All(var, child) => self.visit_all(var, *child),
            LogicNode::Ex(var, child) => self.visit_ex(var, *child),
            LogicNode::Box(child) => self.visit_box(*child),
            LogicNode::Diamond(child) => self.visit_diamond(*child),
        }
    }

    fn visit_var(&self, spelling: Symbol) -> Self::Ret;

    fn visit_not(&self, child: LogicNode) -> Self::Ret;

    fn visit_and(&self, left: LogicNode, right: LogicNode) -> Self::Ret;

    fn visit_or(&self, left: LogicNode, right: LogicNode) -> Self::Ret;

    fn visit_impl(&self, left: LogicNode, right: LogicNode) -> Self::Ret;

    fn visit_equiv(&self, left: LogicNode, right: LogicNode) -> Self::Ret;

    fn visit_rel(&self, spelling: Symbol, args: Vec<FOTerm>) -> Self::Ret;

    fn visit_all(&self, var: Symbol, child: LogicNode) -> Self::Ret;

    fn visit_ex(&self, var: Symbol, child: LogicNode) -> Self::Ret;

    fn visit_box(&self, child: LogicNode) -> Self::Ret;

    fn visit_diamond(&self, child: LogicNode) -> Self::Ret;
}

pub trait MutLogicNodeTransformer {
    type Ret;

    fn visit(&mut self, node: LogicNode) -> Self::Ret {
        match node {
            LogicNode::Var(s) => self.visit_var(s),
            LogicNode::Not(c) => self.visit_not(*c),
            LogicNode::And(left, right) => self.visit_and(*left, *right),
            LogicNode::Or(left, right) => self.visit_or(*left, *right),
            LogicNode::Impl(left, right) => self.visit_impl(*left, *right),
            LogicNode::Equiv(left, right) => self.visit_equiv(*left, *right),
            LogicNode::Rel(s, args) => self.visit_rel(s, args),
            LogicNode::All(var, child) => self.visit_all(var, *child),
            LogicNode::Ex(var, child) => self.visit_ex(var, *child),
            LogicNode::Box(child) => self.visit_box(*child),
            LogicNode::Diamond(child) => self.visit_diamond(*child),
        }
    }

    fn visit_var(&mut self, spelling: Symbol) -> Self::Ret;

    fn visit_not(&mut self, child: LogicNode) -> Self::Ret;

    fn visit_and(&mut self, left: LogicNode, right: LogicNode) -> Self::Ret;

    fn visit_or(&mut self, left: LogicNode, right: LogicNode) -> Self::Ret;

    fn visit_impl(&mut self, left: LogicNode, right: LogicNode) -> Self::Ret;

    fn visit_equiv(&mut self, left: LogicNode, right: LogicNode) -> Self::Ret;

    fn visit_rel(&mut self, spelling: Symbol, args: Vec<FOTerm>) -> Self::Ret;

    fn visit_all(&mut self, var: Symbol, child: LogicNode) -> Self::Ret;

    fn visit_ex(&mut self, var: Symbol, child: LogicNode) -> Self::Ret;

    fn visit_box(&mut self, child: LogicNode) -> Self::Ret;

    fn visit_diamond(&mut self, child: LogicNode) -> Self::Ret;
}

pub trait FOTermTransformer {
    fn visit(&self, term: FOTerm) -> FOTerm {
        match term {
            FOTerm::QuantifiedVar(s) => self.visit_quantified_var(s),
            FOTerm::Const(s) => self.visit_const(s),
            FOTerm::Function(name, args) => self.visit_fn(name, args),
        }
    }

    fn visit_quantified_var(&self, s: Symbol) -> FOTerm;

    fn visit_const(&self, s: Symbol) -> FOTerm;

    fn visit_fn(&self, name: Symbol, args: Vec<FOTerm>) -> FOTerm;
}

pub trait MutFOTermTransformer {
    fn visit(&mut self, term: FOTerm) -> FOTerm {
        match term {
            FOTerm::QuantifiedVar(s) => self.visit_quantified_var(s),
            FOTerm::Const(s) => self.visit_const(s),
            FOTerm::Function(name, args) => self.visit_fn(name, args),
        }
    }

    fn visit_quantified_var(&mut self, s: Symbol) -> FOTerm;

    fn visit_const(&mut self, s: Symbol) -> FOTerm;

    fn visit_fn(&mut self, name: Symbol, args: Vec<FOTerm>) -> FOTerm;
}
