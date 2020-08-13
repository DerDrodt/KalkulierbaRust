use super::super::{FOTerm, LogicNode};

pub trait LogicNodeVisitor {
    type Ret;

    fn visit(&mut self, node: &LogicNode) -> Self::Ret {
        match node {
            LogicNode::Var(s) => self.visit_var(s),
            LogicNode::Not(c) => self.visit_not(c),
            LogicNode::And(left, right) => self.visit_and(left, right),
            LogicNode::Or(left, right) => self.visit_or(left, right),
            LogicNode::Impl(left, right) => self.visit_impl(left, right),
            LogicNode::Equiv(left, right) => self.visit_equiv(left, right),
            /* LogicNode::Rel(s, args) => self.visit_rel(s, args),
            LogicNode::All(var, child, bound_vars) => self.visit_all(var, child, bound_vars),
            LogicNode::Ex(var, child, bound_vars) => self.visit_ex(var, child, bound_vars), */
        }
    }

    fn visit_var(&mut self, spelling: &String) -> Self::Ret;

    fn visit_not(&mut self, child: &LogicNode) -> Self::Ret;

    fn visit_and(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret;

    fn visit_or(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret;

    fn visit_impl(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret;

    fn visit_equiv(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret;

    fn visit_rel(&mut self, spelling: &String, args: &Vec<FOTerm>) -> Self::Ret;

    fn visit_all(&mut self, var: &String, child: &LogicNode, bound_vars: &Vec<String>)
        -> Self::Ret;

    fn visit_ex(&mut self, var: &String, child: &LogicNode, bound_vars: &Vec<String>) -> Self::Ret;
}
