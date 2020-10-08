use std::collections::HashMap;

use super::visitor::{FOTermVisitor, LogicNodeVisitor};
use super::{super::LogicNode, term_manipulator::QuantifierLinker};

pub struct ToBasicOps<'a> {
    quantifiers: HashMap<&'a str, Vec<&'a str>>,
}

impl<'a> ToBasicOps<'a> {
    pub fn new() -> Self {
        Self {
            quantifiers: HashMap::new(),
        }
    }
}

impl<'a> LogicNodeVisitor<'a> for ToBasicOps<'a> {
    type Ret = LogicNode<'a>;

    fn visit_var(&mut self, spelling: &'a str) -> Self::Ret {
        LogicNode::Var(spelling)
    }

    fn visit_not(&mut self, child: &LogicNode<'a>) -> Self::Ret {
        LogicNode::Not(self.visit(child).into())
    }

    fn visit_and(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret {
        LogicNode::And(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_or(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret {
        LogicNode::Or(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_impl(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret {
        let left = self.visit(left).into();
        let right = self.visit(right).into();
        LogicNode::Or(LogicNode::Not(left).into(), right)
    }

    fn visit_equiv(&mut self, left: &LogicNode<'a>, right: &LogicNode<'a>) -> Self::Ret {
        let left = self.visit(left);
        let right = self.visit(right);
        let not_left = LogicNode::Not(left.clone().into()).into();
        let not_right = LogicNode::Not(right.clone().into()).into();

        let both_t = LogicNode::And(left.into(), right.into()).into();
        let both_f = LogicNode::And(not_left, not_right).into();

        LogicNode::Or(both_t, both_f)
    }

    fn visit_rel(
        &mut self,
        spelling: &'a str,
        args: &Vec<crate::logic::fo::FOTerm<'a>>,
    ) -> Self::Ret {
        let mut linker = QuantifierLinker::new(&mut self.quantifiers);

        for arg in args {
            linker.visit(arg).unwrap();
        }

        LogicNode::Rel(spelling, args.clone())
    }

    fn visit_all(&mut self, var: &'a str, child: &LogicNode<'a>, _: &Vec<&'a str>) -> Self::Ret {
        self.quantifiers.insert(var, Vec::new());
        let child = self.visit(child).into();
        let bound = self.quantifiers.remove(var).unwrap();
        LogicNode::All(var, child, bound)
    }

    fn visit_ex(&mut self, var: &'a str, child: &LogicNode<'a>, _: &Vec<&'a str>) -> Self::Ret {
        self.quantifiers.insert(var, Vec::new());
        let child = self.visit(child).into();
        let bound = self.quantifiers.remove(var).unwrap();
        LogicNode::Ex(var, child, bound)
    }
}
