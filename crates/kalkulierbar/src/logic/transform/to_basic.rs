use std::collections::HashMap;

use crate::KStr;

use super::visitor::{FOTermVisitor, LogicNodeVisitor};
use super::{super::LogicNode, term_manipulator::QuantifierLinker};

pub struct ToBasicOps {
    quantifiers: HashMap<KStr, Vec<KStr>>,
}

impl ToBasicOps {
    pub fn new() -> Self {
        Self {
            quantifiers: HashMap::new(),
        }
    }
}

impl<'a> LogicNodeVisitor for ToBasicOps {
    type Ret = LogicNode;

    fn visit_var(&mut self, spelling: &KStr) -> Self::Ret {
        LogicNode::Var(spelling.clone())
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

    fn visit_rel(&mut self, spelling: &KStr, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        let mut linker = QuantifierLinker::new(&mut self.quantifiers);

        for arg in args {
            linker.visit(arg).unwrap();
        }

        LogicNode::Rel(spelling.clone(), args.clone())
    }

    fn visit_all(&mut self, var: &KStr, child: &LogicNode, _: &Vec<KStr>) -> Self::Ret {
        self.quantifiers.insert(var.clone(), Vec::new());
        let child = self.visit(child).into();
        let bound = self.quantifiers.remove(var).unwrap();
        LogicNode::All(var.clone(), child, bound)
    }

    fn visit_ex(&mut self, var: &KStr, child: &LogicNode, _: &Vec<KStr>) -> Self::Ret {
        self.quantifiers.insert(var.clone(), Vec::new());
        let child = self.visit(child).into();
        let bound = self.quantifiers.remove(var).unwrap();
        LogicNode::Ex(var.clone(), child, bound)
    }
}
