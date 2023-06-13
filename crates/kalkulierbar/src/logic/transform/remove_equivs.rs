use crate::logic::LogicNode;

use super::transformer::LogicNodeTransformer;

pub fn remove_equivs(n: LogicNode) -> LogicNode {
    EquivRemover.visit(n)
}

struct EquivRemover;

impl LogicNodeTransformer for EquivRemover {
    type Ret = LogicNode;

    fn visit_var(&self, spelling: crate::Symbol) -> Self::Ret {
        LogicNode::Var(spelling)
    }

    fn visit_not(&self, child: crate::logic::LogicNode) -> Self::Ret {
        LogicNode::Not(self.visit(child).into())
    }

    fn visit_and(
        &self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        LogicNode::And(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_or(&self, left: crate::logic::LogicNode, right: crate::logic::LogicNode) -> Self::Ret {
        LogicNode::Or(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_impl(
        &self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        LogicNode::Impl(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_equiv(
        &self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        let left = self.visit(left);
        let right = self.visit(right);

        let i1 = LogicNode::Impl(left.clone().into(), right.clone().into());
        let i2 = LogicNode::Impl(right.into(), left.into());

        LogicNode::And(i1.into(), i2.into())
    }

    fn visit_rel(&self, spelling: crate::Symbol, args: Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        LogicNode::Rel(spelling, args)
    }

    fn visit_all(&self, var: crate::Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        LogicNode::All(var, self.visit(child).into())
    }

    fn visit_ex(&self, var: crate::Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        LogicNode::Ex(var, self.visit(child).into())
    }

    fn visit_box(&self, child: LogicNode) -> Self::Ret {
        LogicNode::Box(self.visit(child).into())
    }

    fn visit_diamond(&self, child: LogicNode) -> Self::Ret {
        LogicNode::Diamond(self.visit(child).into())
    }
}
