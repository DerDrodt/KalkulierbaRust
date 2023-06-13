use std::collections::HashMap;

use crate::{logic::LogicNode, Symbol};

use super::{
    transformer::{FOTermTransformer, LogicNodeTransformer},
    unique_vars::VariableRenamer,
};

pub fn append_suffix_selectively(n: LogicNode, s: Symbol, suffix: &str) -> LogicNode {
    let new = Symbol::intern(&format!("{s}{suffix}"));
    let map = HashMap::from([(s, new)]);
    let vr = VariableRenamer::new(&map);
    let ssa = SelectiveSuffixAppender(s, vr);
    ssa.visit(n)
}

struct SelectiveSuffixAppender<'a>(Symbol, VariableRenamer<'a>);

impl<'a> LogicNodeTransformer for SelectiveSuffixAppender<'a> {
    type Ret = LogicNode;

    fn visit_var(&self, _: Symbol) -> Self::Ret {
        panic!()
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
        LogicNode::Equiv(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_rel(&self, spelling: Symbol, args: Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        LogicNode::Rel(
            spelling,
            args.into_iter().map(|a| self.1.visit(a)).collect(),
        )
    }

    fn visit_all(&self, var: Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        // If we encounter a new quantor with the same var, we can stop, since all other instances we would find are bound by a new quantor
        if var == self.0 {
            LogicNode::All(var, child.into())
        } else {
            LogicNode::All(var, self.visit(child).into())
        }
    }

    fn visit_ex(&self, var: Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        // If we encounter a new quantor with the same var, we can stop, since all other instances we would find are bound by a new quantor
        if var == self.0 {
            LogicNode::Ex(var, child.into())
        } else {
            LogicNode::Ex(var, self.visit(child).into())
        }
    }

    fn visit_box(&self, child: LogicNode) -> Self::Ret {
        LogicNode::Box(self.visit(child).into())
    }

    fn visit_diamond(&self, child: LogicNode) -> Self::Ret {
        LogicNode::Diamond(self.visit(child).into())
    }
}
