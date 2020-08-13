use super::super::LogicNode;
use super::visitor::LogicNodeVisitor;

enum Quantifier<'a> {
    All(&'a LogicNode),
    Ex(&'a LogicNode),
}

struct ToBasicOps<'a> {
    quantifiers: Vec<Quantifier<'a>>,
}

impl<'a> LogicNodeVisitor for ToBasicOps<'a> {
    type Ret = LogicNode;

    fn visit_var(&mut self, spelling: &String) -> Self::Ret {
        todo!()
    }
    fn visit_not(&mut self, child: &crate::logic::LogicNode) -> Self::Ret {
        todo!()
    }
    fn visit_and(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        todo!()
    }
    fn visit_or(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        todo!()
    }
    fn visit_impl(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        todo!()
    }
    fn visit_equiv(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        todo!()
    }
    fn visit_rel(&mut self, spelling: &String, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        todo!()
    }
    fn visit_all(
        &mut self,
        var: &String,
        child: &crate::logic::LogicNode,
        bound_vars: &Vec<String>,
    ) -> Self::Ret {
        todo!()
    }
    fn visit_ex(
        &mut self,
        var: &String,
        child: &crate::logic::LogicNode,
        bound_vars: &Vec<String>,
    ) -> Self::Ret {
        todo!()
    }
}
