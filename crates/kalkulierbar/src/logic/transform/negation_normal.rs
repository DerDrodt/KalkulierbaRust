use crate::logic::LogicNode;
use crate::symbol::Symbol;

use super::visitor::LogicNodeVisitor;

pub fn negation_normal_form(formula: LogicNode) -> Result<LogicNode, &'static str> {
    NegationNormalForm.visit(&formula.to_basic_ops())
}

struct NegationNormalForm;

impl LogicNodeVisitor for NegationNormalForm {
    type Ret = Result<LogicNode, &'static str>;

    fn visit_var(&self, _: Symbol) -> Self::Ret {
        Err("Unknown LogicNode encountered during Negation Normal Form transformation")
    }

    fn visit_not(&self, child: &crate::logic::LogicNode) -> Self::Ret {
        match child {
            LogicNode::Not(c) => self.visit(c),
            LogicNode::And(l, r) => {
                let n = LogicNode::Or(
                    LogicNode::Not(l.clone()).into(),
                    LogicNode::Not(r.clone()).into(),
                );
                Ok(n.into())
            }
            LogicNode::Or(l, r) => {
                let n = LogicNode::And(
                    LogicNode::Not(l.clone()).into(),
                    LogicNode::Not(r.clone()).into(),
                );
                Ok(n.into())
            }
            LogicNode::Rel(name, args) => Ok(LogicNode::Rel(*name, args.clone())),
            LogicNode::All(var, c, bound) => Ok(LogicNode::Ex(
                *var,
                self.visit(&LogicNode::Not(c.clone()))?.into(),
                bound.clone(),
            )),
            LogicNode::Ex(var, c, bound) => Ok(LogicNode::All(
                *var,
                self.visit(&LogicNode::Not(c.clone()))?.into(),
                bound.clone(),
            )),
            _ => Err("Unknown LogicNode encountered during Negation Normal Form transformation"),
        }
    }

    fn visit_and(
        &self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::And(
            self.visit(left)?.into(),
            self.visit(right)?.into(),
        ))
    }

    fn visit_or(
        &self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Or(
            self.visit(left)?.into(),
            self.visit(right)?.into(),
        ))
    }

    fn visit_impl(
        &self,
        _left: &crate::logic::LogicNode,
        _right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Err("Unknown LogicNode encountered during Negation Normal Form transformation")
    }

    fn visit_equiv(
        &self,
        _left: &crate::logic::LogicNode,
        _right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Err("Unknown LogicNode encountered during Negation Normal Form transformation")
    }

    fn visit_rel(&self, name: Symbol, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        Ok(LogicNode::Rel(name, args.clone()))
    }

    fn visit_all(
        &self,
        var: Symbol,
        child: &crate::logic::LogicNode,
        bound_vars: &Vec<Symbol>,
    ) -> Self::Ret {
        Ok(LogicNode::All(
            var,
            self.visit(child)?.into(),
            bound_vars.clone(),
        ))
    }

    fn visit_ex(
        &self,
        var: Symbol,
        child: &crate::logic::LogicNode,
        bound_vars: &Vec<Symbol>,
    ) -> Self::Ret {
        Ok(LogicNode::Ex(
            var,
            self.visit(child)?.into(),
            bound_vars.clone(),
        ))
    }
}
