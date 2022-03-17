use crate::logic::LogicNode;
use crate::symbol::Symbol;

use super::transformer::LogicNodeTransformer;

pub fn negation_normal_form(formula: LogicNode) -> Result<LogicNode, &'static str> {
    NegationNormalForm.visit(formula.to_basic_ops())
}

struct NegationNormalForm;

impl LogicNodeTransformer for NegationNormalForm {
    type Ret = Result<LogicNode, &'static str>;

    fn visit_var(&self, _: Symbol) -> Self::Ret {
        Err("Unknown LogicNode encountered during Negation Normal Form transformation")
    }

    fn visit_not(&self, child: crate::logic::LogicNode) -> Self::Ret {
        match child {
            LogicNode::Not(c) => self.visit(*c),
            LogicNode::And(l, r) => {
                let n = LogicNode::Or(LogicNode::Not(l).into(), LogicNode::Not(r).into());
                Ok(self.visit(n)?)
            }
            LogicNode::Or(l, r) => {
                let n = LogicNode::And(LogicNode::Not(l).into(), LogicNode::Not(r).into());
                Ok(self.visit(n)?)
            }
            LogicNode::Rel(name, args) => Ok(LogicNode::Not(Box::new(LogicNode::Rel(name, args)))),
            LogicNode::All(var, c) => Ok(LogicNode::Ex(var, self.visit(LogicNode::Not(c))?.into())),
            LogicNode::Ex(var, c) => Ok(LogicNode::All(var, self.visit(LogicNode::Not(c))?.into())),
            _ => Err("Unknown LogicNode encountered during Negation Normal Form transformation"),
        }
    }

    fn visit_and(
        &self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::And(
            self.visit(left)?.into(),
            self.visit(right)?.into(),
        ))
    }

    fn visit_or(&self, left: crate::logic::LogicNode, right: crate::logic::LogicNode) -> Self::Ret {
        Ok(LogicNode::Or(
            self.visit(left)?.into(),
            self.visit(right)?.into(),
        ))
    }

    fn visit_impl(
        &self,
        _left: crate::logic::LogicNode,
        _right: crate::logic::LogicNode,
    ) -> Self::Ret {
        Err("Unknown LogicNode encountered during Negation Normal Form transformation")
    }

    fn visit_equiv(
        &self,
        _left: crate::logic::LogicNode,
        _right: crate::logic::LogicNode,
    ) -> Self::Ret {
        Err("Unknown LogicNode encountered during Negation Normal Form transformation")
    }

    fn visit_rel(&self, name: Symbol, args: Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        Ok(LogicNode::Rel(name, args.to_vec()))
    }

    fn visit_all(&self, var: Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        Ok(LogicNode::All(var, self.visit(child)?.into()))
    }

    fn visit_ex(&self, var: Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        Ok(LogicNode::Ex(var, self.visit(child)?.into()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse::fo::parse_fo_formula, session};

    #[test]
    fn valid() {
        session(|| {
            let formulas = [
                ("R(a) -> R(b)", "(¬R(a) ∨ R(b))"),
                ("!(R(a) | R(b))", "(¬R(a) ∧ ¬R(b))"),
                ("!(R(a) & R(b))", "(¬R(a) ∨ ¬R(b))"),
                ("!(!R(a))", "R(a)"),
                ("!\\ex A : R(A)", "(∀A: ¬R(A))"),
                ("!\\all A : R(A)", "(∃A: ¬R(A))"),
            ];

            for (f, e) in formulas {
                let parsed = parse_fo_formula(f).unwrap();
                let nnf = negation_normal_form(parsed).unwrap();
                assert_eq!(e, nnf.to_string());
            }
        })
    }
}
