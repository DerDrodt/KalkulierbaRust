use std::{collections::HashSet, fmt};

use crate::{logic::LogicNode, Symbol};

use super::visitor::MutLogicNodeVisitor;

enum QuantifierType {
    All,
    Ex,
}

pub fn prenex_normal(n: &LogicNode) -> Result<LogicNode, PrenixNormalFormErr> {
    let mut instance = PrenexNormalForm::new();
    let mut n = instance.visit(n)?;

    for (ty, s) in instance.quants.iter().rev() {
        let q = match ty {
            QuantifierType::All => LogicNode::All,
            QuantifierType::Ex => LogicNode::Ex,
        };
        n = q(*s, Box::new(n));
    }

    Ok(n)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PrenixNormalFormErr(Symbol);

impl fmt::Display for PrenixNormalFormErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Prenex Normal Form conversion encountered double-binding of variable {}",
            self.0
        )
    }
}

pub struct PrenexNormalForm {
    seen: HashSet<Symbol>,
    quants: Vec<(QuantifierType, Symbol)>,
}

impl PrenexNormalForm {
    pub fn new() -> Self {
        Self {
            seen: HashSet::new(),
            quants: Vec::new(),
        }
    }
}

impl MutLogicNodeVisitor for PrenexNormalForm {
    type Ret = Result<LogicNode, PrenixNormalFormErr>;

    fn visit_var(&mut self, _: Symbol) -> Self::Ret {
        panic!()
    }

    fn visit_not(&mut self, child: &crate::logic::LogicNode) -> Self::Ret {
        Ok(LogicNode::Not(Box::new(self.visit(child)?)))
    }

    fn visit_and(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::And(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_or(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Or(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_impl(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Impl(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_equiv(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Equiv(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_rel(&mut self, spelling: Symbol, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        Ok(LogicNode::Rel(spelling, args.clone()))
    }

    fn visit_all(&mut self, var: Symbol, child: &crate::logic::LogicNode) -> Self::Ret {
        if self.seen.contains(&var) {
            Err(PrenixNormalFormErr(var))
        } else {
            self.quants.push((QuantifierType::All, var));
            self.seen.insert(var);
            self.visit(child)
        }
    }

    fn visit_ex(&mut self, var: Symbol, child: &crate::logic::LogicNode) -> Self::Ret {
        if self.seen.contains(&var) {
            Err(PrenixNormalFormErr(var))
        } else {
            self.quants.push((QuantifierType::Ex, var));
            self.seen.insert(var);
            self.visit(child)
        }
    }
}
