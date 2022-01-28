use crate::{
    clause::{Atom, Clause, ClauseSet},
    logic::LogicNode,
    symbol::Symbol,
};

use super::visitor::LogicNodeVisitor;

pub struct NaiveCNF;

impl NaiveCNF {
    pub fn new() -> Self {
        Self {}
    }
}

#[derive(Debug)]
pub struct FormulaConversionErr;

impl LogicNodeVisitor for NaiveCNF {
    type Ret = Result<ClauseSet<Symbol>, FormulaConversionErr>;

    fn visit_var(&mut self, spelling: Symbol) -> Self::Ret {
        let a = Atom::new(spelling, false);
        let c = Clause::new(vec![a]);
        Ok(ClauseSet::new(vec![c]))
    }

    fn visit_not(&mut self, child: &crate::logic::LogicNode) -> Self::Ret {
        match child {
            crate::logic::LogicNode::Var(s) => {
                let a = Atom::new(*s, true);
                let c = Clause::new(vec![a]);
                Ok(ClauseSet::new(vec![c]))
            }
            crate::logic::LogicNode::Not(c) => self.visit(c),
            crate::logic::LogicNode::And(l, r) => self.visit(&LogicNode::Or(
                LogicNode::Not(l.clone()).into(),
                LogicNode::Not(r.clone()).into(),
            )),
            crate::logic::LogicNode::Or(l, r) => self.visit(&LogicNode::And(
                LogicNode::Not(l.clone()).into(),
                LogicNode::Not(r.clone()).into(),
            )),
            crate::logic::LogicNode::Impl(l, r) => {
                self.visit(&LogicNode::And(l.clone(), LogicNode::Not(r.clone()).into()))
            }
            crate::logic::LogicNode::Equiv(l, r) => {
                let impl_1 = LogicNode::Impl(l.clone(), r.clone()).into();
                let impl_2 = LogicNode::Impl(r.clone(), l.clone()).into();

                self.visit(&LogicNode::Not(LogicNode::And(impl_1, impl_2).into()))
            }
            _ => panic!("Cannot create CNF of FO formula"),
        }
    }

    fn visit_and(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        let mut left = self.visit(left)?;
        let right = self.visit(right)?;
        left.unite(&right);
        Ok(left)
    }

    fn visit_or(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        let left: Vec<Clause<Symbol>> = self.visit(left)?.into();
        let right: Vec<Clause<Symbol>> = self.visit(right)?.into();

        if left.len() * right.len() > crate::CNF_BLOWUP_LIMIT as usize {
            Err(FormulaConversionErr)
        } else {
            let mut clauses = vec![];
            for lc in left.into_iter() {
                for rc in right.clone().into_iter() {
                    let mut atoms: Vec<Atom<Symbol>> = lc.clone().into();
                    atoms.append(&mut rc.into());
                    let clause = Clause::new(atoms);
                    clauses.push(clause);
                }
            }

            Ok(ClauseSet::new(clauses))
        }
    }

    fn visit_impl(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        let n = LogicNode::Impl(left.clone().into(), right.clone().into()).to_basic_ops();
        self.visit(&n)
    }

    fn visit_equiv(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        let n = LogicNode::Equiv(left.clone().into(), right.clone().into()).to_basic_ops();
        self.visit(&n)
    }

    fn visit_rel(&mut self, _spelling: Symbol, _args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }

    fn visit_all(
        &mut self,
        _var: Symbol,
        _child: &crate::logic::LogicNode,
        _bound_vars: &Vec<Symbol>,
    ) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }

    fn visit_ex(
        &mut self,
        _var: Symbol,
        _child: &crate::logic::LogicNode,
        _bound_vars: &Vec<Symbol>,
    ) -> Self::Ret {
        panic!("Cannot create CNF of FO formula")
    }
}
