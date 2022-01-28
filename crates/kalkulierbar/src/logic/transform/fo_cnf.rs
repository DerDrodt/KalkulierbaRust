use std::fmt;

use crate::{
    clause::{Atom, Clause, ClauseSet},
    consts,
    logic::{fo::Relation, LogicNode},
    symbol::Symbol,
};

use super::visitor::LogicNodeVisitor;

pub fn fo_cnf(formula: LogicNode) -> Result<ClauseSet<Relation>, FOCNFErr> {
    todo!()
}

#[derive(Debug, Copy, Clone)]
pub enum FOCNFErr {
    UnknownNode,
    HeavyBlowUp,
}

impl fmt::Display for FOCNFErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FOCNFErr::UnknownNode => write!(f, ""),
            FOCNFErr::HeavyBlowUp => write!(f, ""),
        }
    }
}

struct FOCNF;

impl LogicNodeVisitor for FOCNF {
    type Ret = Result<ClauseSet<Relation>, FOCNFErr>;

    fn visit_var(&mut self, _: Symbol) -> Self::Ret {
        panic!("The formula is not a FO formula in skolem normal form")
    }

    fn visit_not(&mut self, child: &crate::logic::LogicNode) -> Self::Ret {
        match child {
            LogicNode::Rel(name, args) => {
                let atom = Atom::new(Relation::new(*name, args.clone()), true);
                let clause = Clause::new(vec![atom]);
                Ok(ClauseSet::new(vec![clause]))
            }
            _ => Err(FOCNFErr::UnknownNode),
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
        let left = self.visit(left)?;
        let right = self.visit(right)?;
        let mut cs = ClauseSet::new(Vec::new());

        if left.size() * right.size() > consts::CNF_BLOWUP_LIMIT as usize {
            return Err(FOCNFErr::HeavyBlowUp);
        }

        for lc in left.clauses() {
            for rc in right.clauses() {
                let mut atoms = Vec::new();
                for l in lc.atoms() {
                    atoms.push(l.clone());
                }
                for r in rc.atoms() {
                    atoms.push(r.clone());
                }
                let clause = Clause::new(atoms);
                cs.add(clause);
            }
        }

        Ok(cs)
    }

    fn visit_impl(
        &mut self,
        _: &crate::logic::LogicNode,
        _: &crate::logic::LogicNode,
    ) -> Self::Ret {
        panic!("The formula is not a FO formula in skolem normal form")
    }

    fn visit_equiv(
        &mut self,
        _: &crate::logic::LogicNode,
        _: &crate::logic::LogicNode,
    ) -> Self::Ret {
        panic!("The formula is not a FO formula in skolem normal form")
    }

    fn visit_rel(&mut self, spelling: Symbol, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        let atom = Atom::new(Relation::new(spelling, args.clone()), false);
        let clause = Clause::new(vec![atom]);
        Ok(ClauseSet::new(vec![clause]))
    }

    fn visit_all(
        &mut self,
        _: Symbol,
        child: &crate::logic::LogicNode,
        _: &Vec<Symbol>,
    ) -> Self::Ret {
        self.visit(child)
    }

    fn visit_ex(&mut self, _: Symbol, _: &crate::logic::LogicNode, _: &Vec<Symbol>) -> Self::Ret {
        panic!("The formula is not a FO formula in skolem normal form")
    }
}
