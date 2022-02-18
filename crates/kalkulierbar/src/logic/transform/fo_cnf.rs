use std::fmt::{self, Debug};

use crate::{
    clause::{Atom, Clause, ClauseSet},
    consts,
    logic::{fo::Relation, LogicNode},
    symbol::Symbol,
};

use super::{
    skolem_normal::{skolem_normal_form, SkolemNormalFormErr},
    visitor::MutLogicNodeVisitor,
};

pub fn fo_cnf(formula: LogicNode) -> Result<ClauseSet<Relation>, FOCNFErr> {
    let mut cnf = FOCNF;
    cnf.visit(&skolem_normal_form(formula)?)
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum FOCNFErr {
    UnknownNode,
    HeavyBlowUp,
    SkolemErr(SkolemNormalFormErr),
}

impl fmt::Display for FOCNFErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FOCNFErr::UnknownNode => write!(f, ""),
            FOCNFErr::HeavyBlowUp => write!(f, ""),
            FOCNFErr::SkolemErr(e) => fmt::Display::fmt(&e, f),
        }
    }
}

impl From<SkolemNormalFormErr> for FOCNFErr {
    fn from(e: SkolemNormalFormErr) -> Self {
        Self::SkolemErr(e)
    }
}

struct FOCNF;

impl MutLogicNodeVisitor for FOCNF {
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

    fn visit_all(&mut self, _: Symbol, child: &crate::logic::LogicNode) -> Self::Ret {
        self.visit(child)
    }

    fn visit_ex(&mut self, _: Symbol, _: &crate::logic::LogicNode) -> Self::Ret {
        panic!("The formula is not a FO formula in skolem normal form")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse::fo::parse_fo_formula, session};

    #[test]
    fn valid() {
        let formulas = vec![
            (
                "R(a) -> R(b) | R(a) & !R(b)",
                "{!R(a), R(b), R(a)}, {!R(a), R(b), !R(b)}",
            ),
            ("!(R(a) | R(b))", "{!R(a)}, {!R(b)}"),
            ("!(R(a) & R(b))", "{!R(a), !R(b)}"),
            (
                "!(!R(a)) <-> !R(a)",
                "{R(a), !R(a)}, {R(a), R(a)}, {!R(a), !R(a)}, {!R(a), R(a)}",
            ),
            (r"!\ex A : \all B : (R(B) -> !R(A))", "{R(sk1(A))}, {R(A)}"),
            (
                r"!\all A : \all C : (R(A) <-> !R(C))",
                "{!R(sk1), R(sk2)}, {R(sk1), !R(sk2)}",
            ),
        ];
        session(|| {
            for (f, e) in formulas {
                let parsed = parse_fo_formula(f).unwrap();
                assert_eq!(e, format!("{}", fo_cnf(parsed).unwrap()));
            }
        })
    }
}
