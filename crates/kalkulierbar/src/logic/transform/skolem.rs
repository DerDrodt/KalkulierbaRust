use std::{collections::HashMap, fmt};

use crate::{
    logic::{fo::FOTerm, LogicNode},
    Symbol,
};

use super::{
    signature::Signature,
    transformer::{MutFOTermTransformer, MutLogicNodeTransformer},
};

pub fn skolemize(n: LogicNode) -> Result<LogicNode, SkolemizationErr> {
    let sig = Signature::of_node(&n);
    Skolemization::new(sig).visit(n)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SkolemizationErr;

impl fmt::Display for SkolemizationErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Double-bound universally quantified variable encountered during Skolemization"
        )
    }
}

pub struct Skolemization {
    counter: u32,
    quantified_vars: Vec<Symbol>,
    replacement_map: HashMap<Symbol, FOTerm>,
    sig: Signature,
}

impl Skolemization {
    pub fn new(sig: Signature) -> Self {
        Self {
            counter: 0,
            quantified_vars: Vec::new(),
            replacement_map: HashMap::new(),
            sig,
        }
    }

    fn get_skolem_term(&mut self) -> FOTerm {
        self.counter += 1;
        let mut name = Symbol::intern(&format!("sk{}", self.counter));

        while self.sig.has_const_or_fn(name) {
            self.counter += 1;
            name = Symbol::intern(&format!("sk{}", self.counter));
        }

        if self.quantified_vars.is_empty() {
            FOTerm::Const(name)
        } else {
            let mut args = Vec::new();

            for v in &self.quantified_vars {
                args.push(FOTerm::QuantifiedVar(*v))
            }

            FOTerm::Function(name, args)
        }
    }
}

impl MutLogicNodeTransformer for Skolemization {
    type Ret = Result<LogicNode, SkolemizationErr>;

    fn visit_var(&mut self, _: Symbol) -> Self::Ret {
        panic!("Unknown LogicNode encountered during Skolemization")
    }

    fn visit_not(&mut self, child: crate::logic::LogicNode) -> Self::Ret {
        Ok(LogicNode::Not(Box::new(self.visit(child)?)))
    }

    fn visit_and(
        &mut self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::And(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_or(
        &mut self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Or(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_impl(
        &mut self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Impl(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_equiv(
        &mut self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Equiv(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_rel(&mut self, spelling: Symbol, args: Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        let mut replacer = SkolemTermReplacer::new(&self.replacement_map);
        Ok(LogicNode::Rel(
            spelling,
            args.into_iter().map(|a| replacer.visit(a)).collect(),
        ))
    }

    fn visit_all(&mut self, var: Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        if self.quantified_vars.contains(&var) {
            return Err(SkolemizationErr);
        }
        self.quantified_vars.push(var);
        let child = self.visit(child)?;
        let popped = self.quantified_vars.pop().unwrap();
        assert!(popped == var);

        Ok(LogicNode::All(var, Box::new(child)))
    }

    fn visit_ex(&mut self, var: Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        let term = self.get_skolem_term();

        let old = self.replacement_map.insert(var, term);

        let ret = self.visit(child);

        if let Some(v) = old {
            self.replacement_map.insert(var, v);
        } else {
            self.replacement_map.remove(&var);
        }

        ret
    }
}

struct SkolemTermReplacer<'a> {
    replacement_map: &'a HashMap<Symbol, FOTerm>,
}

impl<'a> SkolemTermReplacer<'a> {
    fn new(replacement_map: &'a HashMap<Symbol, FOTerm>) -> Self {
        Self { replacement_map }
    }
}

impl<'a> MutFOTermTransformer for SkolemTermReplacer<'a> {
    fn visit_quantified_var(&mut self, s: Symbol) -> FOTerm {
        if self.replacement_map.contains_key(&s) {
            let skolem_term = self.replacement_map.get(&s).unwrap().clone();

            skolem_term
        } else {
            FOTerm::QuantifiedVar(s)
        }
    }

    fn visit_const(&mut self, s: Symbol) -> FOTerm {
        FOTerm::Const(s)
    }

    fn visit_fn(&mut self, name: Symbol, args: Vec<FOTerm>) -> FOTerm {
        FOTerm::Function(name, args.into_iter().map(|a| self.visit(a)).collect())
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
                (
                    "R(a) -> R(b) | R(a) & !R(b)",
                    "(R(a) → (R(b) ∨ (R(a) ∧ ¬R(b))))",
                ),
                ("!(R(a) | R(b))", "¬(R(a) ∨ R(b))"),
                ("!(R(a) & R(b))", "¬(R(a) ∧ R(b))"),
                ("!(!R(a) <-> !R(a))", "¬(¬R(a) <=> ¬R(a))"),
                ("\\ex A: R(A) & Q(sk1)", "(R(sk2) ∧ Q(sk1))"),
                (
                    "!\\ex A : !(S(A) & !\\all B : (R(B) -> !R(A)))",
                    "¬¬(S(sk1) ∧ ¬(∀B: (R(B) → ¬R(sk1))))",
                ),
                (
                    "!\\all A : (P(A) <-> \\ex C : (R(A) <-> !R(C)))",
                    "¬(∀A: (P(A) <=> (R(A) <=> ¬R(sk1(A)))))",
                ),
                (
                    "!\\ex A : R(A) -> !\\all B : !(R(B) | !R(B))",
                    "(¬R(sk1) → ¬(∀B: ¬(R(B) ∨ ¬R(B))))",
                ),
            ];

            for (f, e) in formulas {
                let parsed = parse_fo_formula(f).unwrap();
                let nnf = skolemize(parsed).unwrap();
                assert_eq!(e, nnf.to_string());
            }
        })
    }
}
