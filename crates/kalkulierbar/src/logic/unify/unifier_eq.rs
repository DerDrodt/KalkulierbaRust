use std::collections::HashMap;

use crate::{
    logic::{
        fo::{FOTerm, Relation},
        transform::transformer::MutFOTermTransformer,
    },
    Symbol,
};

use super::{unify, Unifier};

pub fn is_mgu_or_not_unifiable(u: &Unifier, r1: &Relation, r2: &Relation) -> bool {
    match unify(r1, r2) {
        Ok(mgu) => eq(&mgu, u),
        Err(_) => true,
    }
}

fn eq(u1: &Unifier, u2: &Unifier) -> bool {
    let mut term_pairs = Vec::new();
    let keys = u1.keys();

    for k in keys {
        let t1 = u1.get(k).cloned().unwrap_or(FOTerm::QuantifiedVar(*k));
        let t2 = u2.get(k).cloned().unwrap_or(FOTerm::QuantifiedVar(*k));
        term_pairs.push((t1, t2));
    }

    let canonical_terms = canonical_var_names(term_pairs);

    canonical_terms.iter().all(|(t1, t2)| t1.syn_eq(t2))
}

fn canonical_var_names(l: Vec<(FOTerm, FOTerm)>) -> Vec<(FOTerm, FOTerm)> {
    let mut c1 = VarCanonicizer::default();
    let mut c2 = VarCanonicizer::default();

    l.into_iter()
        .map(|(t1, t2)| (c1.visit(t1), c2.visit(t2)))
        .collect()
}

#[derive(Default)]
struct VarCanonicizer {
    counter: u32,
    replacements: HashMap<Symbol, Symbol>,
}

impl MutFOTermTransformer for VarCanonicizer {
    fn visit_quantified_var(&mut self, s: Symbol) -> FOTerm {
        // If we haven't seen this variable before, assign a new name
        let spell = if let Some(s) = self.replacements.get(&s) {
            *s
        } else {
            self.counter += 1;
            let spell = Symbol::intern(&format!("V-{}", self.counter));
            self.replacements.insert(s, spell);
            spell
        };
        FOTerm::QuantifiedVar(spell)
    }

    fn visit_const(&mut self, s: Symbol) -> FOTerm {
        FOTerm::Const(s)
    }

    fn visit_fn(&mut self, name: Symbol, args: Vec<FOTerm>) -> FOTerm {
        FOTerm::Function(name, args.into_iter().map(|a| self.visit(a)).collect())
    }
}
