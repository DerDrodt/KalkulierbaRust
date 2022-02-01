use std::collections::HashMap;

use crate::Symbol;

use super::{
    fo::{FOTerm, Relation},
    transform::{term_manipulator::TermContainsVariableChecker, visitor::FOTermVisitor},
};

pub enum UnificationErr {
    DifferentRels(Relation, Relation),
    DifferentNum(Relation, Relation),
    Occurs(Symbol, FOTerm),
    CannotBeUnified(FOTerm, FOTerm),
}

pub struct Unifier(HashMap<Symbol, FOTerm>);

impl Unifier {
    pub fn new() -> Self {
        Unifier(HashMap::new())
    }

    pub fn from_value(s: Symbol, t: FOTerm) -> Self {
        let mut u = Self::new();
        u.0.insert(s, t);
        u
    }

    pub fn from_map(m: HashMap<Symbol, FOTerm>) -> Self {
        Unifier(m)
    }

    pub fn contains(&self, s: Symbol) -> bool {
        self.0.contains_key(&s)
    }

    pub fn get(&self, s: Symbol) -> &FOTerm {
        self.0.get(&s).unwrap()
    }

    fn add(&mut self, s: Symbol, t: FOTerm) {
        let u = Unifier::from_value(s, t.clone());
        let mut m = HashMap::new();
        for (key, term) in self.0.iter() {
            m.insert(*key, term.instantiate(&u));
        }
        m.insert(s, t);
        self.0 = m
    }
}

pub fn unify(rel1: &Relation, rel2: &Relation) -> Result<Unifier, UnificationErr> {
    let mut terms = Vec::new();
    find_terms_to_unify(&mut terms, rel1, rel2)?;
    unify_terms(terms)
}

pub fn unify_all<'a>(rels: Vec<(&'a Relation, &'a Relation)>) -> Result<Unifier, UnificationErr> {
    let mut terms = Vec::new();
    for (r1, r2) in rels {
        find_terms_to_unify(&mut terms, r1, r2)?;
    }
    unify_terms(terms)
}

fn find_terms_to_unify<'a>(
    terms: &mut Vec<(FOTerm, FOTerm)>,
    r1: &'a Relation,
    r2: &'a Relation,
) -> Result<(), UnificationErr> {
    let arg1 = &r1.args;
    let arg2 = &r2.args;

    if r1.spelling != r2.spelling {
        return Err(UnificationErr::DifferentRels(r1.clone(), r2.clone()));
    }
    if arg1.len() != arg2.len() {
        return Err(UnificationErr::DifferentNum(r1.clone(), r2.clone()));
    }

    for p in arg1.iter().cloned().zip(arg2.iter().cloned()) {
        terms.push(p);
    }

    Ok(())
}

fn unify_terms<'a>(mut terms: Vec<(FOTerm, FOTerm)>) -> Result<Unifier, UnificationErr> {
    let mut mgu = Unifier::new();

    while let Some((ot1, ot2)) = terms.pop() {
        let (t1, t2) = (ot1.instantiate(&mgu), ot2.instantiate(&mgu));

        if t1.syn_eq(&t2) {
            continue;
        } else {
            match (t1, t2) {
                (FOTerm::QuantifiedVar(s), t2) => {
                    if t2.is_fn() && TermContainsVariableChecker(s).visit(&t2) {
                        return Err(UnificationErr::Occurs(s, t2));
                    }
                    mgu.add(s, t2)
                }
                (t1, FOTerm::QuantifiedVar(s)) => terms.push((FOTerm::QuantifiedVar(s), t1)),
                (FOTerm::Function(n1, args1), FOTerm::Function(n2, args2))
                    if n1 == n2 && args1.len() == args2.len() =>
                {
                    for (a1, a2) in args1.into_iter().zip(args2) {
                        terms.push((a1, a2))
                    }
                }
                (t1, t2) => return Err(UnificationErr::CannotBeUnified(t1, t2)),
            }
        }
    }

    Ok(mgu)
}
