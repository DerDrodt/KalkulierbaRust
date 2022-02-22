use std::fmt;

use crate::{
    clause::{Atom, Clause},
    SynEq,
};

pub enum UtilErr<L>
where
    L: fmt::Display + Clone,
{
    DoesNotContain(Clause<L>, L),
    DoNotContainPosNeg(Clause<L>, Clause<L>, L),
    NoCommonLits(Clause<L>, Clause<L>),
    NoCommonPosNegLits(Clause<L>, Clause<L>),
}

impl<L> fmt::Display for UtilErr<L>
where
    L: fmt::Display + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UtilErr::DoesNotContain(c, l) => write!(f, "Clause '{c}' does not contain atom '{l}'"),
            UtilErr::DoNotContainPosNeg(c1, c2, l) => write!(f, "Clauses '{c1}' and '{c2}' do not contain atom '{l}' in both positive and negated form"),
            UtilErr::NoCommonLits(c1, c2) => write!(f, "Clauses '{c1}' and '{c2}' contain no common literals"),
            UtilErr::NoCommonPosNegLits(c1, c2) => write!(f, "Clauses '{c1}' and '{c2}' contain no common literals that appear in positive and negated form"),
        }
    }
}

pub fn filter_clause<'a, L>(
    c1: &'a Clause<L>,
    c2: &'a Clause<L>,
    lit: &'a L,
) -> Result<(Atom<L>, Atom<L>), UtilErr<L>>
where
    L: fmt::Display + Clone + SynEq,
{
    // Filter clauses for atoms with correct literal
    let as_in_c1: Vec<Atom<L>> = c1
        .atoms()
        .iter()
        .filter(|a| lits_are_eq(a.lit(), lit))
        .cloned()
        .collect();
    if as_in_c1.is_empty() {
        return Err(UtilErr::DoesNotContain(c1.clone(), lit.clone()));
    }
    let as_in_c2: Vec<Atom<L>> = c2
        .atoms()
        .iter()
        .filter(|a| lits_are_eq(a.lit(), lit))
        .cloned()
        .collect();
    if as_in_c2.is_empty() {
        return Err(UtilErr::DoesNotContain(c2.clone(), lit.clone()));
    }

    find_res_candidate(as_in_c1, as_in_c2)
        .ok_or_else(|| UtilErr::DoNotContainPosNeg(c1.clone(), c2.clone(), lit.clone()))
}

pub fn get_auto_res_candidate<L>(
    c1: &Clause<L>,
    c2: &Clause<L>,
) -> Result<(Atom<L>, Atom<L>), UtilErr<L>>
where
    L: fmt::Display + Clone + SynEq + PartialEq,
{
    // Find literals present in both clauses
    let shared: Vec<&Atom<L>> = c1
        .atoms()
        .iter()
        .filter(|a1| c2.atoms().iter().any(|a2| lits_are_eq(a1.lit(), a2.lit())))
        .collect();

    if shared.is_empty() {
        return Err(UtilErr::NoCommonLits(c1.clone(), c2.clone()));
    }

    let mut idx = None;
    let shared: Vec<&Atom<L>> = shared
        .iter()
        .filter(|a| match c2.find_negation_of(a) {
            Some(i) => {
                idx = Some(i);
                true
            }
            _ => false,
        })
        .map(|a| *a)
        .collect();

    if shared.is_empty() {
        return Err(UtilErr::NoCommonPosNegLits(c1.clone(), c2.clone()));
    }

    Ok((shared[0].clone(), c2.atoms()[idx.unwrap()].clone()))
}

pub fn build_clause<L>(c1: &Clause<L>, a1: Atom<L>, c2: &Clause<L>, a2: Atom<L>) -> Clause<L>
where
    L: fmt::Display + Clone + PartialEq,
{
    let atoms = c1
        .atoms()
        .iter()
        .filter(|a| *a != &a1)
        .chain(c2.atoms().iter().filter(|a| *a != &a2))
        .cloned()
        .collect();
    Clause::new(atoms)
}

pub fn find_res_candidate<L>(as1: Vec<Atom<L>>, as2: Vec<Atom<L>>) -> Option<(Atom<L>, Atom<L>)>
where
    L: fmt::Display + Clone,
{
    let (pos, neg) = as2.iter().partition(|a| !a.negated());

    for a1 in as1 {
        let other: &Vec<&Atom<L>> = if a1.negated() { &pos } else { &neg };
        if other.is_empty() {
            continue;
        }
        let a2 = other[0];
        return Some((a1, a2.clone()));
    }
    None
}

fn lits_are_eq<L>(a: &L, b: &L) -> bool
where
    L: fmt::Display + Clone + SynEq,
{
    // Use syntactic equality for literal comparison if defined
    a.syn_eq(b)
}
