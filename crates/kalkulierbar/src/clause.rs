use std::fmt;

use serde::{Deserialize, Serialize};

use crate::logic::{fo::Relation, unify::Substitution};

#[derive(Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
pub struct Atom<L: fmt::Display + Clone> {
    lit: L,
    negated: bool,
}

impl<L: fmt::Display + Clone> Atom<L> {
    pub fn new(lit: L, negated: bool) -> Self {
        Atom { lit, negated }
    }

    pub fn lit(&self) -> &L {
        &self.lit
    }

    pub fn take_lit(self) -> L {
        self.lit
    }

    pub fn negated(&self) -> bool {
        self.negated
    }

    pub fn not(&self) -> Atom<L> {
        Atom {
            lit: self.lit.clone(),
            negated: !self.negated,
        }
    }
}

impl Atom<Relation> {
    pub fn instantiate(&self, u: &Substitution) -> Self {
        Atom {
            lit: self.lit.instantiate(u),
            negated: self.negated,
        }
    }
}

impl<L: fmt::Display + Clone> fmt::Display for Atom<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.negated() { "!" } else { "" }, self.lit())
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct Clause<L: fmt::Display + Clone> {
    atoms: Vec<Atom<L>>,
}

impl<L: fmt::Display + Clone> Clause<L> {
    pub fn new(atoms: Vec<Atom<L>>) -> Self {
        Clause { atoms }
    }

    pub fn add(&mut self, atom: Atom<L>) {
        self.atoms.push(atom);
    }

    pub fn add_all(&mut self, atoms: Vec<Atom<L>>) {
        for a in atoms {
            self.add(a);
        }
    }

    pub fn is_positive(&self) -> bool {
        self.atoms.iter().all(|a| !a.negated())
    }

    pub fn is_empty(&self) -> bool {
        self.atoms.is_empty()
    }

    pub fn size(&self) -> usize {
        self.atoms.len()
    }

    pub fn atoms(&self) -> &Vec<Atom<L>> {
        &self.atoms
    }

    pub fn take_atoms(self) -> Vec<Atom<L>> {
        self.atoms
    }

    pub fn remove(&mut self, idx: usize) {
        self.atoms.remove(idx);
    }
}

impl Clause<Relation> {
    pub fn instantiate(&self, u: &Substitution) -> Self {
        Clause {
            atoms: self.atoms.iter().map(|a| a.instantiate(u)).collect(),
        }
    }
}

impl<L: fmt::Display + Clone + PartialEq> Clause<L> {
    pub fn find_negation_of(&self, a: &Atom<L>) -> Option<usize> {
        for (i, atom) in self.atoms.iter().enumerate() {
            if atom.negated != a.negated && a.lit == atom.lit {
                return Some(i);
            }
        }
        None
    }
}

impl<L: fmt::Display + Clone> From<Clause<L>> for Vec<Atom<L>> {
    fn from(c: Clause<L>) -> Self {
        c.atoms
    }
}

impl<L: fmt::Display + Clone> fmt::Display for Clause<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut atoms = String::new();

        for (i, a) in self.atoms.iter().enumerate() {
            atoms.push_str(&a.to_string());
            if i < self.size() - 1 {
                atoms.push_str(", ");
            }
        }

        write!(f, "{{{}}}", atoms)
    }
}

impl<L> IntoIterator for Clause<L>
where
    L: Clone + fmt::Display,
{
    type Item = Atom<L>;

    type IntoIter = ClauseIntoIterator<L>;

    fn into_iter(mut self) -> Self::IntoIter {
        self.atoms.reverse();
        ClauseIntoIterator(self)
    }
}

pub struct ClauseIntoIterator<L>(Clause<L>)
where
    L: Clone + fmt::Display;

impl<L> Iterator for ClauseIntoIterator<L>
where
    L: Clone + fmt::Display,
{
    type Item = Atom<L>;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.atoms.pop()
    }
}

impl<'a, L> IntoIterator for &'a Clause<L>
where
    L: Clone + fmt::Display,
{
    type Item = &'a Atom<L>;

    type IntoIter = ClauseIterator<'a, L>;

    fn into_iter(self) -> Self::IntoIter {
        ClauseIterator {
            clause: self,
            idx: 0,
        }
    }
}

pub struct ClauseIterator<'a, L>
where
    L: Clone + fmt::Display,
{
    clause: &'a Clause<L>,
    idx: usize,
}

impl<'a, L> Iterator for ClauseIterator<'a, L>
where
    L: Clone + fmt::Display,
{
    type Item = &'a Atom<L>;

    fn next(&mut self) -> Option<Self::Item> {
        let res = self.clause.atoms.get(self.idx);
        self.idx += 1;
        res
    }
}

#[derive(Clone, Debug, Deserialize, Serialize, Default)]
pub struct ClauseSet<L: fmt::Display + Clone> {
    clauses: Vec<Clause<L>>,
}

impl<L: fmt::Display + Clone> ClauseSet<L> {
    pub fn new(clauses: Vec<Clause<L>>) -> Self {
        ClauseSet { clauses }
    }

    pub fn add(&mut self, c: Clause<L>) {
        self.clauses.push(c)
    }

    pub fn add_all(&mut self, cs: Vec<Clause<L>>) {
        for c in cs {
            self.add(c);
        }
    }

    pub fn unite(&mut self, cs: &ClauseSet<L>) {
        for c in cs.clauses.iter().cloned() {
            self.add(c)
        }
    }

    pub fn size(&self) -> usize {
        self.clauses.len()
    }

    pub fn clauses(&self) -> &Vec<Clause<L>> {
        &self.clauses
    }

    pub fn clear(&mut self) {
        self.clauses.clear();
    }

    pub fn remove(&mut self, idx: usize) -> Clause<L> {
        self.clauses.remove(idx)
    }

    pub fn remove_atom(&mut self, c: usize, a: usize) {
        self.clauses[c].remove(a);
    }

    pub fn insert(&mut self, idx: usize, c: Clause<L>) {
        self.clauses.insert(idx, c)
    }

    pub fn replace(&mut self, idx: usize, c: Clause<L>) {
        self.clauses[idx] = c;
    }
}

impl<L: fmt::Display + Clone> fmt::Display for ClauseSet<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut atoms = String::new();

        for (i, a) in self.clauses.iter().enumerate() {
            atoms.push_str(&a.to_string());
            if i < self.size() - 1 {
                atoms.push_str(", ");
            }
        }

        write!(f, "{}", atoms)
    }
}

impl<L: fmt::Display + Clone> From<ClauseSet<L>> for Vec<Clause<L>> {
    fn from(c: ClauseSet<L>) -> Self {
        c.clauses
    }
}
