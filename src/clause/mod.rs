use std::fmt;

#[derive(Clone, Debug)]
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

    pub fn negated(&self) -> bool {
        self.negated
    }
}

impl<L: fmt::Display + Clone> fmt::Display for Atom<L> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}{}", if self.negated() { "!" } else { "" }, self.lit())
    }
}

#[derive(Debug, Clone)]
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

#[derive(Clone, Debug)]
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
