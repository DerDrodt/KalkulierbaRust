use std::{
    collections::{hash_map::Keys, HashMap},
    fmt,
};

use serde::{
    de::{MapAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};

use crate::{
    parse::{fo::parse_fo_term, ParseErr},
    Symbol,
};

use super::{
    fo::{FOTerm, Relation},
    transform::{term_manipulator::TermContainsVariableChecker, visitor::FOTermVisitor},
};

pub mod unifier_eq;

#[derive(Debug, PartialEq, Eq)]
pub enum UnificationErr {
    DifferentRels(Relation, Relation),
    DifferentNum(Relation, Relation),
    Occurs(Symbol, FOTerm),
    CannotBeUnified(FOTerm, FOTerm),
}

impl fmt::Display for UnificationErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UnificationErr::DifferentRels(r1, r2) => {
                write!(f, "Relations '{r1}' and '{r2}' have different names")
            }
            UnificationErr::DifferentNum(r1, r2) => write!(
                f,
                "Relations '{r1}' and '{r2}' have different numbers of arguments"
            ),
            UnificationErr::Occurs(v, t) => write!(f, "Variable '{v}' appears in '{t}'"),
            UnificationErr::CannotBeUnified(t1, t2) => {
                write!(f, "'{t1}' and '{t2}' cannot be unified")
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
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

    pub fn get(&self, s: &Symbol) -> Option<&FOTerm> {
        self.0.get(s)
    }

    pub fn get_unwrap(&self, s: Symbol) -> &FOTerm {
        self.0.get(&s).unwrap()
    }

    pub fn remove(&mut self, s: &Symbol) -> Option<FOTerm> {
        self.0.remove(s)
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

    pub fn keys(&self) -> Keys<Symbol, FOTerm> {
        self.0.keys()
    }

    pub fn rendered_map(&self) -> HashMap<Symbol, String> {
        self.0.iter().map(|(s, t)| (*s, t.to_string())).collect()
    }
}

impl fmt::Display for Unifier {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let mut contents = String::new();
        for (i, (k, v)) in self.0.iter().enumerate() {
            contents.push_str(&format!("{}={}", k, v));
            if i < self.0.len() - 1 {
                contents.push_str(", ");
            }
        }
        write!(f, "{{{}}}", contents)
    }
}

pub fn try_to_parse_unifier(h: HashMap<Symbol, String>) -> Result<Unifier, ParseErr> {
    let mut u = HashMap::new();

    for (k, v) in h {
        let t = parse_fo_term(&v)?;
        u.insert(k, t);
    }

    Ok(Unifier::from_map(u))
}

impl Serialize for Unifier {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        Serialize::serialize(&self.0, serializer)
    }
}

impl<'de> Deserialize<'de> for Unifier {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct MapVisitor;

        impl<'de> Visitor<'de> for MapVisitor {
            type Value = Unifier;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a map")
            }

            #[inline]
            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: MapAccess<'de>,
            {
                let mut values = HashMap::new();

                while let Some((key, value)) = map.next_entry()? {
                    values.insert(key, value);
                }

                Ok(Unifier::from_map(values))
            }
        }

        deserializer.deserialize_map(MapVisitor)
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

fn unify_terms(mut terms: Vec<(FOTerm, FOTerm)>) -> Result<Unifier, UnificationErr> {
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

#[cfg(test)]
mod tests {

    use super::*;
    use crate::session;

    macro_rules! rel {
        ($name:expr, $( $arg:expr ),*) => {
            Relation::new(Symbol::intern($name), vec![$($arg),*])
        };
    }

    macro_rules! func {
        ($name:expr, $( $arg:expr ),*) => {
            FOTerm::Function(Symbol::intern($name), vec![$($arg),*])
        };
    }

    fn q_var(s: &str) -> FOTerm {
        FOTerm::QuantifiedVar(Symbol::intern(s))
    }

    fn con(s: &str) -> FOTerm {
        FOTerm::Const(Symbol::intern(s))
    }

    #[test]
    fn test_unify() {
        session(|| {
            let mgu = unify(
                &rel!("R", func!("f", q_var("X")), func!("g", con("c"))),
                &rel!("R", func!("f", q_var("Y")), q_var("Y")),
            )
            .unwrap();

            let mut map = HashMap::new();
            map.insert(Symbol::intern("X"), func!("g", con("c")));
            map.insert(Symbol::intern("Y"), func!("g", con("c")));

            assert_eq!(map.len(), mgu.0.len());

            for (key, val) in map {
                assert!(
                    val.syn_eq(mgu.get_unwrap(key)),
                    "{}!={}",
                    val,
                    mgu.get_unwrap(key)
                )
            }
        })
    }
}
