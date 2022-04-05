use std::collections::HashMap;
use std::fmt;

use serde::de::{self, MapAccess, Visitor};
use serde::ser::SerializeStruct;
use serde::{Deserialize, Serialize};

use crate::calculus::CloseMsg;
use crate::clause::{Atom, Clause, ClauseSet};
use crate::parse::{parse_prop_flexible, CNFStrategy, ParseErr};
use crate::tamper_protect::ProtectedState;
use crate::{Calculus, Symbol};

use super::util::{build_clause, filter_clause, get_auto_res_candidate, UtilErr};
use super::VisualHelp;

#[derive(Deserialize, Serialize, Default)]
#[serde(rename_all = "camelCase")]
#[serde(default)]
pub struct Params {
    cnf_strategy: CNFStrategy,
    visual_help: VisualHelp,
}

#[derive(Debug, Clone)]
pub struct State {
    pub clause_set: ClauseSet<Symbol>,
    pub visual_help: VisualHelp,
    pub newest_node: Option<usize>,
    pub hidden_clauses: ClauseSet<Symbol>,
    pub last_move: Option<Move>,
}

impl State {
    pub fn new(clause_set: ClauseSet<Symbol>, visual_help: VisualHelp) -> Self {
        Self {
            clause_set,
            visual_help,
            newest_node: None,
            hidden_clauses: ClauseSet::new(vec![]),
            last_move: None,
        }
    }
}

impl ProtectedState for State {
    fn compute_seal_info(&self) -> String {
        format!(
            "resolutionstate|{}|{}|{}|{}",
            self.clause_set,
            self.hidden_clauses,
            self.visual_help,
            match self.newest_node {
                Some(n) => n as i32,
                _ => -1,
            }
        )
    }
}

#[derive(Debug, Clone)]
pub enum Move {
    Resolve(usize, usize, Option<Symbol>),
    Hide(usize),
    Show,
    Hyper(usize, HashMap<usize, (usize, usize)>),
    Factorize(usize),
}

#[derive(Debug)]
pub enum Err {
    Parse(ParseErr),
    InvalidClauseId(usize),
    NothingToFactorize,
    SameIds,
    UtilErr(UtilErr<Symbol>),
    NoSuchAtomInMain(Clause<Symbol>, usize),
    NoSuchAtomInSide(Clause<Symbol>, usize),
    EmptyHyperMap,
    SidePremissNotPos(Clause<Symbol>),
    MainAtomNotNeg(Atom<Symbol>),
    ResultingMainNotPos(Clause<Symbol>),
}

impl From<ParseErr> for Err {
    fn from(e: ParseErr) -> Self {
        Self::Parse(e)
    }
}

impl From<UtilErr<Symbol>> for Err {
    fn from(e: UtilErr<Symbol>) -> Self {
        Self::UtilErr(e)
    }
}

impl fmt::Display for Err {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Err::Parse(e) => fmt::Display::fmt(e, f),
            Err::InvalidClauseId(c) => write!(f, "There is no clause with id {c}"),
            Err::NothingToFactorize => write!(f, "Nothing to factorize"),
            Err::SameIds => write!(f, "Both ids refer to the same clause"),
            Err::UtilErr(e) => fmt::Display::fmt(e, f),
            Err::NoSuchAtomInMain(c, id) => write!(
                f,
                "There is no atom with id {id} in (main premiss) clause '{c}'"
            ),
            Err::NoSuchAtomInSide(c, id) => write!(
                f,
                "There is no atom with id {id} in (side premiss) clause '{c}'"
            ),
            Err::EmptyHyperMap => {
                write!(f, "Please select side premisses for hyper resolution")
            }
            Err::SidePremissNotPos(c) => write!(f, "Side premiss '{c}' is not positive"),
            Err::MainAtomNotNeg(a) => {
                write!(f, "Literal '{a}' in main premiss has to be negative")
            }
            Err::ResultingMainNotPos(c) => {
                write!(f, "Resulting clause '{c}' is not positive")
            }
        }
    }
}

pub type PropResResult<T> = Result<T, Err>;

pub struct PropResolution;

impl<'f> Calculus<'f> for PropResolution {
    type Params = Params;

    type State = State;

    type Move = Move;

    type Error = Err;

    fn parse_formula(
        formula: &'f str,
        params: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        let params = params.unwrap_or_default();
        let parsed = parse_prop_flexible(formula, params.cnf_strategy)?;
        Ok(State::new(parsed, params.visual_help))
    }

    fn apply_move(state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        let mut state = match k_move.clone() {
            Move::Resolve(c1, c2, lit) => apply_resolve(state, c1, c2, lit)?,
            Move::Hide(c) => apply_hide(state, c)?,
            Move::Show => apply_show(state),
            Move::Hyper(main, map) => apply_hyper(state, main, map)?,
            Move::Factorize(c) => apply_factorize(state, c)?,
        };
        state.last_move = Some(k_move);
        Ok(state)
    }

    fn check_close(state: Self::State) -> crate::calculus::CloseMsg {
        let has_empty_clause = state.clause_set.clauses().iter().any(|c| c.is_empty());
        let msg = if has_empty_clause {
            "The proof is closed"
        } else {
            "The proof is not closed"
        };
        CloseMsg {
            closed: has_empty_clause,
            msg: msg.to_string(),
        }
    }
}

fn apply_resolve(
    mut state: State,
    c1: usize,
    c2: usize,
    lit: Option<Symbol>,
) -> PropResResult<State> {
    if c1 == c2 {
        return Err(Err::SameIds);
    }
    if c1 >= state.clause_set.size() {
        return Err(Err::InvalidClauseId(c1));
    }
    if c2 >= state.clause_set.size() {
        return Err(Err::InvalidClauseId(c2));
    }

    let newest_node = c2;

    let c1 = &state.clause_set.clauses()[c1];
    let c2 = &state.clause_set.clauses()[c2];

    let (a1, a2) = match lit {
        Some(l) => filter_clause(c1, c2, &l)?,
        None => get_auto_res_candidate(c1, c2)?,
    };

    let c = build_clause(c1, a1, c2, a2);

    state.clause_set.insert(newest_node, c);
    state.newest_node = Some(newest_node);

    Ok(state)
}

fn apply_hide(mut state: State, c: usize) -> PropResResult<State> {
    if c >= state.clause_set.size() {
        return Err(Err::InvalidClauseId(c));
    }

    // Move clause from main clause set to hidden clause set
    let c = state.clause_set.remove(c);
    state.hidden_clauses.add(c);
    state.newest_node = None;

    Ok(state)
}

fn apply_show(mut state: State) -> State {
    state.clause_set.unite(&state.hidden_clauses);
    state.hidden_clauses.clear();
    state.newest_node = None;

    state
}

fn apply_hyper(
    mut state: State,
    main: usize,
    atom_map: HashMap<usize, (usize, usize)>,
) -> PropResResult<State> {
    check_hyper(&state, main, &atom_map)?;

    if atom_map.is_empty() {
        return Err(Err::EmptyHyperMap);
    }

    let mut main_premiss = state.clause_set.clauses()[main].clone();

    for (ma_id, (sc_id, sa_id)) in atom_map {
        let side = &state.clause_set.clauses()[sc_id];

        // Check side premise for positiveness
        if !side.is_positive() {
            return Err(Err::SidePremissNotPos(side.clone()));
        }

        let ma = state.clause_set.clauses()[main].atoms()[ma_id].clone();
        if !ma.negated() {
            return Err(Err::MainAtomNotNeg(ma));
        }
        let sa = state.clause_set.clauses()[sc_id].atoms()[sa_id].clone();

        main_premiss = build_clause(&main_premiss, ma, side, sa);
    }

    if !main_premiss.is_positive() {
        return Err(Err::ResultingMainNotPos(main_premiss));
    }

    state.clause_set.add(main_premiss);
    state.newest_node = Some(state.clause_set.size() - 1);

    Ok(state)
}

fn apply_factorize(mut state: State, c: usize) -> PropResResult<State> {
    let mut cs = state.clause_set;

    if c >= cs.size() {
        return Err(Err::InvalidClauseId(c));
    }

    let old_c = &cs.clauses()[c];
    let mut atoms = vec![];
    for a in old_c {
        if !atoms.contains(a) {
            atoms.push(a.clone());
        }
    }

    let new_c = Clause::new(atoms);

    if new_c.size() == old_c.size() {
        return Err(Err::NothingToFactorize);
    }

    cs.remove(c);
    cs.insert(c, new_c);
    state.newest_node = Some(c);
    state.clause_set = cs;
    Ok(state)
}

fn check_hyper(
    state: &State,
    c_id: usize,
    atom_map: &HashMap<usize, (usize, usize)>,
) -> PropResResult<()> {
    if c_id >= state.clause_set.size() {
        return Err(Err::InvalidClauseId(c_id));
    }

    let main = state.clause_set.clauses()[c_id].atoms();

    // Check that (mainAtomID -> (sideClauseID, atomID)) map elements are correct
    for (m_id, (sc_id, sa_id)) in atom_map {
        if *m_id >= main.len() {
            return Err(Err::NoSuchAtomInMain(
                state.clause_set.clauses()[*m_id].clone(),
                *m_id,
            ));
        }
        if *sc_id >= state.clause_set.size() {
            return Err(Err::InvalidClauseId(c_id));
        }
        let c = state.clause_set.clauses()[*sc_id].atoms();
        if *sa_id >= c.len() {
            return Err(Err::NoSuchAtomInSide(
                state.clause_set.clauses()[*sa_id].clone(),
                *sa_id,
            ));
        }
    }

    Ok(())
}

impl Serialize for State {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("PropResState", 6)?;
        state.serialize_field("clauseSet", &self.clause_set)?;
        state.serialize_field("visualHelp", &self.visual_help)?;
        state.serialize_field(
            "newestNode",
            &match self.newest_node {
                Some(n) => n as i32,
                _ => -1,
            },
        )?;
        state.serialize_field("hiddenClauses", &self.hidden_clauses)?;
        state.serialize_field("lastMove", &self.last_move)?;
        state.serialize_field("seal", &self.seal())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for State {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "clauseSet")]
            ClauseSet,
            #[serde(rename = "visualHelp")]
            VisualHelp,
            #[serde(rename = "newestNode")]
            NewestNode,
            #[serde(rename = "hiddenClauses")]
            HiddenClauses,
            #[serde(rename = "lastMove")]
            LastMove,
            #[serde(rename = "seal")]
            Seal,
        }

        struct StateVisitor;

        impl<'de> Visitor<'de> for StateVisitor {
            type Value = State;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct PropResState")
            }

            fn visit_map<V>(self, mut map: V) -> Result<State, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut clause_set: Option<ClauseSet<Symbol>> = None;
                let mut visual_help: Option<VisualHelp> = None;
                let mut newest_node: Option<i32> = None;
                let mut hidden_clauses: Option<ClauseSet<Symbol>> = None;
                let mut last_move: Option<Move> = None;
                let mut seal: Option<String> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::ClauseSet => {
                            if clause_set.is_some() {
                                return Err(de::Error::duplicate_field("clauseSet"));
                            }
                            clause_set = Some(map.next_value()?);
                        }
                        Field::VisualHelp => {
                            if visual_help.is_some() {
                                return Err(de::Error::duplicate_field("visualHelp"));
                            }
                            visual_help = Some(map.next_value()?);
                        }
                        Field::NewestNode => {
                            if newest_node.is_some() {
                                return Err(de::Error::duplicate_field("newestNode"));
                            }
                            newest_node = Some(map.next_value()?);
                        }
                        Field::HiddenClauses => {
                            if hidden_clauses.is_some() {
                                return Err(de::Error::duplicate_field("hiddenClauses"));
                            }
                            hidden_clauses = Some(map.next_value()?);
                        }
                        Field::LastMove => {
                            if last_move.is_some() {
                                return Err(de::Error::duplicate_field("lastMove"));
                            }
                            last_move = map.next_value()?;
                        }
                        Field::Seal => {
                            if seal.is_some() {
                                return Err(de::Error::duplicate_field("seal"));
                            }
                            seal = Some(map.next_value()?);
                        }
                    }
                }

                let clause_set = clause_set.ok_or_else(|| de::Error::missing_field("clauseSet"))?;
                let visual_help =
                    visual_help.ok_or_else(|| de::Error::missing_field("visualHelp"))?;
                let newest_node =
                    newest_node.ok_or_else(|| de::Error::missing_field("newestNode"))?;
                let newest_node = if newest_node >= 0 {
                    Some(newest_node as usize)
                } else if newest_node == -1 {
                    None
                } else {
                    return Err(de::Error::invalid_value(
                        de::Unexpected::Signed(newest_node.into()),
                        &"A value between -1 and max int",
                    ));
                };
                let hidden_clauses =
                    hidden_clauses.ok_or_else(|| de::Error::missing_field("hiddenClauses"))?;
                let seal = seal.ok_or_else(|| de::Error::missing_field("seal"))?;

                let s = State {
                    clause_set,
                    visual_help,
                    newest_node,
                    last_move,
                    hidden_clauses,
                };

                if !s.verify_seal(&seal) {
                    Err(de::Error::invalid_value(
                        de::Unexpected::Str("Invalid tamper protection seal"),
                        &"Unmodified state and corresponding seal",
                    ))
                } else {
                    Ok(s)
                }
            }
        }

        const FIELDS: &[&str] = &[
            "clause_set",
            "visualHelp",
            "newestNode",
            "lastMove",
            "hiddenClauses",
            "seal",
        ];
        deserializer.deserialize_struct("PropResState", FIELDS, StateVisitor)
    }
}

impl Serialize for Move {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (ty, num_fields) = match self {
            Move::Resolve(..) => ("res-resolve", 4),
            Move::Hide(_) => ("res-hide", 2),
            Move::Show => ("res-show", 1),
            Move::Hyper(..) => ("res-hyper", 3),
            Move::Factorize(_) => ("res-factorize", 2),
        };
        let mut state = serializer.serialize_struct("PropResMove", num_fields)?;
        state.serialize_field("type", ty)?;
        match self {
            Move::Resolve(c1, c2, literal) => {
                state.serialize_field("c1", c1)?;
                state.serialize_field("c2", c2)?;
                state.serialize_field("literal", literal)?;
            }
            Move::Hide(c1) => {
                state.serialize_field("c1", c1)?;
            }
            Move::Show => {}
            Move::Hyper(main_id, atom_map) => {
                state.serialize_field("mainID", main_id)?;
                state.serialize_field("atomMap", atom_map)?;
            }
            Move::Factorize(c1) => {
                state.serialize_field("c1", c1)?;
                let empty: Vec<usize> = Vec::new();
                state.serialize_field("atoms", &empty)?;
            }
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for Move {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "type")]
            Ty,
            #[serde(rename = "c1")]
            C1,
            #[serde(rename = "c2")]
            C2,
            #[serde(rename = "literal")]
            Literal,
            #[serde(rename = "mainID")]
            MainId,
            #[serde(rename = "atomMap")]
            AtomMap,
            #[serde(rename = "atoms")]
            Atoms,
        }

        struct MoveVisitor;

        impl<'de> Visitor<'de> for MoveVisitor {
            type Value = Move;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct PropResMove")
            }

            fn visit_map<V>(self, mut map: V) -> Result<Move, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut c1: Option<usize> = None;
                let mut c2: Option<usize> = None;
                let mut lit: Option<String> = None;
                let mut main_id: Option<usize> = None;
                let mut atom_map: Option<HashMap<usize, (usize, usize)>> = None;
                let mut atoms: Option<Vec<usize>> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Ty => {
                            if ty.is_some() {
                                return Err(de::Error::duplicate_field("type"));
                            }
                            ty = Some(map.next_value()?);
                        }
                        Field::C1 => {
                            if c1.is_some() {
                                return Err(de::Error::duplicate_field("c1"));
                            }
                            c1 = Some(map.next_value()?);
                        }
                        Field::C2 => {
                            if c2.is_some() {
                                return Err(de::Error::duplicate_field("c2"));
                            }
                            c2 = Some(map.next_value()?);
                        }
                        Field::Literal => {
                            if lit.is_some() {
                                return Err(de::Error::duplicate_field("literal"));
                            }
                            lit = Some(map.next_value()?);
                        }
                        Field::MainId => {
                            if main_id.is_some() {
                                return Err(de::Error::duplicate_field("mainID"));
                            }
                            main_id = Some(map.next_value()?);
                        }
                        Field::AtomMap => {
                            if atom_map.is_some() {
                                return Err(de::Error::duplicate_field("atomMap"));
                            }
                            atom_map = Some(map.next_value()?);
                        }
                        Field::Atoms => {
                            if atoms.is_some() {
                                return Err(de::Error::duplicate_field("atoms"));
                            }
                            atoms = Some(map.next_value()?);
                        }
                    }
                }

                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                let ty: &str = &ty;
                Ok(match ty {
                    "res-resolve" => Move::Resolve(
                        c1.ok_or_else(|| de::Error::missing_field("c1"))?,
                        c2.ok_or_else(|| de::Error::missing_field("c2"))?,
                        lit.map(|s| Symbol::intern(&s)),
                    ),
                    "res-hide" => Move::Hide(c1.ok_or_else(|| de::Error::missing_field("c1"))?),
                    "res-show" => Move::Show,
                    "res-hyper" => Move::Hyper(
                        main_id.ok_or_else(|| de::Error::missing_field("mainID"))?,
                        atom_map.ok_or_else(|| de::Error::missing_field("atomMap"))?,
                    ),
                    "res-factorize" => {
                        Move::Factorize(c1.ok_or_else(|| de::Error::missing_field("c1"))?)
                    }
                    _ => todo!(),
                })
            }
        }

        const FIELDS: &[&str] = &["type", "c1", "c2", "literal", "mainID", "atomMap", "atoms"];
        deserializer.deserialize_struct("PropResMove", FIELDS, MoveVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session;

    mod check_close {
        use super::*;

        #[test]
        fn simple() {
            session(|| {
                let s = PropResolution::parse_formula("a;!a", None).unwrap();
                assert!(!PropResolution::check_close(s.clone()).closed);

                let s = PropResolution::apply_move(s, Move::Resolve(0, 1, None)).unwrap();
                assert!(PropResolution::check_close(s).closed);
            })
        }

        #[test]
        fn simple2() {
            session(|| {
                let s = PropResolution::parse_formula("a,b;!a;!b", None).unwrap();
                assert!(!PropResolution::check_close(s.clone()).closed);

                let s = PropResolution::apply_move(s, Move::Resolve(0, 1, None)).unwrap();
                let s =
                    PropResolution::apply_move(s, Move::Resolve(3, 1, Some("b".into()))).unwrap();
                assert!(PropResolution::check_close(s).closed);
            })
        }

        #[test]
        fn complex() {
            session(|| {
                let s =
                    PropResolution::parse_formula("a,b,!c,d;!a,b,d;!b,!c,d;!d;c", None).unwrap();
                assert!(!PropResolution::check_close(s.clone()).closed);

                let s = PropResolution::apply_move(s, Move::Resolve(0, 1, None)).unwrap();
                let s =
                    PropResolution::apply_move(s, Move::Resolve(1, 3, Some("b".into()))).unwrap();
                let s =
                    PropResolution::apply_move(s, Move::Resolve(3, 5, Some("d".into()))).unwrap();
                assert!(!PropResolution::check_close(s.clone()).closed);

                let s =
                    PropResolution::apply_move(s, Move::Resolve(5, 7, Some("c".into()))).unwrap();
                assert!(PropResolution::check_close(s).closed);
            })
        }

        #[test]
        fn negative() {
            session(|| {
                let s = PropResolution::parse_formula("a,b,c;!a;!b", None).unwrap();
                assert!(!PropResolution::check_close(s.clone()).closed);

                let s = PropResolution::apply_move(s, Move::Resolve(0, 1, None)).unwrap();
                let s =
                    PropResolution::apply_move(s, Move::Resolve(3, 1, Some("b".into()))).unwrap();
                assert!(!PropResolution::check_close(s).closed);
            })
        }
    }

    mod factorize {
        use super::*;

        #[test]
        fn invalid_clause() {
            session(|| {
                let s = PropResolution::parse_formula("a;!a", None).unwrap();
                assert!(PropResolution::apply_move(s, Move::Factorize(2)).is_err());
            })
        }

        #[test]
        fn nothing_to_fact() {
            session(|| {
                let s = PropResolution::parse_formula("a;a,b,c", None).unwrap();
                assert!(PropResolution::apply_move(s.clone(), Move::Factorize(0)).is_err());
                assert!(PropResolution::apply_move(s, Move::Factorize(1)).is_err());
            })
        }

        #[test]
        fn prop_f() {
            session(|| {
                let s = PropResolution::parse_formula("a;a,b,c,a,b,c", None).unwrap();
                let s = PropResolution::apply_move(s, Move::Factorize(1)).unwrap();
                assert_eq!(2, s.clause_set.size());
                assert_eq!("{a, b, c}", s.clause_set.clauses()[1].to_string())
            })
        }

        #[test]
        fn clause_positioning() {
            session(|| {
                let s = PropResolution::parse_formula("a;b,b;c;d;e", None).unwrap();
                let s = PropResolution::apply_move(s, Move::Factorize(1)).unwrap();
                assert_eq!("{b}", s.clause_set.clauses()[1].to_string())
            })
        }
    }
}
