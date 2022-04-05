use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{
    calculus::CloseMsg,
    clause::{Atom, Clause, ClauseSet},
    logic::{
        fo::Relation,
        transform::{
            fo_cnf::FOCNFErr,
            term_manipulator::{VariableSuffixAppend, VariableSuffixStripper},
            visitor::FOTermVisitor,
        },
        unify::{
            try_to_parse_unifier, unifier_eq::is_mgu_or_not_unifiable, unify, unify_all,
            Substitution, UnificationErr,
        },
    },
    parse::{parse_fo_flexibly_to_cnf, FOToCNFParseErr, ParseErr},
    tamper_protect::ProtectedState,
    Calculus, Symbol,
};

use super::{
    util::{build_clause, filter_clause, UtilErr},
    VisualHelp,
};

#[derive(Deserialize, Serialize, Default)]
#[serde(rename_all = "camelCase")]
#[serde(default)]
pub struct Params {
    visual_help: VisualHelp,
}

#[derive(Debug)]
pub enum Err {
    ParseErr(ParseErr),
    CNFErr(FOCNFErr),
    UnificationErr(UnificationErr),
    UtilErr(UtilErr<Relation>),
    InvalidClauseId(usize),
    NoSuchAtom(Clause<Relation>, usize),
    TooFewAtoms,
    NEAfterInst(Atom<Relation>, Atom<Relation>),
    NoSuchAtomInMain(Clause<Relation>, usize),
    NoSuchAtomInSide(Clause<Relation>, usize),
    EmptyHyperMap,
    SidePremissNotPos(Clause<Relation>),
    MainAtomNotNeg(Atom<Relation>),
    ResultingMainNotPos(Clause<Relation>),
    CannotUnifyWithSelf,
}

impl From<ParseErr> for Err {
    fn from(e: ParseErr) -> Self {
        Self::ParseErr(e)
    }
}

impl From<FOCNFErr> for Err {
    fn from(e: FOCNFErr) -> Self {
        Self::CNFErr(e)
    }
}

impl From<FOToCNFParseErr> for Err {
    fn from(e: FOToCNFParseErr) -> Self {
        match e {
            FOToCNFParseErr::ParseErr(e) => Self::ParseErr(e),
            FOToCNFParseErr::CNFErr(e) => Self::CNFErr(e),
        }
    }
}

impl From<UnificationErr> for Err {
    fn from(e: UnificationErr) -> Self {
        Self::UnificationErr(e)
    }
}

impl From<UtilErr<Relation>> for Err {
    fn from(e: UtilErr<Relation>) -> Self {
        Self::UtilErr(e)
    }
}

impl fmt::Display for Err {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Err::ParseErr(e) => fmt::Display::fmt(e, f),
            Err::CNFErr(e) => fmt::Display::fmt(e, f),
            Err::UnificationErr(e) => fmt::Display::fmt(e, f),
            Err::UtilErr(e) => fmt::Display::fmt(e, f),
            Err::InvalidClauseId(c) => write!(f, "There is no clause with id {c}"),
            Err::NoSuchAtom(c, id) => {
                write!(f, "There is no atom with id {id} in clause '{c}'")
            }
            Err::TooFewAtoms => write!(f, "Please select more than 1 atom to factorize"),
            Err::NEAfterInst(a1, a2) => write!(
                f,
                "Atoms '${a1}' and '${a2}' are not equal after instantiation"
            ),
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
            Err::CannotUnifyWithSelf => write!(f, "Cannot unify an atom with itself"),
        }
    }
}

pub type FOResResult<T> = Result<T, Err>;

#[derive(Debug, Clone)]
pub struct State {
    pub clause_set: ClauseSet<Relation>,
    pub visual_help: VisualHelp,
    pub newest_node: Option<usize>,
    pub hidden_clauses: ClauseSet<Relation>,
    pub clause_counter: u32,
    pub status_msg: Option<String>,
    pub last_move: Option<Move>,
}

impl State {
    pub fn new(clause_set: ClauseSet<Relation>, visual_help: VisualHelp) -> Self {
        Self {
            clause_set,
            visual_help,
            newest_node: None,
            hidden_clauses: ClauseSet::new(vec![]),
            clause_counter: 0,
            status_msg: None,
            last_move: None,
        }
    }

    fn set_suffix(&mut self, c_id: usize) {
        self.clause_counter += 1;
        let c = &self.clause_set.clauses()[c_id];

        let stripper = VariableSuffixStripper("_");
        let appender = VariableSuffixAppend(Symbol::intern(&format!("_{}", self.clause_counter)));

        let mut atoms = vec![];

        for a in c {
            let r = Relation::new(
                a.lit().spelling,
                a.lit()
                    .args
                    .iter()
                    .map(|t| appender.visit(&stripper.visit(t)))
                    .collect(),
            );
            atoms.push(Atom::new(r, a.negated()));
        }

        self.clause_set.replace(c_id, Clause::new(atoms));
    }

    fn init_suffix(&mut self) {
        for i in 0..self.clause_set.size() {
            self.set_suffix(i);
        }
    }
}

#[derive(Debug, Clone)]
pub enum Move {
    ResolveUnify(usize, usize, usize, usize),
    ResolveCustom(usize, usize, usize, usize, Substitution),
    Hide(usize),
    Show,
    Hyper(usize, HashMap<usize, (usize, usize)>),
    Factorize(usize, Vec<usize>),
}

impl ProtectedState for State {
    fn compute_seal_info(&self) -> String {
        format!(
            "resolutionstate|{}|{}|{}|{}|{}",
            self.clause_set,
            self.hidden_clauses,
            self.visual_help,
            match self.newest_node {
                Some(n) => n as i32,
                _ => -1,
            },
            self.clause_counter
        )
    }
}

pub struct FOResolution;

impl<'f> Calculus<'f> for FOResolution {
    type Params = Params;

    type State = State;

    type Move = Move;

    type Error = Err;

    fn parse_formula(
        formula: &'f str,
        params: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        let cs = parse_fo_flexibly_to_cnf(formula)?;

        let mut s = State::new(cs, params.unwrap_or_default().visual_help);

        // Distinguish variables in each clause by appending suffixes
        s.init_suffix();
        Ok(s)
    }

    fn apply_move(mut state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        state.status_msg.take();

        state = match k_move.clone() {
            Move::ResolveUnify(c1, c2, l1, l2) => apply_resolve_unify(state, c1, c2, l1, l2)?,
            Move::ResolveCustom(c1, c2, l1, l2, u) => {
                apply_resolve_custom(state, c1, c2, l1, l2, u)?
            }
            Move::Hide(c) => apply_hide(state, c)?,
            Move::Show => apply_show(state),
            Move::Hyper(c, m) => apply_hyper(state, c, m)?,
            Move::Factorize(c, a) => apply_factorize(state, c, a)?,
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

fn apply_resolve_unify(
    state: State,
    c1: usize,
    c2: usize,
    l1: usize,
    l2: usize,
) -> FOResResult<State> {
    resolve_check_ids(&state, c1, c2, l1, l2)?;

    let cl1 = &state.clause_set.clauses()[c1];
    let cl2 = &state.clause_set.clauses()[c2];
    let lit1 = cl1.atoms()[l1].lit();
    let lit2 = cl2.atoms()[l2].lit();

    let mgu = unify(lit1, lit2)?;

    apply_resolve(state, c1, c2, l1, mgu)
}

fn apply_resolve_custom(
    mut state: State,
    c1: usize,
    c2: usize,
    l1: usize,
    l2: usize,
    u: Substitution,
) -> FOResResult<State> {
    resolve_check_ids(&state, c1, c2, l1, l2)?;

    let cl1 = &state.clause_set.clauses()[c1];
    let cl2 = &state.clause_set.clauses()[c2];
    let lit1 = cl1.atoms()[l1].lit();
    let lit2 = cl2.atoms()[l2].lit();

    if !is_mgu_or_not_unifiable(&u, lit1, lit2) {
        state.status_msg = Some("The unifier you specified is not an MGU".to_string());
        return Ok(state);
    }

    apply_resolve(state, c1, c2, l1, u)
}

fn apply_hide(mut state: State, c: usize) -> FOResResult<State> {
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
    main_id: usize,
    atom_map: HashMap<usize, (usize, usize)>,
) -> FOResResult<State> {
    check_hyper(&state, main_id, &atom_map)?;

    if atom_map.is_empty() {
        return Err(Err::EmptyHyperMap);
    }

    let main_premiss = state.clause_set.clauses()[main_id].clone();
    let mut rels = Vec::new();

    for (ma_id, (sc_id, sa_id)) in &atom_map {
        let ma_id = *ma_id;
        let sc_id = *sc_id;
        let sa_id = *sa_id;

        let side = &state.clause_set.clauses()[sc_id];

        // Check side premise for positiveness
        if !side.is_positive() {
            return Err(Err::SidePremissNotPos(side.clone()));
        }

        let ma = &state.clause_set.clauses()[main_id].atoms()[ma_id];
        if !ma.negated() {
            return Err(Err::MainAtomNotNeg(ma.clone()));
        }
        let sa = &state.clause_set.clauses()[sc_id].atoms()[sa_id];

        rels.push((ma.lit(), sa.lit()));
    }

    let mgu = unify_all(rels)?;

    let mut new_main = main_premiss.instantiate(&mgu);

    for (ma_id, (sc_id, sa_id)) in atom_map {
        let side = state.clause_set.clauses()[sc_id].instantiate(&mgu);

        new_main = build_clause(
            &new_main,
            main_premiss.atoms()[ma_id].instantiate(&mgu),
            &side,
            side.atoms()[sa_id].clone(),
        );
    }

    if !new_main.is_positive() {
        return Err(Err::ResultingMainNotPos(main_premiss));
    }

    state.clause_set.add(new_main);
    state.newest_node = Some(state.clause_set.size() - 1);

    Ok(state)
}

fn apply_factorize(mut state: State, c: usize, atoms: Vec<usize>) -> FOResResult<State> {
    if c >= state.clause_set.size() {
        return Err(Err::InvalidClauseId(c));
    }
    if atoms.len() < 2 {
        return Err(Err::TooFewAtoms);
    }

    let c = &state.clause_set.clauses()[c];
    let mut first: Option<&Atom<Relation>> = None;
    let mut to_unify = Vec::new();
    let last = *atoms.last().unwrap();
    let mut seen_ids = HashSet::new();

    for i in atoms.iter() {
        let i = *i;
        if !seen_ids.insert(i) {
            return Err(Err::CannotUnifyWithSelf);
        }
        if i >= c.atoms().len() {
            return Err(Err::NoSuchAtom(c.clone(), i));
        }
        let a = &c.atoms()[i];
        match first {
            Some(f) => {
                if f.negated() != a.negated() {
                    return Err(Err::NEAfterInst(f.clone(), a.clone()));
                }
                to_unify.push((f.lit(), a.lit()));
            }
            _ => {
                first = Some(a);
            }
        }
    }

    let mgu = unify_all(to_unify)?;
    let atoms = c
        .atoms()
        .iter()
        .enumerate()
        .filter_map(|(i, a)| {
            if i != last && atoms.contains(&i) {
                None
            } else {
                Some(a.instantiate(&mgu))
            }
        })
        .collect();

    let nc = Clause::new(atoms);
    let idx = state.clause_set.size();
    state.newest_node = Some(idx);
    state.clause_set.add(nc);
    state.set_suffix(idx);

    Ok(state)
}

fn apply_resolve(
    mut state: State,
    c1: usize,
    c2: usize,
    l1: usize,
    u: Substitution,
) -> FOResResult<State> {
    let cl1 = &state.clause_set.clauses()[c1];
    let cl2 = &state.clause_set.clauses()[c2];
    let lit1 = cl1.atoms()[l1].lit();

    let icl1 = cl1.instantiate(&u);
    let icl2 = cl2.instantiate(&u);
    let il = lit1.instantiate(&u);

    let (a1, a2) = filter_clause(&icl1, &icl2, &il)?;

    let nc = build_clause(&icl1, a1, &icl2, a2);

    let idx = state.clause_set.size();
    state.newest_node = Some(idx);
    state.clause_set.add(nc);
    state.set_suffix(idx);

    Ok(state)
}

fn resolve_check_ids(state: &State, c1: usize, c2: usize, l1: usize, l2: usize) -> FOResResult<()> {
    if c1 >= state.clause_set.size() {
        Err(Err::InvalidClauseId(c1))
    } else if c2 >= state.clause_set.size() {
        Err(Err::InvalidClauseId(c2))
    } else {
        let c1 = &state.clause_set.clauses()[c1];
        let c2 = &state.clause_set.clauses()[c2];

        if l1 >= c1.atoms().len() {
            Err(Err::NoSuchAtom(c1.clone(), l1))
        } else if l2 >= c2.atoms().len() {
            Err(Err::NoSuchAtom(c2.clone(), l2))
        } else {
            Ok(())
        }
    }
}

fn check_hyper(
    state: &State,
    c_id: usize,
    atom_map: &HashMap<usize, (usize, usize)>,
) -> FOResResult<()> {
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
        let mut state = serializer.serialize_struct("FOResState", 8)?;
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
        state.serialize_field("clauseCounter", &self.clause_counter)?;
        state.serialize_field("statusMessage", &self.status_msg)?;
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
            #[serde(rename = "clauseCounter")]
            ClauseCounter,
            #[serde(rename = "statusMessage")]
            StatusMsg,
            #[serde(rename = "lastMove")]
            LastMove,
            #[serde(rename = "seal")]
            Seal,
        }

        struct StateVisitor;

        impl<'de> Visitor<'de> for StateVisitor {
            type Value = State;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct FOResState")
            }

            fn visit_map<V>(self, mut map: V) -> Result<State, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut clause_set: Option<ClauseSet<Relation>> = None;
                let mut visual_help: Option<VisualHelp> = None;
                let mut newest_node: Option<i32> = None;
                let mut hidden_clauses: Option<ClauseSet<Relation>> = None;
                let mut last_move: Option<Move> = None;
                let mut clause_counter: Option<u32> = None;
                let mut status_msg: Option<String> = None;
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
                            last_move = Some(map.next_value()?);
                        }
                        Field::ClauseCounter => {
                            if clause_counter.is_some() {
                                return Err(de::Error::duplicate_field("clauseCounter"));
                            }
                            clause_counter = Some(map.next_value()?);
                        }
                        Field::StatusMsg => {
                            if status_msg.is_some() {
                                return Err(de::Error::duplicate_field("statusMessage"));
                            }
                            status_msg = Some(map.next_value()?);
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
                let clause_counter =
                    clause_counter.ok_or_else(|| de::Error::missing_field("clauseCounter"))?;
                let seal = seal.ok_or_else(|| de::Error::missing_field("seal"))?;

                let s = State {
                    clause_set,
                    visual_help,
                    newest_node,
                    last_move,
                    hidden_clauses,
                    clause_counter,
                    status_msg,
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
            Move::ResolveUnify(..) => ("res-resolveunify", 5),
            Move::ResolveCustom(..) => ("res-resolvecustom", 6),
            Move::Hide(_) => ("res-hide", 2),
            Move::Show => ("res-show", 1),
            Move::Hyper(..) => ("res-hyper", 3),
            Move::Factorize(..) => ("res-factorize", 3),
        };
        let mut state = serializer.serialize_struct("FOResMove", num_fields)?;
        state.serialize_field("type", ty)?;
        match self {
            Move::ResolveUnify(c1, c2, l1, l2) => {
                state.serialize_field("c1", c1)?;
                state.serialize_field("c2", c2)?;
                state.serialize_field("l1", l1)?;
                state.serialize_field("l2", l2)?;
            }
            Move::ResolveCustom(c1, c2, l1, l2, u) => {
                state.serialize_field("c1", c1)?;
                state.serialize_field("c2", c2)?;
                state.serialize_field("l1", l1)?;
                state.serialize_field("l2", l2)?;
                state.serialize_field("varAssign", &u.rendered_map())?;
            }
            Move::Hide(c1) => {
                state.serialize_field("c1", c1)?;
            }
            Move::Show => {}
            Move::Hyper(main_id, atom_map) => {
                state.serialize_field("mainID", main_id)?;
                state.serialize_field("atomMap", atom_map)?;
            }
            Move::Factorize(c, atoms) => {
                state.serialize_field("c1", c)?;
                state.serialize_field("atoms", atoms)?;
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
            #[serde(rename = "l1")]
            L1,
            #[serde(rename = "l2")]
            L2,
            #[serde(rename = "varAssign")]
            VarAssign,
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
                formatter.write_str("struct FOResMove")
            }

            fn visit_map<V>(self, mut map: V) -> Result<Move, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut c1: Option<usize> = None;
                let mut c2: Option<usize> = None;
                let mut l1: Option<usize> = None;
                let mut l2: Option<usize> = None;
                let mut var_assign: Option<HashMap<Symbol, String>> = None;
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
                        Field::L1 => {
                            if l1.is_some() {
                                return Err(de::Error::duplicate_field("l1"));
                            }
                            l1 = Some(map.next_value()?);
                        }
                        Field::L2 => {
                            if l2.is_some() {
                                return Err(de::Error::duplicate_field("l2"));
                            }
                            l2 = Some(map.next_value()?);
                        }
                        Field::VarAssign => {
                            if var_assign.is_some() {
                                return Err(de::Error::duplicate_field("varAssign"));
                            }
                            var_assign = Some(map.next_value()?);
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
                    "res-resolveunify" => Move::ResolveUnify(
                        c1.ok_or_else(|| de::Error::missing_field("c1"))?,
                        c2.ok_or_else(|| de::Error::missing_field("c2"))?,
                        l1.ok_or_else(|| de::Error::missing_field("l1"))?,
                        l2.ok_or_else(|| de::Error::missing_field("l2"))?,
                    ),
                    "res-resolvecustom" => Move::ResolveCustom(
                        c1.ok_or_else(|| de::Error::missing_field("c1"))?,
                        c2.ok_or_else(|| de::Error::missing_field("c2"))?,
                        l1.ok_or_else(|| de::Error::missing_field("l1"))?,
                        l2.ok_or_else(|| de::Error::missing_field("l2"))?,
                        {
                            let v =
                                var_assign.ok_or_else(|| de::Error::missing_field("varAssign"))?;
                            match try_to_parse_unifier(v) {
                                Ok(u) => u,
                                Err(e) => return Err(de::Error::custom(e.to_string())),
                            }
                        },
                    ),
                    "res-hide" => Move::Hide(c1.ok_or_else(|| de::Error::missing_field("c1"))?),
                    "res-show" => Move::Show,
                    "res-hyper" => Move::Hyper(
                        main_id.ok_or_else(|| de::Error::missing_field("mainID"))?,
                        atom_map.ok_or_else(|| de::Error::missing_field("atomMap"))?,
                    ),
                    "res-factorize" => Move::Factorize(
                        c1.ok_or_else(|| de::Error::missing_field("c1"))?,
                        atoms.ok_or_else(|| de::Error::missing_field("atoms"))?,
                    ),
                    _ => todo!(),
                })
            }
        }

        const FIELDS: &[&str] = &[
            "type",
            "c1",
            "c2",
            "l1",
            "l2",
            "varAssign",
            "mainID",
            "atomMap",
            "atoms",
        ];
        deserializer.deserialize_struct("FOResMove", FIELDS, MoveVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session;

    // see https://github.com/KalkulierbaR/kalkulierbar/issues/50
    #[test]
    fn issue50() {
        session(|| {
            let s = FOResolution::parse_formula(
                "/all M: /all N: (Subset(M, N) <-> /all A: (In(A, M) -> In(A, N)))",
                None,
            )
            .unwrap();
            let expected = "{!Subset(M_1, N_1), !In(A_1, M_1), In(A_1, N_1)}, {Subset(M_2, N_2), In(sk1(M_2, N_2), M_2)}, {Subset(M_3, N_3), !In(sk1(M_3, N_3), N_3)}";
            assert_eq!(expected, s.clause_set.to_string());
        })
    }

    mod factorize {
        use super::*;

        #[test]
        fn invalid_clause() {
            session(|| {
                let s = FOResolution::parse_formula("P(c) & R(c) | R(y)", None).unwrap();
                assert!(FOResolution::apply_move(s, Move::Factorize(2, vec![0, 1])).is_err());
            })
        }

        #[test]
        fn invalid_atom() {
            session(|| {
                let s = FOResolution::parse_formula("R(c) | R(y)", None).unwrap();
                assert!(
                    FOResolution::apply_move(s.clone(), Move::Factorize(0, vec![0, 0])).is_err()
                );
                assert!(
                    FOResolution::apply_move(s.clone(), Move::Factorize(0, vec![2, 0])).is_err()
                );
                assert!(FOResolution::apply_move(s, Move::Factorize(0, vec![1, 2])).is_err());
            })
        }

        #[test]
        fn unification_fail() {
            session(|| {
                let s = FOResolution::parse_formula("R(c) | R(y)", None).unwrap();
                assert!(FOResolution::apply_move(s, Move::Factorize(0, vec![0, 1])).is_err());

                let s = FOResolution::parse_formula("\\all X: (R(X) | R(f(X)))", None).unwrap();
                assert!(FOResolution::apply_move(s, Move::Factorize(0, vec![0, 1])).is_err());

                let s =
                    FOResolution::parse_formula("\\all X: \\all Y: (R(X,X) | R(Y))", None).unwrap();
                assert!(FOResolution::apply_move(s, Move::Factorize(0, vec![0, 1])).is_err());
            })
        }

        #[test]
        fn fo_f() {
            session(|| {
                let s = FOResolution::parse_formula(
                    "\\all X: (Q(z) | R(X,c) | R(f(c),c) | Q(y))",
                    None,
                )
                .unwrap();
                let s = FOResolution::apply_move(s, Move::Factorize(0, vec![1, 2])).unwrap();
                assert_eq!(2, s.clause_set.size());
                assert_eq!(
                    "{Q(z), R(f(c), c), Q(y)}",
                    s.clause_set.clauses()[1].to_string()
                );
                assert_eq!(
                    "{Q(z), R(X_1, c), R(f(c), c), Q(y)}",
                    s.clause_set.clauses()[0].to_string()
                );
            })
        }

        #[test]
        fn clause_positioning() {
            session(|| {
                let s = FOResolution::parse_formula("Q(a) & (R(z) | R(z)) & Q(b) & Q(c)", None)
                    .unwrap();
                let s = FOResolution::apply_move(s, Move::Factorize(1, vec![0, 1])).unwrap();
                assert_eq!("{R(z)}", s.clause_set.clauses()[4].to_string());
                assert_eq!("{R(z), R(z)}", s.clause_set.clauses()[1].to_string());
            })
        }

        #[test]
        fn multiple() {
            session(|| {
                let s = FOResolution::parse_formula("/all X: (Q(f(X)) | Q(f(c)) | Q(f(X)))", None)
                    .unwrap();
                let s = FOResolution::apply_move(s, Move::Factorize(0, vec![0, 1, 2])).unwrap();
                assert_eq!("{Q(f(c))}", s.clause_set.clauses()[1].to_string());
            })
        }

        #[test]
        fn multiple_invalid() {
            session(|| {
                let s = FOResolution::parse_formula("/all X: (Q(X) | Q(g(c)) | Q(f(X)))", None)
                    .unwrap();
                assert!(FOResolution::apply_move(s, Move::Factorize(0, vec![0, 1, 2])).is_err());
            })
        }
    }
}
