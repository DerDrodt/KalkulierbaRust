use std::{collections::HashMap, fmt};

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
            fo_cnf::{fo_cnf, FOCNFErr},
            term_manipulator::{VariableSuffixAppend, VariableSuffixStripper},
            visitor::FOTermVisitor,
        },
        unify::{unifier_eq::is_mgu_or_not_unifiable, unify, unify_all, UnificationErr, Unifier},
    },
    parse::{fo::parse_fo_formula, ParseErr},
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
pub struct FOResParam {
    visual_help: VisualHelp,
}

pub enum FOResErr {
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
}

impl From<ParseErr> for FOResErr {
    fn from(e: ParseErr) -> Self {
        Self::ParseErr(e)
    }
}

impl From<FOCNFErr> for FOResErr {
    fn from(e: FOCNFErr) -> Self {
        Self::CNFErr(e)
    }
}

impl From<UnificationErr> for FOResErr {
    fn from(e: UnificationErr) -> Self {
        Self::UnificationErr(e)
    }
}

impl From<UtilErr<Relation>> for FOResErr {
    fn from(e: UtilErr<Relation>) -> Self {
        Self::UtilErr(e)
    }
}

pub type FOResResult<T> = Result<T, FOResErr>;

pub struct FOResState {
    clause_set: ClauseSet<Relation>,
    visual_help: VisualHelp,
    newest_node: Option<usize>,
    hidden_clauses: ClauseSet<Relation>,
    clause_counter: u32,
    status_msg: Option<String>,
    last_move: Option<FOResMove>,
}

impl FOResState {
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
pub enum FOResMove {
    ResolveUnify(usize, usize, usize, usize),
    ResolveCustom(usize, usize, usize, usize, Unifier),
    Hide(usize),
    Show,
    Hyper(usize, HashMap<usize, (usize, usize)>),
    Factorize(usize, Vec<usize>),
}

impl ProtectedState for FOResState {
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
    type Params = FOResParam;

    type State = FOResState;

    type Move = FOResMove;

    type Error = FOResErr;

    fn parse_formula(
        formula: &'f str,
        params: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        let fo = parse_fo_formula(formula)?;
        let cs = fo_cnf(fo)?;

        let mut s = FOResState::new(cs, params.unwrap_or_default().visual_help);

        // Distinguish variables in each clause by appending suffixes
        s.init_suffix();
        Ok(s)
    }

    fn apply_move(mut state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        state.status_msg.take();

        state = match k_move.clone() {
            FOResMove::ResolveUnify(c1, c2, l1, l2) => apply_resolve_unify(state, c1, c2, l1, l2)?,
            FOResMove::ResolveCustom(c1, c2, l1, l2, u) => {
                apply_resolve_custom(state, c1, c2, l1, l2, u)?
            }
            FOResMove::Hide(c) => apply_hide(state, c)?,
            FOResMove::Show => apply_show(state),
            FOResMove::Hyper(c, m) => apply_hyper(state, c, m)?,
            FOResMove::Factorize(c, a) => apply_factorize(state, c, a)?,
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
    state: FOResState,
    c1: usize,
    c2: usize,
    l1: usize,
    l2: usize,
) -> FOResResult<FOResState> {
    resolve_check_ids(&state, c1, c2, l1, l2)?;

    let cl1 = &state.clause_set.clauses()[c1];
    let cl2 = &state.clause_set.clauses()[c2];
    let lit1 = cl1.atoms()[l1].lit();
    let lit2 = cl2.atoms()[l2].lit();

    let mgu = unify(lit1, lit2)?;

    apply_resolve(state, c1, c2, l1, mgu)
}

fn apply_resolve_custom(
    mut state: FOResState,
    c1: usize,
    c2: usize,
    l1: usize,
    l2: usize,
    u: Unifier,
) -> FOResResult<FOResState> {
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

fn apply_hide(mut state: FOResState, c: usize) -> FOResResult<FOResState> {
    if c >= state.clause_set.size() {
        return Err(FOResErr::InvalidClauseId(c));
    }

    // Move clause from main clause set to hidden clause set
    let c = state.clause_set.remove(c);
    state.hidden_clauses.add(c);
    state.newest_node = None;

    Ok(state)
}

fn apply_show(mut state: FOResState) -> FOResState {
    state.clause_set.unite(&state.hidden_clauses);
    state.hidden_clauses.clear();
    state.newest_node = None;

    state
}

fn apply_hyper(
    mut state: FOResState,
    main_id: usize,
    atom_map: HashMap<usize, (usize, usize)>,
) -> FOResResult<FOResState> {
    check_hyper(&state, main_id, &atom_map)?;

    if atom_map.is_empty() {
        return Err(FOResErr::EmptyHyperMap);
    }

    let main_premiss = state.clause_set.clauses()[main_id].clone();
    let mut rels = Vec::new();

    for (ma_id, (sc_id, sa_id)) in &atom_map {
        let ma_id = *ma_id;
        let sc_id = *sc_id;
        let sa_id = *sa_id;

        let side = &state.clause_set.clauses()[sc_id];

        // Check side premiss for positiveness
        if !side.is_positive() {
            return Err(FOResErr::SidePremissNotPos(side.clone()));
        }

        let ma = &state.clause_set.clauses()[main_id].atoms()[ma_id];
        if !ma.negated() {
            return Err(FOResErr::MainAtomNotNeg(ma.clone()));
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

    if !main_premiss.is_positive() {
        return Err(FOResErr::ResultingMainNotPos(main_premiss));
    }

    state.clause_set.add(main_premiss);
    state.newest_node = Some(state.clause_set.size() - 1);

    Ok(state)
}

fn apply_factorize(mut state: FOResState, c: usize, atoms: Vec<usize>) -> FOResResult<FOResState> {
    if c >= state.clause_set.size() {
        return Err(FOResErr::InvalidClauseId(c));
    }
    if atoms.len() < 2 {
        return Err(FOResErr::TooFewAtoms);
    }

    let c = &state.clause_set.clauses()[c];
    let mut first: Option<&Atom<Relation>> = None;
    let mut to_unify = Vec::new();
    let last = *atoms.last().unwrap();

    for i in atoms.iter() {
        let a = &c.atoms()[*i];
        match first {
            Some(f) => {
                if f.negated() != a.negated() {
                    return Err(FOResErr::NEAfterInst(f.clone(), a.clone()));
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
    mut state: FOResState,
    c1: usize,
    c2: usize,
    l1: usize,
    u: Unifier,
) -> FOResResult<FOResState> {
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

fn resolve_check_ids(
    state: &FOResState,
    c1: usize,
    c2: usize,
    l1: usize,
    l2: usize,
) -> FOResResult<()> {
    if c1 >= state.clause_set.size() {
        Err(FOResErr::InvalidClauseId(c1))
    } else if c2 >= state.clause_set.size() {
        Err(FOResErr::InvalidClauseId(c2))
    } else {
        let c1 = &state.clause_set.clauses()[c1];
        let c2 = &state.clause_set.clauses()[c2];

        if l1 >= c1.atoms().len() {
            Err(FOResErr::NoSuchAtom(c1.clone(), l1))
        } else if l2 >= c2.atoms().len() {
            Err(FOResErr::NoSuchAtom(c2.clone(), l2))
        } else {
            Ok(())
        }
    }
}

fn check_hyper(
    state: &FOResState,
    c_id: usize,
    atom_map: &HashMap<usize, (usize, usize)>,
) -> FOResResult<()> {
    if c_id >= state.clause_set.size() {
        return Err(FOResErr::InvalidClauseId(c_id));
    }

    let main = state.clause_set.clauses()[c_id].atoms();

    // Check that (mainAtomID -> (sideClauseID, atomID)) map elements are correct
    for (m_id, (sc_id, sa_id)) in atom_map {
        if *m_id >= main.len() {
            return Err(FOResErr::NoSuchAtomInMain(
                state.clause_set.clauses()[*m_id].clone(),
                *m_id,
            ));
        }
        if *sc_id >= state.clause_set.size() {
            return Err(FOResErr::InvalidClauseId(c_id));
        }
        let c = state.clause_set.clauses()[*sc_id].atoms();
        if *sa_id >= c.len() {
            return Err(FOResErr::NoSuchAtomInSide(
                state.clause_set.clauses()[*sa_id].clone(),
                *sa_id,
            ));
        }
    }

    Ok(())
}

impl Serialize for FOResState {
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
        state.serialize_field("seal", &self.compute_seal_info())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for FOResState {
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
            type Value = FOResState;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct FOTabState")
            }

            fn visit_map<V>(self, mut map: V) -> Result<FOResState, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut clause_set: Option<ClauseSet<Relation>> = None;
                let mut visual_help: Option<VisualHelp> = None;
                let mut newest_node: Option<i32> = None;
                let mut hidden_clauses: Option<ClauseSet<Relation>> = None;
                let mut last_move: Option<FOResMove> = None;
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

                let s = FOResState {
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

impl Serialize for FOResMove {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (ty, num_fields) = match self {
            FOResMove::ResolveUnify(..) => ("res-resolveunify", 5),
            FOResMove::ResolveCustom(..) => ("res-resolvecustom", 6),
            FOResMove::Hide(_) => ("res-hide", 2),
            FOResMove::Show => ("res-show", 1),
            FOResMove::Hyper(..) => ("res-hyper", 3),
            FOResMove::Factorize(..) => ("res-factorize", 3),
        };
        let mut state = serializer.serialize_struct("FOResMove", num_fields)?;
        state.serialize_field("type", ty)?;
        match self {
            FOResMove::ResolveUnify(c1, c2, l1, l2) => {
                state.serialize_field("c1", c1)?;
                state.serialize_field("c2", c2)?;
                state.serialize_field("l1", l1)?;
                state.serialize_field("l2", l2)?;
            }
            FOResMove::ResolveCustom(c1, c2, l1, l2, u) => {
                state.serialize_field("c1", c1)?;
                state.serialize_field("c2", c2)?;
                state.serialize_field("l1", l1)?;
                state.serialize_field("l2", l2)?;
                state.serialize_field("varAssign", u)?;
            }
            FOResMove::Hide(c1) => {
                state.serialize_field("c1", c1)?;
            }
            FOResMove::Show => {}
            FOResMove::Hyper(main_id, atom_map) => {
                state.serialize_field("mainID", main_id)?;
                state.serialize_field("atomMap", atom_map)?;
            }
            FOResMove::Factorize(c, atoms) => {
                state.serialize_field("c1", c)?;
                state.serialize_field("atoms", atoms)?;
            }
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for FOResMove {
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
            type Value = FOResMove;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct FOResMove")
            }

            fn visit_map<V>(self, mut map: V) -> Result<FOResMove, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut c1: Option<usize> = None;
                let mut c2: Option<usize> = None;
                let mut l1: Option<usize> = None;
                let mut l2: Option<usize> = None;
                let mut var_assign: Option<Unifier> = None;
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
                    "res-resolveunify" => FOResMove::ResolveUnify(
                        c1.ok_or_else(|| de::Error::missing_field("c1"))?,
                        c2.ok_or_else(|| de::Error::missing_field("c2"))?,
                        l1.ok_or_else(|| de::Error::missing_field("l1"))?,
                        l2.ok_or_else(|| de::Error::missing_field("l2"))?,
                    ),
                    "res-resolvecustom" => FOResMove::ResolveCustom(
                        c1.ok_or_else(|| de::Error::missing_field("c1"))?,
                        c2.ok_or_else(|| de::Error::missing_field("c2"))?,
                        l1.ok_or_else(|| de::Error::missing_field("l1"))?,
                        l2.ok_or_else(|| de::Error::missing_field("l2"))?,
                        var_assign.ok_or_else(|| de::Error::missing_field("varAssign"))?,
                    ),
                    "res-hide" => {
                        FOResMove::Hide(c1.ok_or_else(|| de::Error::missing_field("c1"))?)
                    }
                    "res-show" => FOResMove::Show,
                    "res-hyper" => FOResMove::Hyper(
                        main_id.ok_or_else(|| de::Error::missing_field("mainID"))?,
                        atom_map.ok_or_else(|| de::Error::missing_field("atomMap"))?,
                    ),
                    "res-factorize" => FOResMove::Factorize(
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
