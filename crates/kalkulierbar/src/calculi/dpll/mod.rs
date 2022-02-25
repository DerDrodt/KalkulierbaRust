use std::{collections::HashMap, fmt};

use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{
    clause::{Atom, Clause, ClauseSet},
    parse::{parse_flexible, CNFStrategy, ParseErr},
    tamper_protect::ProtectedState,
    Calculus, Symbol,
};

#[derive(Debug)]
pub enum DPLLErr {
    ParseErr(ParseErr),
    InvalidBranchId(usize),
    AtomsNotCompatible(Atom<Symbol>, Atom<Symbol>),
    ExpectedLeaf(usize),
    PropAnnotation(DPLLNode),
    InvalidClauseId(usize),
    NoSuchAtom(Clause<Symbol>, usize),
    SameClauseIds,
    MayOnlyHaveOneAtom(Clause<Symbol>),
    SplitAnnotation(DPLLNode),
    InvalidVarName(String),
    CannotPruneAnnotation(usize),
    ExpectedModelNode(DPLLNode),
    HasAlreadyBeenChecked,
    IDoesNotSatisfy(Clause<Symbol>),
}

impl From<ParseErr> for DPLLErr {
    fn from(e: ParseErr) -> Self {
        Self::ParseErr(e)
    }
}

impl fmt::Display for DPLLErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DPLLErr::ParseErr(e) => fmt::Display::fmt(e, f),
            DPLLErr::InvalidBranchId(b) => write!(f, "Branch with ID {b} does not exist"),
            DPLLErr::AtomsNotCompatible(a1, a2) => {
                write!(f, "Selected atom '{a1}' is not compatible with '{a2}'")
            }
            DPLLErr::ExpectedLeaf(b) => write!(f, "ID {b} does not reference a leaf"),
            DPLLErr::PropAnnotation(b) => write!(f, "Cannot propagate on annotation '{b}'"),
            DPLLErr::InvalidClauseId(c) => write!(f, "Clause set has no clause with ID {c}"),
            DPLLErr::NoSuchAtom(c, a) => write!(f, "Clause '{c}' has no atom with ID {a}"),
            DPLLErr::SameClauseIds => {
                write!(f, "Base and propagation clauses have to be different")
            }
            DPLLErr::MayOnlyHaveOneAtom(c) => {
                write!(f, "Base clause {c} may only have exactly one atom")
            }
            DPLLErr::SplitAnnotation(b) => write!(f, "Cannot split on annotation '{b}'"),
            DPLLErr::InvalidVarName(l) => write!(f, "Invalid variable name '{l}'"),
            DPLLErr::CannotPruneAnnotation(b) => write!(f, "Cannot prune annotation '{b}'"),
            DPLLErr::ExpectedModelNode(b) => write!(f, "Node '{b}' is not a model node"),
            DPLLErr::HasAlreadyBeenChecked => write!(f, "This node has already been checked"),
            DPLLErr::IDoesNotSatisfy(c) => write!(
                f,
                "The given interpretation does not satisfy any atom of clause {c}"
            ),
        }
    }
}

pub type DPLLResult<T> = Result<T, DPLLErr>;

#[derive(Debug, Clone)]
pub enum DPLLMove {
    Split(usize, String),
    Propagate(usize, usize, usize, usize),
    Prune(usize),
    ModelCheck(usize, HashMap<Symbol, bool>),
}

#[derive(Debug, Clone)]
pub struct DPLLState {
    clause_set: ClauseSet<Symbol>,
    nodes: Vec<DPLLNode>,
}

impl DPLLState {
    pub fn new(clause_set: ClauseSet<Symbol>) -> Self {
        Self {
            clause_set,
            nodes: Vec::new(),
        }
    }

    pub fn get_cs(&self, branch: usize) -> ClauseSet<Symbol> {
        let mut n = &self.nodes[branch];
        let mut diffs = vec![];

        while let Some(p) = n.parent {
            diffs.push(&n.diff);
            n = &self.nodes[p];
        }

        let mut cs = self.clause_set.clone();

        for d in diffs.iter().rev() {
            cs = d.apply(cs);
        }

        todo!()
    }

    pub fn add_child(&mut self, p: usize, n: DPLLNode) {
        let idx = self.nodes.len();
        self.nodes[p].children.push(idx);
        self.nodes.push(n);
    }
}

impl ProtectedState for DPLLState {
    fn compute_seal_info(&self) -> String {
        let nis: Vec<String> = self.nodes.iter().map(|n| n.info()).collect();
        format!("pdpll|{}|{}", self.clause_set, nis.join(","))
    }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum NodeType {
    #[serde(rename = "ROOT")]
    Root,
    #[serde(rename = "PROP")]
    Prop,
    #[serde(rename = "SPLIT")]
    Split,
    #[serde(rename = "MODEL")]
    Model,
    #[serde(rename = "CLOSED")]
    Closed,
}

impl NodeType {
    pub fn is_annotation(&self) -> bool {
        match self {
            NodeType::Model | NodeType::Closed => true,
            _ => false,
        }
    }

    pub fn is_closed(&self) -> bool {
        match self {
            Self::Closed => true,
            _ => false,
        }
    }

    pub fn is_model(&self) -> bool {
        match self {
            Self::Model => true,
            _ => false,
        }
    }
}

impl fmt::Display for NodeType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NodeType::Root => write!(f, "ROOT"),
            NodeType::Prop => write!(f, "PROP"),
            NodeType::Split => write!(f, "SPLIT"),
            NodeType::Model => write!(f, "MODEL"),
            NodeType::Closed => write!(f, "CLOSED"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum CsDiff {
    Id,
    RemoveClause(usize),
    AddClause(Clause<Symbol>),
    RemoveAtom(usize, usize),
}

impl CsDiff {
    pub fn apply(&self, mut cs: ClauseSet<Symbol>) -> ClauseSet<Symbol> {
        match self {
            CsDiff::Id => cs.clone(),
            CsDiff::RemoveClause(c) => {
                cs.remove(*c);
                cs
            }
            CsDiff::AddClause(c) => {
                cs.add(c.clone());
                cs
            }
            CsDiff::RemoveAtom(c, a) => {
                cs.remove_atom(*c, *a);
                cs
            }
        }
    }
}

impl fmt::Display for CsDiff {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CsDiff::Id => write!(f, ""),
            CsDiff::RemoveClause(c) => write!(f, "remove-{c}"),
            CsDiff::AddClause(c) => write!(f, "add-{c}"),
            CsDiff::RemoveAtom(c, a) => write!(f, "remove-{c}-{a}"),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DPLLNode {
    parent: Option<usize>,
    #[serde(rename = "type")]
    ty: NodeType,
    label: Symbol,
    diff: CsDiff,
    children: Vec<usize>,
    #[serde(rename = "modelVerified")]
    verified: Option<bool>,
}

impl DPLLNode {
    pub fn new(parent: Option<usize>, ty: NodeType, label: Symbol, diff: CsDiff) -> Self {
        Self {
            parent,
            ty,
            label,
            diff,
            children: vec![],
            verified: None,
        }
    }

    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }

    pub fn is_annotation(&self) -> bool {
        self.ty.is_annotation()
    }

    pub fn info(&self) -> String {
        let parent = match self.parent {
            Some(p) => p.to_string(),
            _ => "null".to_string(),
        };
        let children = self
            .children
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<String>>()
            .join(",");
        let ty = &self.ty;
        let label = self.label;
        let diff = &self.diff;
        let veri = match self.verified {
            Some(true) => "true",
            Some(false) => "false",
            _ => "null",
        };
        format!("({parent}|{children}|{ty}|{label}|{diff}|{veri})")
    }

    pub fn is_closed(&self) -> bool {
        !self.is_leaf() || self.ty.is_closed()
    }
}

impl fmt::Display for DPLLNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.label, f)
    }
}

pub struct DPLL;

impl<'f> Calculus<'f> for DPLL {
    type Params = ();

    type State = DPLLState;

    type Move = DPLLMove;

    type Error = DPLLErr;

    fn parse_formula(
        formula: &'f str,
        _: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        let cs = parse_flexible(formula, CNFStrategy::Optimal)?;
        let mut s = DPLLState::new(cs);
        s.nodes.push(DPLLNode::new(
            None,
            NodeType::Root,
            "true".into(),
            CsDiff::Id,
        ));

        Ok(s)
    }

    fn apply_move(state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        match k_move {
            DPLLMove::Split(branch, lit) => split(state, branch, lit),
            DPLLMove::Propagate(branch, base_clause, prop_clause, prop_atom) => {
                propagate(state, branch, base_clause, prop_clause, prop_atom)
            }
            DPLLMove::Prune(branch) => prune(state, branch),
            DPLLMove::ModelCheck(branch, interpretation) => {
                model_check(state, branch, interpretation)
            }
        }
    }

    fn check_close(state: Self::State) -> crate::calculus::CloseMsg {
        let closed = state.nodes.iter().all(DPLLNode::is_closed);
        let done = state
            .nodes
            .iter()
            .all(|n| !n.is_leaf() || n.is_annotation());

        let msg = match (closed, done) {
          (true, _) => "The proof is closed and proves the unsatisfiability of the clause set",
          (_, true) => "The proof is not closed - however, all branches are completed. The clause set is satisfiable.",
          _ => "The proof is not closed yet."
        };

        crate::calculus::CloseMsg {
            closed,
            msg: msg.to_string(),
        }
    }
}

fn propagate(
    mut state: DPLLState,
    branch: usize,
    base_c: usize,
    prop_c: usize,
    prop_a: usize,
) -> DPLLResult<DPLLState> {
    let cs = check_propagate_restrictions(&state, branch, base_c, prop_c, prop_a)?;
    let base_a = &cs.clauses()[base_c].atoms()[0];
    let prop_atom = &cs.clauses()[prop_c].atoms()[prop_a];

    // If the selected clause contains the atom which we know must be true,
    // the whole clause is trivially true and we can remove it from the set

    let diff = if base_a == prop_atom {
        CsDiff::RemoveClause(prop_c)
    } else if base_a.lit() == prop_atom.lit() && base_a.negated() != prop_atom.negated() {
        CsDiff::RemoveAtom(prop_c, prop_a)
    } else {
        return Err(DPLLErr::AtomsNotCompatible(
            base_a.clone(),
            prop_atom.clone(),
        ));
    };

    let ncs = diff.apply(cs);
    let prop_node = DPLLNode::new(Some(branch), NodeType::Prop, "prop".into(), diff);
    state.add_child(branch, prop_node);
    let pn_id = state.nodes.len() - 1;

    // Add proper annotations if the node created by propagation is closed or represents a model

    // A node is considered closed if the clause set associated with it contains an empty clause
    if ncs.clauses().iter().any(|c| c.is_empty()) {
        state.add_child(
            pn_id,
            DPLLNode::new(Some(pn_id), NodeType::Closed, "closed".into(), CsDiff::Id),
        );
    }
    // A node is considered a model if it contains only single-atom clauses
    // that do not contradict each other and contain no duplicates
    else if ncs.clauses().iter().all(|c| c.size() == 1) && check_no_dups(&ncs) {
        state.add_child(
            pn_id,
            DPLLNode::new(Some(pn_id), NodeType::Model, "model".into(), CsDiff::Id),
        );
    }

    Ok(state)
}

fn split(mut state: DPLLState, branch: usize, l: String) -> DPLLResult<DPLLState> {
    let lit = check_split_restrictions(&state, branch, l)?;

    // Add a case distinction for $literal
    let true_c = Clause::new(vec![Atom::new(lit, false)]);
    let false_c = Clause::new(vec![Atom::new(lit, true)]);
    let true_n = DPLLNode::new(
        Some(branch),
        NodeType::Split,
        lit,
        CsDiff::AddClause(true_c),
    );
    let false_n = DPLLNode::new(
        Some(branch),
        NodeType::Split,
        Symbol::intern(&format!("¬{lit}")),
        CsDiff::AddClause(false_c),
    );
    state.add_child(branch, true_n);
    state.add_child(branch, false_n);

    Ok(state)
}

fn prune(mut state: DPLLState, branch: usize) -> DPLLResult<DPLLState> {
    if branch >= state.nodes.len() {
        return Err(DPLLErr::InvalidBranchId(branch));
    }

    let n = &state.nodes[branch];

    // Weird things would happen if we would allow removing annotations
    if n.children.len() == 1 {
        let c = n.children[0];
        if state.nodes[c].is_annotation() {
            return Err(DPLLErr::CannotPruneAnnotation(c));
        }
    }

    // Collect all transitive children of the node
    // (not deleting anything yet to keep index structures intact)
    let mut q = vec![];
    let mut to_del = vec![];
    for c in &n.children {
        q.push(*c);
    }

    while let Some(idx) = q.get(0) {
        let idx = *idx;
        let n = &state.nodes[idx];
        for c in &n.children {
            q.push(*c);
        }
        to_del.push(idx)
    }

    // Remove each identified child, keeping parent references but not children references
    // We remove items from the largest index to the smallest to keep the indices of the other
    // items in the list consistent

    to_del.sort();
    for i in to_del.iter().rev() {
        state.nodes.remove(*i);
        for n in state.nodes.iter_mut() {
            if let Some(p) = n.parent {
                if p > *i {
                    n.parent = Some(p - 1);
                }
            }
        }
    }

    // Re-compute children references
    state.nodes.iter_mut().for_each(|n| n.children.clear());

    for i in 0..state.nodes.len() {
        let n = &state.nodes[i];
        if let Some(p) = n.parent {
            state.nodes[p].children.push(i);
        }
    }

    Ok(state)
}

fn model_check(
    mut state: DPLLState,
    branch: usize,
    i: HashMap<Symbol, bool>,
) -> DPLLResult<DPLLState> {
    if branch >= state.nodes.len() {
        return Err(DPLLErr::InvalidBranchId(branch));
    }

    let b = &state.nodes[branch];

    if !b.ty.is_model() {
        return Err(DPLLErr::ExpectedModelNode(b.clone()));
    }

    if let Some(true) = b.verified {
        return Err(DPLLErr::HasAlreadyBeenChecked);
    }

    let cs = state.get_cs(branch);

    // Check that the mapping satisfies every clause
    for c in cs.clauses() {
        if !c
            .atoms()
            .iter()
            .any(|a| i.contains_key(a.lit()) && a.negated() != i[a.lit()])
        {
            return Err(DPLLErr::IDoesNotSatisfy(c.clone()));
        }
    }

    let b = &mut state.nodes[branch];
    b.verified = Some(true);
    b.label = Symbol::intern(&format!("{} ✓", b.label));

    Ok(state)
}

fn check_propagate_restrictions(
    state: &DPLLState,
    branch: usize,
    base_c: usize,
    prop_c: usize,
    prop_a: usize,
) -> DPLLResult<ClauseSet<Symbol>> {
    // Check branch validity
    if branch >= state.nodes.len() {
        return Err(DPLLErr::InvalidBranchId(branch));
    }
    let b = &state.nodes[branch];
    if !b.is_leaf() {
        return Err(DPLLErr::ExpectedLeaf(branch));
    }
    if b.is_annotation() {
        return Err(DPLLErr::PropAnnotation(b.clone()));
    }

    let cs = state.get_cs(branch);

    // Check baseID, propID, atomID validity
    if base_c >= cs.size() {
        return Err(DPLLErr::InvalidClauseId(base_c));
    }
    if prop_c >= cs.size() {
        return Err(DPLLErr::InvalidClauseId(prop_c));
    }
    if base_c == prop_c {
        return Err(DPLLErr::SameClauseIds);
    }
    let c = &cs.clauses()[prop_c];
    if prop_a >= c.size() {
        return Err(DPLLErr::NoSuchAtom(c.clone(), prop_a));
    }

    let base = &cs.clauses()[base_c];
    if base.size() != 1 {
        return Err(DPLLErr::MayOnlyHaveOneAtom(base.clone()));
    }

    Ok(cs)
}

fn check_no_dups(cs: &ClauseSet<Symbol>) -> bool {
    let mut v: Vec<Symbol> = cs.clauses().iter().map(|c| *c.atoms()[0].lit()).collect();
    v.sort();
    v.dedup();
    v.len() == cs.size()
}

fn check_split_restrictions(state: &DPLLState, branch: usize, lit: String) -> DPLLResult<Symbol> {
    use crate::parse::{Token, TokenKind, Tokenizer};
    if branch >= state.nodes.len() {
        return Err(DPLLErr::InvalidBranchId(branch));
    }
    let b = &state.nodes[branch];
    if !b.is_leaf() {
        return Err(DPLLErr::ExpectedLeaf(branch));
    }
    if b.is_annotation() {
        return Err(DPLLErr::PropAnnotation(b.clone()));
    }

    let tokenized: Result<Vec<Token>, ParseErr> = Tokenizer::new(&lit, false).collect();
    let mut tokenized = tokenized?;

    if tokenized.len() != 1 {
        return Err(DPLLErr::InvalidVarName(lit));
    }
    let v = tokenized.remove(0);

    if v.kind != TokenKind::CapIdent && v.kind != TokenKind::LowIdent {
        return Err(DPLLErr::InvalidVarName(lit));
    }

    Ok(v.spelling.into())
}

impl Serialize for CsDiff {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (ty, len) = match self {
            CsDiff::Id => ("cd-identity", 1),
            CsDiff::RemoveClause(_) => ("cd-delclause", 2),
            CsDiff::AddClause(_) => ("cd-addclause", 2),
            CsDiff::RemoveAtom(_, _) => ("cd-delatom", 3),
        };
        let mut state = serializer.serialize_struct("CsDiff", len)?;
        state.serialize_field("ty", ty)?;
        match self {
            CsDiff::Id => {}
            CsDiff::RemoveClause(c) => {
                state.serialize_field("id", c)?;
            }
            CsDiff::AddClause(c) => {
                state.serialize_field("clause", c)?;
            }
            CsDiff::RemoveAtom(c, a) => {
                state.serialize_field("cid", c)?;
                state.serialize_field("aid", a)?;
            }
        };
        state.end()
    }
}

impl<'de> Deserialize<'de> for CsDiff {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "type")]
            Ty,
            #[serde(rename = "id")]
            Id,
            #[serde(rename = "clause")]
            Clause,
            #[serde(rename = "cid")]
            CId,
            #[serde(rename = "aid")]
            AId,
        }

        struct DiffVisitor;

        impl<'de> Visitor<'de> for DiffVisitor {
            type Value = CsDiff;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct CsDiff")
            }

            fn visit_map<V>(self, mut map: V) -> Result<CsDiff, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut id: Option<usize> = None;
                let mut clause: Option<Clause<Symbol>> = None;
                let mut cid: Option<usize> = None;
                let mut aid: Option<usize> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Ty => {
                            if ty.is_some() {
                                return Err(de::Error::duplicate_field("type"));
                            }
                            ty = Some(map.next_value()?);
                        }
                        Field::Id => {
                            if id.is_some() {
                                return Err(de::Error::duplicate_field("id"));
                            }
                            id = Some(map.next_value()?);
                        }
                        Field::Clause => {
                            if clause.is_some() {
                                return Err(de::Error::duplicate_field("clause"));
                            }
                            clause = Some(map.next_value()?);
                        }
                        Field::CId => {
                            if cid.is_some() {
                                return Err(de::Error::duplicate_field("cid"));
                            }
                            cid = Some(map.next_value()?);
                        }
                        Field::AId => {
                            if aid.is_some() {
                                return Err(de::Error::duplicate_field("aid"));
                            }
                            aid = Some(map.next_value()?);
                        }
                    }
                }

                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                let ty: &str = &ty;
                Ok(match ty {
                    "cd-identity" => CsDiff::Id,
                    "cd-delclause" => {
                        CsDiff::RemoveClause(id.ok_or_else(|| de::Error::missing_field("id"))?)
                    }
                    "cd-addclause" => {
                        CsDiff::AddClause(clause.ok_or_else(|| de::Error::missing_field("clause"))?)
                    }
                    "cd-delatom" => CsDiff::RemoveAtom(
                        cid.ok_or_else(|| de::Error::missing_field("cid"))?,
                        aid.ok_or_else(|| de::Error::missing_field("aid"))?,
                    ),
                    _ => todo!(),
                })
            }
        }

        const FIELDS: &[&str] = &["type", "id", "clause", "cid", "aid"];
        deserializer.deserialize_struct("PropResMove", FIELDS, DiffVisitor)
    }
}

impl Serialize for DPLLState {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("DPLLState", 3)?;
        state.serialize_field("clauseSet", &self.clause_set)?;
        state.serialize_field("tree", &self.nodes)?;
        state.serialize_field("seal", &self.seal())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for DPLLState {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "clauseSet")]
            ClauseSet,
            #[serde(rename = "tree")]
            Nodes,
            #[serde(rename = "seal")]
            Seal,
        }

        struct StateVisitor;

        impl<'de> Visitor<'de> for StateVisitor {
            type Value = DPLLState;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct DPLLState")
            }

            fn visit_map<V>(self, mut map: V) -> Result<DPLLState, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut clause_set: Option<ClauseSet<Symbol>> = None;
                let mut nodes: Option<Vec<DPLLNode>> = None;
                let mut seal: Option<String> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::ClauseSet => {
                            if clause_set.is_some() {
                                return Err(de::Error::duplicate_field("clauseSet"));
                            }
                            clause_set = Some(map.next_value()?);
                        }
                        Field::Nodes => {
                            if nodes.is_some() {
                                return Err(de::Error::duplicate_field("tree"));
                            }
                            nodes = Some(map.next_value()?);
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
                let nodes = nodes.ok_or_else(|| de::Error::missing_field("tree"))?;
                let seal = seal.ok_or_else(|| de::Error::missing_field("seal"))?;

                let s = DPLLState { clause_set, nodes };

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

        const FIELDS: &[&str] = &["clause_set", "tree", "seal"];
        deserializer.deserialize_struct("DPLLState", FIELDS, StateVisitor)
    }
}

impl Serialize for DPLLMove {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (ty, len) = match self {
            DPLLMove::Split(_, _) => ("dpll-split", 3),
            DPLLMove::Propagate(_, _, _, _) => ("dpll-prop", 5),
            DPLLMove::Prune(_) => ("dpll-prune", 2),
            DPLLMove::ModelCheck(_, _) => ("dpll-modelcheck", 3),
        };
        let mut state = serializer.serialize_struct("DPLLMove", len)?;
        state.serialize_field("type", ty)?;
        match self {
            DPLLMove::Split(b, l) => {
                state.serialize_field("branch", b)?;
                state.serialize_field("literal", l)?;
            }
            DPLLMove::Propagate(b, base, pc, pa) => {
                state.serialize_field("branch", b)?;
                state.serialize_field("baseClause", base)?;
                state.serialize_field("propClause", pc)?;
                state.serialize_field("propAtom", pa)?;
            }
            DPLLMove::Prune(b) => {
                state.serialize_field("branch", b)?;
            }
            DPLLMove::ModelCheck(b, i) => {
                state.serialize_field("branch", b)?;
                state.serialize_field("interpretation", i)?;
            }
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for DPLLMove {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "type")]
            Ty,
            #[serde(rename = "branch")]
            Branch,
            #[serde(rename = "literal")]
            Literal,
            #[serde(rename = "baseClause")]
            BaseClause,
            #[serde(rename = "propClause")]
            PropClause,
            #[serde(rename = "propAtom")]
            PropAtom,
            #[serde(rename = "interpretation")]
            Interpretation,
        }

        struct MoveVisitor;

        impl<'de> Visitor<'de> for MoveVisitor {
            type Value = DPLLMove;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct DPLLMove")
            }

            fn visit_map<V>(self, mut map: V) -> Result<DPLLMove, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut branch: Option<usize> = None;
                let mut lit: Option<String> = None;
                let mut base_c: Option<usize> = None;
                let mut prop_c: Option<usize> = None;
                let mut prop_a: Option<usize> = None;
                let mut i: Option<HashMap<Symbol, bool>> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Ty => {
                            if ty.is_some() {
                                return Err(de::Error::duplicate_field("type"));
                            }
                            ty = Some(map.next_value()?);
                        }
                        Field::Branch => {
                            if branch.is_some() {
                                return Err(de::Error::duplicate_field("branch"));
                            }
                            branch = Some(map.next_value()?);
                        }
                        Field::Literal => {
                            if lit.is_some() {
                                return Err(de::Error::duplicate_field("literal"));
                            }
                            lit = Some(map.next_value()?);
                        }
                        Field::BaseClause => {
                            if base_c.is_some() {
                                return Err(de::Error::duplicate_field("baseClause"));
                            }
                            base_c = Some(map.next_value()?);
                        }
                        Field::PropClause => {
                            if prop_c.is_some() {
                                return Err(de::Error::duplicate_field("propClause"));
                            }
                            prop_c = Some(map.next_value()?);
                        }
                        Field::PropAtom => {
                            if prop_a.is_some() {
                                return Err(de::Error::duplicate_field("propAtom"));
                            }
                            prop_a = Some(map.next_value()?);
                        }
                        Field::Interpretation => {
                            if i.is_some() {
                                return Err(de::Error::duplicate_field("interpretation"));
                            }
                            i = Some(map.next_value()?);
                        }
                    }
                }

                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                let ty: &str = &ty;
                let branch = branch.ok_or_else(|| de::Error::missing_field("branch"))?;
                let lit = lit.ok_or_else(|| de::Error::missing_field("literal"))?;
                let base_c = base_c.ok_or_else(|| de::Error::missing_field("baseClause"))?;
                let prop_c = prop_c.ok_or_else(|| de::Error::missing_field("propClause"))?;
                let prop_a = prop_a.ok_or_else(|| de::Error::missing_field("propAtom"))?;
                let i = i.ok_or_else(|| de::Error::missing_field("interpretation"))?;
                Ok(match ty {
                    "dpll-split" => DPLLMove::Split(branch, lit),
                    "dpll-prop" => DPLLMove::Propagate(branch, base_c, prop_c, prop_a),
                    "dpll-prune" => DPLLMove::Prune(branch),
                    "dpll-modelcheck" => DPLLMove::ModelCheck(branch, i),
                    _ => todo!(),
                })
            }
        }

        const FIELDS: &[&str] = &["type", "c1", "c2", "literal", "mainID", "atomMap", "atoms"];
        deserializer.deserialize_struct("PropResMove", FIELDS, MoveVisitor)
    }
}
