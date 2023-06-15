use std::fmt;

use serde::de::{self, MapAccess, Visitor};
use serde::{ser::SerializeStruct, Deserialize, Serialize, Serializer};

use super::TableauxType;
use crate::clause::{Atom, Clause, ClauseSet};
use crate::parse::ParseErr;
use crate::parse::{parse_prop_flexible, CNFStrategy};
use crate::tamper_protect::ProtectedState;
use crate::Calculus;
use crate::{calculus::CloseMsg, symbol::Symbol};

pub type PropTabResult<T> = Result<T, Err>;

impl From<ParseErr> for Err {
    fn from(e: ParseErr) -> Self {
        Err::ParseErr(e)
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum Err {
    ParseErr(ParseErr),
    InvalidNodeId(usize),
    InvalidClauseId(usize),
    Backtracking,
    BacktrackingEmpty,
    IllegalMove,
    NotConnected,
    ExpectedLeaf(usize),
    ExpectedClosed(usize),
    AlreadyClosed(usize),
    WouldMakeIrregular(String),
    WouldMakeUnconnected,
    WouldMakeNotStronglyConnected(String),
    LemmaRoot,
    LemmaLeaf(usize),
    ExpectedSiblings(usize, usize),
    ExpectedSameSpelling(usize, usize),
    CloseBothPos(usize, usize),
    CloseBothNeg(usize, usize),
    ExpectedParent(usize, usize),
    CloseRoot,
}

impl fmt::Display for Err {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Err::ParseErr(e) => write!(f, "{}", e),
            Err::InvalidNodeId(id) => write!(f, "Node with ID {} does not exist", id),
            Err::InvalidClauseId(id) => write!(f, "Clause with ID {} does not exist", id),
            Err::Backtracking => write!(f, "Backtracking is not enabled for this proof"),
            Err::BacktrackingEmpty => write!(f, "Can't undo in initial state"),
            Err::IllegalMove => write!(f, "Illegal move"),
            Err::NotConnected => write!(f, "The proof tree is currently not sufficiently connected, please close branches first to restore connectedness before expanding more leaves"),
            Err::ExpectedLeaf(id) => write!(f, "Node {} is not a leaf", id),
            Err::ExpectedClosed(id) => write!(f, "Node '{}' is not the root of a closed subtree", id),
            Err::AlreadyClosed(id) => write!(f, "Node '{}' is already closed",id),
            Err::WouldMakeIrregular(msg) => write!(f, "Expanding this clause would introduce a duplicate node '{}' on the branch, making the tree irregular", msg),
            Err::WouldMakeUnconnected => write!(f, "No literal in this clause would be closeable, making the tree unconnected"),
            Err::WouldMakeNotStronglyConnected(msg) => write!(f, "No literal in this clause would be closeable with '{}', making the tree not strongly connected", msg),
            Err::LemmaRoot => write!(f, "Root node cannot be used for lemma creation"),
            Err::LemmaLeaf(id) => write!(f, "Cannot create lemma from a leaf: {}", id),
            Err::ExpectedSiblings(id1, id2) => write!(f, "Nodes '{}' and '{}' are not siblings", id1, id2),
            Err::ExpectedSameSpelling(id1, id2) => write!(f, "Leaf '{}' and node '{}' do not reference the same literal", id1, id2),
            Err::CloseBothPos(id1, id2) => write!(f, "Leaf '{}' and node '{}' reference the same literal, but neither of them are negated", id1, id2),
            Err::CloseBothNeg(id1, id2) => write!(f, "Leaf '{}' and node '{}' reference the same literal, but both of them are negated", id1, id2),
            Err::ExpectedParent(id1, id2) => write!(f, "Node '{}' is not an ancestor of leaf '{}'", id1, id2),
            Err::CloseRoot => write!(f, "The root node cannot be used for branch closure"),
        }
    }
}

#[derive(Deserialize, Serialize)]
pub struct Params {
    #[serde(rename = "type")]
    pub tab_type: TableauxType,
    pub regular: bool,
    pub backtracking: bool,
    #[serde(rename = "cnfStrategy")]
    pub cnf_strategy: CNFStrategy,
}

impl Default for Params {
    fn default() -> Self {
        Params {
            tab_type: TableauxType::Unconnected,
            regular: false,
            backtracking: false,
            cnf_strategy: CNFStrategy::Optimal,
        }
    }
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct State {
    #[serde(rename = "clauseSet")]
    clause_set: ClauseSet<Symbol>,
    #[serde(rename = "type")]
    ty: TableauxType,
    regular: bool,
    backtracking: bool,
    #[serde(rename = "tree")]
    nodes: Vec<Node>,
    #[serde(rename = "moveHistory")]
    moves: Vec<Move>,
    #[serde(rename = "usedBacktracking")]
    used_backtracking: bool,
    seal: String,
}

impl ProtectedState for State {
    fn compute_seal_info(&self) -> String {
        let opts = format!(
            "{}|{}|{}|{}",
            self.ty.to_string().to_uppercase(),
            self.regular,
            self.backtracking,
            self.used_backtracking
        );
        let clause_set = self.clause_set.to_string();
        let nodes = {
            let mut ns = String::new();
            for (i, n) in self.nodes.iter().enumerate() {
                ns.push_str(&n.info());
                if i < self.nodes.len() - 1 {
                    ns.push('|');
                }
            }
            ns
        };
        let history = {
            let mut ms = String::new();
            for (i, m) in self.moves.iter().enumerate() {
                ms.push_str(&m.to_string());
                if i < self.moves.len() - 1 {
                    ms.push(',');
                }
            }
            ms
        };
        format!(
            "tableauxstate|{}|{}|[{}]|[{}]",
            opts, clause_set, nodes, history
        )
    }
}

impl State {
    pub fn new(
        clause_set: ClauseSet<Symbol>,
        ty: TableauxType,
        regular: bool,
        backtracking: bool,
    ) -> Self {
        Self {
            clause_set,
            ty,
            regular,
            backtracking,
            nodes: vec![Node::new(None, "true".into(), false, None)],
            moves: vec![],
            used_backtracking: false,
            seal: String::new(),
        }
    }

    pub fn root(&self) -> &Node {
        &self.nodes[0]
    }

    pub fn node(&self, id: usize) -> PropTabResult<&Node> {
        if let Some(node) = self.nodes.get(id) {
            Ok(node)
        } else {
            Err(Err::InvalidNodeId(id))
        }
    }

    pub fn node_mut(&mut self, id: usize) -> PropTabResult<&mut Node> {
        if let Some(node) = self.nodes.get_mut(id) {
            Ok(node)
        } else {
            Err(Err::InvalidNodeId(id))
        }
    }

    pub fn node_is_closable(&self, id: usize) -> PropTabResult<bool> {
        let node = self.nodes.get(id);
        if let Some(node) = node {
            let atom: Atom<Symbol> = node.into();
            Ok(node.is_leaf() && self.node_ancestry_contains_atom(id, atom.not())?)
        } else {
            Err(Err::InvalidNodeId(id))
        }
    }

    pub fn node_is_directly_closable(&self, id: usize) -> PropTabResult<bool> {
        let node = self.nodes.get(id);
        if let Some(node) = node {
            let atom: Atom<Symbol> = node.into();
            if let Some(parent) = node.parent {
                let parent = self.node(parent)?;
                let pa: Atom<Symbol> = parent.into();
                let pa = pa.not();
                Ok(node.is_leaf() && atom == pa)
            } else {
                Ok(false)
            }
        } else {
            Err(Err::InvalidNodeId(id))
        }
    }

    pub fn clause_expand_preprocessing<'c>(
        &self,
        clause: &'c Clause<Symbol>,
    ) -> &'c Vec<Atom<Symbol>> {
        clause.atoms()
    }

    pub fn node_ancestry_contains_atom(
        &self,
        node_id: usize,
        atom: Atom<Symbol>,
    ) -> PropTabResult<bool> {
        let mut node = self.node(node_id)?;

        while let Some(parent) = node.parent {
            node = self.node(parent)?;
            if atom == node.into() {
                return Ok(true);
            }
        }

        Ok(false)
    }

    pub fn mark_node_closed(&mut self, leaf: usize) {
        let mut id = leaf;
        while self.is_leaf(id) || self.all_children_closed(id) {
            let node = &mut self.nodes[id];
            node.mark_closed();
            if node.parent().is_none() {
                break;
            }
            id = node.parent.unwrap();
        }
    }

    pub fn is_leaf(&self, leaf: usize) -> bool {
        self.nodes[leaf].children.is_empty()
    }

    pub fn all_children_closed(&self, node_id: usize) -> bool {
        let node = &self.nodes[node_id];
        node.children.iter().all(|e| self.nodes[*e].is_closed())
    }

    pub fn get_close_msg(&self) -> CloseMsg {
        let msg = if !self.root().is_closed() {
            "The proof tree is not closed".to_string()
        } else {
            let connectedness = match self.ty {
                TableauxType::Unconnected => "unconnected",
                TableauxType::WeaklyConnected => "weakly connected",
                TableauxType::StronglyConnected => "strongly connected",
            };
            let regularity = if check_regularity(self) {
                "regular "
            } else {
                ""
            };
            let backtracking = if self.used_backtracking {
                "with"
            } else {
                "without"
            };

            format!(
                "The proof is closed and valid in a {} {}tableaux {} backtracking",
                connectedness, regularity, backtracking
            )
        };

        CloseMsg {
            closed: self.root().is_closed(),
            msg,
        }
    }

    pub fn node_is_parent_of(&self, parent_id: usize, child: usize) -> PropTabResult<bool> {
        let child = self.node(child)?;
        if let Some(parent) = child.parent() {
            if parent == parent_id {
                Ok(true)
            } else {
                self.node_is_parent_of(parent_id, parent)
            }
        } else {
            Ok(false)
        }
    }

    pub fn get_lemma(&self, leaf_id: usize, lemma_id: usize) -> PropTabResult<Atom<Symbol>> {
        let leaf = self.node(leaf_id)?;
        let lemma = self.node(lemma_id)?;

        if !leaf.is_leaf() {
            return Err(Err::ExpectedLeaf(leaf_id));
        }

        if leaf.is_closed() {
            return Err(Err::AlreadyClosed(leaf_id));
        }

        if !lemma.is_closed() {
            return Err(Err::ExpectedClosed(lemma_id));
        }

        if lemma.parent().is_none() {
            return Err(Err::LemmaRoot);
        }

        if lemma.is_leaf() {
            return Err(Err::LemmaLeaf(lemma_id));
        }

        let common_parent = lemma.parent().unwrap();

        if !self.node_is_parent_of(common_parent, leaf_id)? {
            return Err(Err::ExpectedSiblings(leaf_id, lemma_id));
        }

        let atom: Atom<Symbol> = lemma.into();
        let atom = atom.not();

        if self.regular {
            verify_expand_regularity(self, leaf_id, &Clause::new(vec![atom.clone()]))?;
        }

        Ok(atom)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Node {
    parent: Option<usize>,
    spelling: Symbol,
    negated: bool,
    lemma_source: Option<usize>,
    is_closed: bool,
    close_ref: Option<usize>,
    children: Vec<usize>,
}

impl Node {
    pub fn new(
        parent: Option<usize>,
        spelling: Symbol,
        negated: bool,
        lemma_source: Option<usize>,
    ) -> Self {
        Self {
            parent,
            spelling,
            negated,
            lemma_source,
            is_closed: false,
            close_ref: None,
            children: vec![],
        }
    }

    pub fn parent(&self) -> Option<usize> {
        self.parent
    }

    pub fn spelling(&self) -> Symbol {
        self.spelling
    }

    pub fn negated(&self) -> bool {
        self.negated
    }

    pub fn lemma_source(&self) -> Option<usize> {
        self.lemma_source
    }

    pub fn is_closed(&self) -> bool {
        self.is_closed
    }

    pub fn close_ref(&self) -> Option<usize> {
        self.close_ref
    }

    pub fn children(&self) -> &Vec<usize> {
        &self.children
    }

    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }

    pub fn mark_closed(&mut self) {
        self.is_closed = true;
    }

    pub fn info(&self) -> String {
        let neg = if self.negated { "n" } else { "p" };
        let parent = match self.parent {
            Some(p) => p.to_string(),
            None => "null".to_string(),
        };
        let leaf = if self.is_leaf() { "l" } else { "i" };
        let closed = if self.is_closed { "c" } else { "o" };
        let r#ref = match self.close_ref {
            Some(r) => r.to_string(),
            None => "-".to_string(),
        };
        let child_list = {
            let mut cs = String::new();
            for (i, c) in self.children.iter().enumerate() {
                cs.push_str(&c.to_string());
                if i < self.children.len() - 1 {
                    cs.push(',');
                }
            }
            cs
        };

        format!(
            "{};{};{};{};{};{};({})",
            self.spelling, neg, parent, r#ref, leaf, closed, child_list
        )
    }
}

impl From<&Node> for Atom<Symbol> {
    fn from(node: &Node) -> Self {
        Atom::new(node.spelling, node.negated)
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            if self.negated { "!" } else { "" },
            self.spelling
        )
    }
}

#[derive(Debug, Clone)]
pub enum Move {
    Expand(usize, usize),
    AutoClose(usize, usize),
    Lemma(usize, usize),
    Undo,
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Move::Expand(l, r) => write!(f, "Expand({},{})", l, r),
            Move::AutoClose(l, r) => write!(f, "AutoClose({},{})", l, r),
            Move::Lemma(l, r) => write!(f, "Lemma({},{})", l, r),
            Move::Undo => write!(f, "Undo"),
        }
    }
}

pub struct PropTableaux<'l> {
    _f: &'l str,
}

impl<'l> Calculus<'l> for PropTableaux<'l> {
    type Params = Params;
    type State = State;
    type Move = Move;
    type Error = Err;

    fn parse_formula(formula: &'l str, params: Option<Self::Params>) -> PropTabResult<Self::State> {
        let Self::Params {
            tab_type,
            backtracking,
            regular,
            cnf_strategy,
        } = params.unwrap_or_default();

        let clauses = parse_prop_flexible(formula, cnf_strategy)?;
        let state = State::new(clauses, tab_type, regular, backtracking);
        state.compute_seal_info();
        Ok(state)
    }

    fn apply_move(state: Self::State, k_move: Self::Move) -> PropTabResult<Self::State> {
        use Move::*;
        let r = match k_move {
            Expand(leaf, clause) => apply_expand(state, leaf, clause),
            AutoClose(leaf, node) => apply_close(state, leaf, node),
            Lemma(leaf, lemma) => apply_lemma(state, leaf, lemma),
            Undo => apply_undo(state),
        };
        let state = r?;
        state.compute_seal_info();
        Ok(state)
    }

    fn check_close(state: Self::State) -> CloseMsg {
        state.get_close_msg()
    }

    fn validate(_state: Self::State) -> bool {
        true
    }
}

pub fn apply_expand(mut state: State, leaf_id: usize, clause_id: usize) -> PropTabResult<State> {
    ensure_expandable(&state, leaf_id, clause_id)?;

    let clause = &state.clause_set.clauses()[clause_id];
    let len = state.nodes.len();

    for (i, atom) in clause.atoms().iter().enumerate() {
        let new_leaf = Node::new(Some(leaf_id), *atom.lit(), atom.negated(), None);
        state.nodes.push(new_leaf);
        let leaf = &mut state.nodes[leaf_id];
        leaf.children.push(len + i);
    }

    verify_expand_connectedness(&state, leaf_id)?;

    if state.backtracking {
        state.moves.push(Move::Expand(leaf_id, clause_id));
    }

    Ok(state)
}

pub fn apply_close(mut state: State, leaf_id: usize, node_id: usize) -> PropTabResult<State> {
    ensure_basic_closeability(&state, leaf_id, node_id)?;

    let leaf = state.node_mut(leaf_id)?;
    leaf.close_ref = Some(node_id);
    state.mark_node_closed(leaf_id);

    if state.backtracking {
        state.moves.push(Move::AutoClose(leaf_id, node_id));
    }

    Ok(state)
}

pub fn apply_lemma(mut state: State, leaf_id: usize, lemma_id: usize) -> PropTabResult<State> {
    let atom = state.get_lemma(leaf_id, lemma_id)?;

    let new_leaf = Node::new(Some(leaf_id), *atom.lit(), atom.negated(), Some(lemma_id));
    let size = state.nodes.len();
    state.nodes.push(new_leaf);
    state.nodes.get_mut(leaf_id).unwrap().children.push(size);

    verify_expand_connectedness(&state, leaf_id)?;

    if state.backtracking {
        state.moves.push(Move::Lemma(leaf_id, lemma_id));
    }

    Ok(state)
}

pub fn apply_undo(mut state: State) -> PropTabResult<State> {
    if !state.backtracking {
        return Err(Err::Backtracking);
    }

    let mut history = state.moves;

    if history.is_empty() {
        return Err(Err::BacktrackingEmpty);
    }

    let last = history.pop().unwrap();

    state.used_backtracking = true;
    state.moves = history;

    match last {
        Move::AutoClose(leaf, ..) => undo_close(state, leaf),
        Move::Expand(id1, _) | Move::Lemma(id1, _) => undo_expand(state, id1),
        _ => Err(Err::IllegalMove),
    }
}

fn verify_expand_regularity(
    state: &State,
    leaf_id: usize,
    clause: &Clause<Symbol>,
) -> PropTabResult<()> {
    let leaf = &state.nodes[leaf_id];
    let mut lst: Vec<Atom<Symbol>> = vec![leaf.into()];

    let mut pred = None;

    if let Some(p) = leaf.parent {
        pred = Some(&state.nodes[p]);
    }

    while let Some(predecessor) = pred {
        if let Some(p) = predecessor.parent {
            lst.push(predecessor.into());
            pred = Some(&state.nodes[p]);
        } else {
            break;
        }
    }

    let clause = clause.atoms();

    for atom in clause {
        if lst.contains(atom) {
            return Err(Err::WouldMakeIrregular(atom.to_string()));
        }
    }

    Ok(())
}

fn verify_expand_connectedness(state: &State, leaf_id: usize) -> PropTabResult<()> {
    let leaf = &state.nodes[leaf_id];
    let children = &leaf.children;

    if leaf_id == 0 {
        return Ok(());
    }

    match state.ty {
        TableauxType::WeaklyConnected
            if !children
                .iter()
                .any(|id| state.node_is_closable(*id).unwrap()) =>
        {
            Err(Err::WouldMakeUnconnected)
        }
        TableauxType::StronglyConnected
            if !children
                .iter()
                .any(|id| state.node_is_directly_closable(*id).unwrap()) =>
        {
            Err(Err::WouldMakeNotStronglyConnected(leaf.to_string()))
        }
        _ => Ok(()),
    }
}

fn check_connectedness(state: &State, ty: TableauxType) -> bool {
    let start = &state.root().children;
    if ty == TableauxType::Unconnected {
        true
    } else {
        let strong = ty == TableauxType::StronglyConnected;
        start
            .iter()
            .all(|id| check_connectedness_subtree(state, *id, strong))
    }
}

fn check_connectedness_subtree(state: &State, root: usize, strong: bool) -> bool {
    let node = &state.nodes[root];

    // A sub-tree is weakly/strongly connected iff:
    // 1. The root is a leaf OR at least one child of the root is a closed leaf
    // 1a. For strong connection: The closed child is closed with the root
    // 2. All child-sub-trees are weakly/strongly connected themselves

    if node.is_leaf() {
        return true;
    }

    let mut has_directly_closed_child = false;
    let mut all_children_connected = true;

    for id in node.children.iter() {
        let id = *id;
        let child = &state.nodes[id];

        let closed_cond = child.is_closed() && (!strong || child.close_ref == Some(root));

        if child.is_leaf() && closed_cond {
            has_directly_closed_child = true;
        }
        // All children are connected themselves
        if !check_connectedness_subtree(state, id, strong) {
            all_children_connected = false;
            break;
        }
    }

    has_directly_closed_child && all_children_connected
}

pub(crate) fn check_regularity(state: &State) -> bool {
    let start = &state.root().children;

    start
        .iter()
        .all(|id| check_regularity_subtree(state, *id, vec![]))
}

fn check_regularity_subtree(state: &State, root: usize, mut lst: Vec<Atom<Symbol>>) -> bool {
    let node = &state.nodes[root];
    let atom = node.into();

    if lst.contains(&atom) {
        false
    } else {
        // TODO: optimize
        lst.push(atom);

        node.children
            .iter()
            .all(|id| check_regularity_subtree(state, *id, lst.clone()))
    }
}

fn ensure_expandable(state: &State, leaf_id: usize, clause_id: usize) -> PropTabResult<()> {
    if !check_connectedness(state, state.ty) {
        return Err(Err::NotConnected);
    }

    if leaf_id >= state.nodes.len() {
        return Err(Err::InvalidNodeId(leaf_id));
    }
    if clause_id >= state.clause_set.size() {
        return Err(Err::InvalidClauseId(clause_id));
    }

    let leaf = &state.nodes[leaf_id];

    if !leaf.is_leaf() {
        return Err(Err::ExpectedLeaf(leaf_id));
    }
    if leaf.is_closed() {
        return Err(Err::AlreadyClosed(leaf_id));
    }

    let clause = &state.clause_set.clauses()[clause_id];

    if state.regular {
        verify_expand_regularity(state, leaf_id, clause)
    } else {
        Ok(())
    }
}

fn ensure_basic_closeability(state: &State, leaf_id: usize, node_id: usize) -> PropTabResult<()> {
    let leaf = state.node(leaf_id)?;
    let node = state.node(node_id)?;

    if !leaf.is_leaf() {
        return Err(Err::ExpectedLeaf(leaf_id));
    }

    if leaf.is_closed {
        return Err(Err::AlreadyClosed(leaf_id));
    }

    if leaf.spelling != node.spelling {
        return Err(Err::ExpectedSameSpelling(leaf_id, node_id));
    }

    if node_id == 0 {
        return Err(Err::CloseRoot);
    }

    if !state.node_is_parent_of(node_id, leaf_id)? {
        return Err(Err::ExpectedParent(node_id, leaf_id));
    }

    match (leaf.negated, node.negated) {
        (true, true) => Err(Err::CloseBothNeg(leaf_id, node_id)),
        (false, false) => Err(Err::CloseBothPos(leaf_id, node_id)),
        _ => Ok(()),
    }
}

fn undo_close(mut state: State, leaf: usize) -> PropTabResult<State> {
    let mut nodes = state.nodes;

    let mut id = leaf;
    let node = &nodes[id];
    let mut is_closed = node.is_closed;

    while is_closed {
        let node = nodes.get_mut(id).unwrap();
        node.is_closed = false;
        if node.parent.is_none() {
            break;
        }
        id = node.parent.unwrap();
        is_closed = nodes.get(id).unwrap().is_closed;
    }

    nodes.get_mut(leaf).unwrap().close_ref = None;
    state.nodes = nodes;

    Ok(state)
}

fn undo_expand(mut state: State, leaf: usize) -> PropTabResult<State> {
    let leaf = state.node_mut(leaf)?;

    let children = leaf.children().len();
    leaf.children.clear();
    let mut nodes = state.nodes;

    for _ in 0..children {
        nodes.pop();
    }

    state.nodes = nodes;

    Ok(state)
}

impl Serialize for Move {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let is_undo = matches!(self, Move::Undo);
        let mut state = serializer.serialize_struct("PropTabMove", if is_undo { 1 } else { 3 })?;
        let ty = match self {
            Move::Undo => "tableaux-undo",
            Move::AutoClose(..) => "tableaux-close",
            Move::Expand(..) => "tableaux-expand",
            Move::Lemma(..) => "tableaux-lemma",
        };
        state.serialize_field("type", ty)?;
        if !is_undo {
            let (id1, id2) = match self {
                Move::Undo => panic!(),
                Move::AutoClose(id1, id2) => (id1, id2),
                Move::Expand(id1, id2) => (id1, id2),
                Move::Lemma(id1, id2) => (id1, id2),
            };
            state.serialize_field("id1", id1)?;
            state.serialize_field("id2", id2)?;
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
            #[serde(rename = "id1")]
            Id1,
            #[serde(rename = "id2")]
            Id2,
        }

        struct MoveVisitor;

        impl<'de> Visitor<'de> for MoveVisitor {
            type Value = Move;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct PropTableauxMove")
            }

            fn visit_map<V>(self, mut map: V) -> Result<Move, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut id1: Option<usize> = None;
                let mut id2: Option<usize> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Ty => {
                            if ty.is_some() {
                                return Err(de::Error::duplicate_field("type"));
                            }
                            ty = Some(map.next_value()?);
                        }
                        Field::Id1 => {
                            if id1.is_some() {
                                return Err(de::Error::duplicate_field("id1"));
                            }
                            id1 = Some(map.next_value()?);
                        }
                        Field::Id2 => {
                            if id2.is_some() {
                                return Err(de::Error::duplicate_field("id2"));
                            }
                            id2 = Some(map.next_value()?);
                        }
                    }
                }

                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                Ok(if ty == "tableaux-undo" {
                    Move::Undo
                } else {
                    let id1 = id1.ok_or_else(|| de::Error::missing_field("id1"))?;
                    let id2 = id2.ok_or_else(|| de::Error::missing_field("id2"))?;

                    let ty: &str = &ty;
                    match ty {
                        "tableaux-expand" => Move::Expand(id1, id2),
                        "tableaux-close" => Move::AutoClose(id1, id2),
                        "tableaux-lemma" => Move::Lemma(id1, id2),
                        _ => todo!(),
                    }
                })
            }
        }

        const FIELDS: &[&str] = &["type", "id1", "id2"];
        deserializer.deserialize_struct("PropTableauxMove", FIELDS, MoveVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session;

    fn create_artificial_expand_state(mut state: State, nodes: Vec<Node>) -> State {
        state.nodes.append(&mut nodes.clone());

        for (i, n) in nodes.iter().enumerate() {
            let pn = n.parent.unwrap();
            state.nodes.get_mut(pn).unwrap().children.push(i + 1);
        }

        state
    }

    mod undo {
        use super::*;
        use crate::{parse::clause_set::CNFStrategy, tamper_protect::ProtectedState, Calculus};

        fn opts() -> Params {
            Params {
                tab_type: TableauxType::Unconnected,
                regular: false,
                backtracking: true,
                cnf_strategy: CNFStrategy::Optimal,
            }
        }

        #[test]
        fn disabled() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;c", None).unwrap();
                let res = PropTableaux::apply_move(state, Move::Undo).unwrap_err();

                assert_eq!(res, Err::Backtracking);
            })
        }

        #[test]
        fn init() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;d", Some(opts())).unwrap();
                let res = PropTableaux::apply_move(state, Move::Undo).unwrap_err();

                assert_eq!(res, Err::BacktrackingEmpty);
            })
        }

        #[test]
        fn flag() {
            session(|| {
                let mut state = PropTableaux::parse_formula("a,b,c;d", Some(opts())).unwrap();

                state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();

                assert!(!state.used_backtracking);

                state = PropTableaux::apply_move(state, Move::Undo).unwrap();

                assert!(state.used_backtracking);

                state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();

                assert!(state.used_backtracking);
            })
        }

        #[test]
        fn expand_simple() {
            session(|| {
                let mut state = PropTableaux::parse_formula("a,b;c;!a", Some(opts())).unwrap();
                state.used_backtracking = true;

                let info = state.compute_seal_info();

                state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                state = PropTableaux::apply_move(state, Move::Undo).unwrap();

                assert_eq!(info, state.compute_seal_info());
            })
        }

        #[test]
        fn close_simple() {
            session(|| {
                let mut state = PropTableaux::parse_formula("a;!a", Some(opts())).unwrap();
                state.used_backtracking = true;

                state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();

                let info = state.compute_seal_info();

                state = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap();
                state = PropTableaux::apply_move(state, Move::Undo).unwrap();

                assert_eq!(info, state.compute_seal_info());
            })
        }

        fn move_and_info(state: State, r#move: Move) -> (State, String) {
            let msg = r#move.to_string();
            let state = PropTableaux::apply_move(state, r#move).expect(&msg);
            let info = state.compute_seal_info();
            (state, info)
        }

        #[test]
        fn complex() {
            session(|| {
                let mut state =
                    PropTableaux::parse_formula("a,b,c;!a;!b;!c", Some(opts())).unwrap();
                state.used_backtracking = true;

                let e6 = state.compute_seal_info();
                let (state, e5) = move_and_info(state, Move::Expand(0, 0));
                let (state, e4) = move_and_info(state, Move::Expand(1, 1));
                let (state, e3) = move_and_info(state, Move::AutoClose(4, 1));
                let (state, e2) = move_and_info(state, Move::Expand(3, 0));
                let (state, e1) = move_and_info(state, Move::Expand(5, 1));
                let (state, _) = move_and_info(state, Move::AutoClose(8, 5));

                let (state, s1) = move_and_info(state, Move::Undo);
                let (state, s2) = move_and_info(state, Move::Undo);
                let (state, s3) = move_and_info(state, Move::Undo);
                let (state, s4) = move_and_info(state, Move::Undo);
                let (state, s5) = move_and_info(state, Move::Undo);
                let (_, s6) = move_and_info(state, Move::Undo);

                assert_eq!(e1, s1);
                assert_eq!(e2, s2);
                assert_eq!(e3, s3);
                assert_eq!(e4, s4);
                assert_eq!(e5, s5);
                assert_eq!(e6, s6);
            })
        }
    }

    mod expand {
        use super::*;
        use crate::{parse::clause_set::CNFStrategy, tamper_protect::ProtectedState, Calculus};

        fn opts() -> Params {
            Params {
                tab_type: TableauxType::Unconnected,
                regular: false,
                backtracking: false,
                cnf_strategy: CNFStrategy::Optimal,
            }
        }

        #[test]
        fn valid_a() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;d", Some(opts())).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();

                assert_eq!(4, state.nodes.len());
                assert_eq!(3, state.nodes[0].children.len());

                assert_eq!("tableauxstate|UNCONNECTED|false|false|false|{a, b, c}, {d}|[true;p;null;-;i;o;(1,2,3)|a;p;0;-;l;o;()|b;p;0;-;l;o;()|c;p;0;-;l;o;()]|[]", state.compute_seal_info());
            })
        }

        #[test]
        fn valid_b() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;d", Some(opts())).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 1)).unwrap();

                assert_eq!(2, state.nodes.len());
                assert_eq!(1, state.nodes[0].children.len());

                assert_eq!("tableauxstate|UNCONNECTED|false|false|false|{a, b, c}, {d}|[true;p;null;-;i;o;(1)|d;p;0;-;l;o;()]|[]", state.compute_seal_info());
            })
        }

        #[test]
        fn valid_c() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;d", Some(opts())).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(3, 1)).unwrap();

                assert_eq!(5, state.nodes.len());
                assert_eq!(3, state.nodes[0].children.len());
                assert_eq!(1, state.nodes[3].children.len());

                assert_eq!("tableauxstate|UNCONNECTED|false|false|false|{a, b, c}, {d}|[true;p;null;-;i;o;(1,2,3)|a;p;0;-;l;o;()|b;p;0;-;l;o;()|c;p;0;-;i;o;(4)|d;p;3;-;l;o;()]|[]", state.compute_seal_info());
            })
        }

        #[test]
        fn leaf_index_invalid() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;c", Some(opts())).unwrap();
                let info = state.compute_seal_info();

                let res = PropTableaux::apply_move(state.clone(), Move::Expand(1, 0)).unwrap_err();
                assert_eq!(Err::InvalidNodeId(1), res);

                let res = PropTableaux::apply_move(state.clone(), Move::Expand(15, 0)).unwrap_err();
                assert_eq!(Err::InvalidNodeId(15), res);

                assert_eq!(info, state.compute_seal_info())
            })
        }

        #[test]
        fn clause_index_invalid() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;c", Some(opts())).unwrap();
                let info = state.compute_seal_info();

                let res = PropTableaux::apply_move(state.clone(), Move::Expand(0, 2)).unwrap_err();
                assert_eq!(Err::InvalidClauseId(2), res);

                let res = PropTableaux::apply_move(state.clone(), Move::Expand(0, 15)).unwrap_err();
                assert_eq!(Err::InvalidClauseId(15), res);

                assert_eq!(info, state.compute_seal_info())
            })
        }

        #[test]
        fn non_leaf() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;c", Some(opts())).unwrap();

                let state = PropTableaux::apply_move(state, Move::Expand(0, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();

                let info = state.compute_seal_info();

                let res = PropTableaux::apply_move(state.clone(), Move::Expand(0, 0)).unwrap_err();
                assert_eq!(Err::ExpectedLeaf(0), res);

                let res = PropTableaux::apply_move(state.clone(), Move::Expand(1, 0)).unwrap_err();
                assert_eq!(Err::ExpectedLeaf(1), res);

                assert_eq!(info, state.compute_seal_info())
            })
        }

        #[test]
        fn closed_leaf() {
            session(|| {
                let state = PropTableaux::parse_formula("a;!a", Some(opts())).unwrap();

                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap();

                let info = state.compute_seal_info();

                let res = PropTableaux::apply_move(state.clone(), Move::Expand(2, 0)).unwrap_err();
                assert_eq!(Err::AlreadyClosed(2), res);

                assert_eq!(info, state.compute_seal_info())
            })
        }
    }

    mod lemma {
        use super::*;
        use crate::{parse::clause_set::CNFStrategy, Calculus};

        fn opts() -> Params {
            Params {
                tab_type: TableauxType::Unconnected,
                regular: false,
                backtracking: false,
                cnf_strategy: CNFStrategy::Optimal,
            }
        }

        fn state(i: u8) -> State {
            let formulas = vec!["a,a;!a,b;!b", "a;b,b;!a,!b", "!a,b;!b;a,b", "a,b;!b;!a,b"];

            let formula = formulas[i as usize];

            PropTableaux::parse_formula(formula, Some(opts())).unwrap()
        }

        #[test]
        fn valid1() {
            session(|| {
                let state = state(0);

                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(4, 2)).unwrap();

                let state = PropTableaux::apply_move(state, Move::AutoClose(3, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(5, 4)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Lemma(2, 1)).unwrap();

                assert_eq!(1, state.nodes[6].lemma_source.unwrap());
                assert!(state.nodes[6].negated);
                PropTableaux::apply_move(state, Move::AutoClose(6, 2)).unwrap();
            })
        }

        #[test]
        fn valid2() {
            session(|| {
                let state = state(1);

                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(2, 2)).unwrap();

                let state = PropTableaux::apply_move(state, Move::AutoClose(4, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(5, 2)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Lemma(3, 2)).unwrap();

                assert_eq!(2, state.nodes[6].lemma_source.unwrap());
                assert!(state.nodes[6].negated);
                PropTableaux::apply_move(state, Move::AutoClose(6, 3)).unwrap();
            })
        }

        #[test]
        fn valid3() {
            session(|| {
                let state = state(2);

                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(3, 2)).unwrap();

                let state = PropTableaux::apply_move(state, Move::AutoClose(4, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(5, 3)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Lemma(2, 1)).unwrap();

                assert_eq!(1, state.nodes[6].lemma_source.unwrap());
                assert!(!state.nodes[6].negated);
            })
        }

        #[test]
        fn invalid() {
            session(|| {
                let state = state(2);

                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(3, 2)).unwrap();

                let state = PropTableaux::apply_move(state, Move::AutoClose(4, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(5, 3)).unwrap();

                let res = PropTableaux::apply_move(state.clone(), Move::Lemma(2, 3)).unwrap_err();
                assert_eq!(Err::ExpectedSiblings(2, 3), res);

                let res = PropTableaux::apply_move(state.clone(), Move::Lemma(2, 4)).unwrap_err();
                assert_eq!(Err::LemmaLeaf(4), res);

                let res = PropTableaux::apply_move(state, Move::Lemma(5, 3)).unwrap_err();
                assert_eq!(Err::AlreadyClosed(5), res);
            })
        }

        #[test]
        fn special_case() {
            session(|| {
                let state = state(0);

                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();

                let res = PropTableaux::apply_move(state.clone(), Move::Lemma(0, 0)).unwrap_err();
                assert_eq!(Err::ExpectedLeaf(0), res);

                let res = PropTableaux::apply_move(state, Move::Lemma(usize::MAX, 0)).unwrap_err();
                assert_eq!(Err::InvalidNodeId(usize::MAX), res);
            })
        }
    }

    mod close {
        use super::*;
        use crate::{parse::clause_set::CNFStrategy, tamper_protect::ProtectedState, Calculus};

        fn opts() -> Option<Params> {
            Some(Params {
                tab_type: TableauxType::Unconnected,
                regular: false,
                backtracking: false,
                cnf_strategy: CNFStrategy::Optimal,
            })
        }

        #[test]
        fn valid_a() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;!b", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(0), "b".into(), false, None),
                    Node::new(Some(2), "b".into(), true, None),
                ];

                let state = super::create_artificial_expand_state(state, nodes);
                let state = PropTableaux::apply_move(state, Move::AutoClose(3, 2)).unwrap();

                assert!(state.nodes[3].is_closed);
                assert_eq!(2, state.nodes[3].close_ref.unwrap());
                assert_eq!("tableauxstate|UNCONNECTED|false|false|false|{a, b}, {!b}|[true;p;null;-;i;o;(1,2)|a;p;0;-;l;o;()|b;p;0;-;i;c;(3)|b;n;2;2;l;c;()]|[]", state.compute_seal_info());
            })
        }

        #[test]
        fn valid_b() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;!a;!b;!c", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "b".into(), true, None),
                    Node::new(Some(1), "a".into(), false, None),
                    Node::new(Some(1), "b".into(), false, None),
                    Node::new(Some(1), "c".into(), false, None),
                ];

                let state = super::create_artificial_expand_state(state, nodes);
                let state = PropTableaux::apply_move(state, Move::AutoClose(3, 1)).unwrap();

                assert!(state.nodes[3].is_closed);
                assert!(!state.nodes[2].is_closed);
                assert!(!state.nodes[4].is_closed);

                assert_eq!(1, state.nodes[3].close_ref.unwrap());
                assert_eq!(
                "tableauxstate|UNCONNECTED|false|false|false|{a, b, c}, {!a}, {!b}, {!c}|[true;p;null;-;i;o;(1)|b;n;0;-;i;o;(2,3,4)|a;p;1;-;l;o;()|b;p;1;1;l;c;()|c;p;1;-;l;o;()]|[]",
                state.compute_seal_info()
            );
            })
        }

        #[test]
        fn valid_c() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;!a;!b;!c", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(0), "b".into(), false, None),
                    Node::new(Some(0), "c".into(), false, None),
                    Node::new(Some(1), "a".into(), true, None),
                    Node::new(Some(2), "b".into(), true, None),
                ];

                let state = super::create_artificial_expand_state(state, nodes);
                let state = PropTableaux::apply_move(state, Move::AutoClose(4, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(5, 2)).unwrap();

                assert!(!state.nodes[3].is_closed);
                assert!(state.nodes[4].is_closed);
                assert!(state.nodes[5].is_closed);

                assert_eq!(1, state.nodes[4].close_ref.unwrap());
                assert_eq!(2, state.nodes[5].close_ref.unwrap());
                assert_eq!(
                "tableauxstate|UNCONNECTED|false|false|false|{a, b, c}, {!a}, {!b}, {!c}|[true;p;null;-;i;o;(1,2,3)|a;p;0;-;i;c;(4)|b;p;0;-;i;c;(5)|c;p;0;-;l;o;()|a;n;1;1;l;c;()|b;n;2;2;l;c;()]|[]",
                state.compute_seal_info()
            );
            })
        }

        #[test]
        fn invalid_leaf_idx() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;c", opts()).unwrap();

                let res = PropTableaux::apply_move(state, Move::AutoClose(42, 1)).unwrap_err();

                assert_eq!(Err::InvalidNodeId(42), res);
            })
        }

        #[test]
        fn invalid_idx() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;c", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(0), "b".into(), false, None),
                    Node::new(Some(1), "a".into(), false, None),
                    Node::new(Some(1), "b".into(), true, None),
                ];

                let state = super::create_artificial_expand_state(state, nodes);
                let res = PropTableaux::apply_move(state, Move::AutoClose(3, 403)).unwrap_err();

                assert_eq!(Err::InvalidNodeId(403), res);
            })
        }

        #[test]
        fn non_leaf() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;c", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "c".into(), false, None),
                    Node::new(Some(1), "c".into(), false, None),
                ];

                let state = super::create_artificial_expand_state(state, nodes);
                let res =
                    PropTableaux::apply_move(state.clone(), Move::AutoClose(1, 2)).unwrap_err();

                assert_eq!(Err::ExpectedLeaf(1), res);

                let res = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap_err();
                assert_eq!(Err::CloseBothPos(2, 1), res);
            })
        }

        #[test]
        fn non_path() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;!b", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(0), "b".into(), false, None),
                    Node::new(Some(1), "a".into(), false, None),
                    Node::new(Some(1), "b".into(), false, None),
                    Node::new(Some(2), "b".into(), true, None),
                    Node::new(Some(5), "a".into(), false, None),
                    Node::new(Some(5), "b".into(), false, None),
                ];

                let state = super::create_artificial_expand_state(state, nodes);

                let res =
                    PropTableaux::apply_move(state.clone(), Move::AutoClose(4, 5)).unwrap_err();

                assert_eq!(Err::ExpectedParent(5, 4), res);

                let res = PropTableaux::apply_move(state, Move::AutoClose(5, 4)).unwrap_err();
                assert_eq!(Err::ExpectedLeaf(5), res);
            })
        }

        #[test]
        fn closed_leaf() {
            session(|| {
                let state = PropTableaux::parse_formula("c;!c", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "c".into(), false, None),
                    Node::new(Some(1), "c".into(), true, None),
                ];

                let state = super::create_artificial_expand_state(state, nodes);
                let state = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap();

                let res = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap_err();

                assert_eq!(Err::AlreadyClosed(2), res);
            })
        }

        #[test]
        fn wrong_var() {
            session(|| {
                let state = PropTableaux::parse_formula("a;!c", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(1), "c".into(), true, None),
                ];

                let state = super::create_artificial_expand_state(state, nodes);

                let res = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap_err();

                assert_eq!(Err::ExpectedSameSpelling(2, 1), res);
            })
        }

        #[test]
        fn root() {
            session(|| {
                let state = PropTableaux::parse_formula("!true", opts()).unwrap();

                let nodes = vec![Node::new(Some(0), "true".into(), true, None)];

                let state = super::create_artificial_expand_state(state, nodes);

                let res = PropTableaux::apply_move(state, Move::AutoClose(1, 0)).unwrap_err();

                assert_eq!(Err::CloseRoot, res);
            })
        }

        #[test]
        fn close_marking() {
            session(|| {
                let state = PropTableaux::parse_formula("b,a;!b;!a,b", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "b".into(), false, None),
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(1), "b".into(), false, None),
                    Node::new(Some(1), "a".into(), false, None),
                    Node::new(Some(2), "b".into(), true, None),
                    Node::new(Some(5), "a".into(), true, None),
                    Node::new(Some(5), "b".into(), false, None),
                ];

                let state = super::create_artificial_expand_state(state, nodes);
                let state = PropTableaux::apply_move(state, Move::AutoClose(7, 5)).unwrap();

                assert!(state.nodes[7].is_closed);
                assert!(!state.nodes[5].is_closed);

                let state = PropTableaux::apply_move(state, Move::AutoClose(6, 2)).unwrap();

                assert!(state.nodes[7].is_closed);
                assert!(state.nodes[6].is_closed);
                assert!(state.nodes[5].is_closed);
                assert!(state.nodes[2].is_closed);
                assert!(!state.nodes[0].is_closed);
                assert!(state.nodes[5].close_ref.is_none());
                assert!(state.nodes[2].close_ref.is_none());
            })
        }
    }

    mod check_close {
        use super::*;
        use crate::{parse::clause_set::CNFStrategy, Calculus};

        fn opts() -> Params {
            Params {
                tab_type: TableauxType::Unconnected,
                regular: false,
                backtracking: false,
                cnf_strategy: CNFStrategy::Optimal,
            }
        }

        #[test]
        fn simple() {
            session(|| {
                let mut state = PropTableaux::parse_formula("a,!a", Some(opts())).unwrap();
                assert!(!PropTableaux::check_close(state.clone()).closed);

                let mut nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(1), "a".into(), true, None),
                ];

                state.nodes.append(&mut nodes);
                state.nodes.get_mut(0).unwrap().children.push(1);
                state.nodes.get_mut(1).unwrap().children.push(2);

                assert!(!PropTableaux::check_close(state.clone()).closed);

                state = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap();
                assert!(PropTableaux::check_close(state).closed)
            })
        }

        #[test]
        fn test() {
            session(|| {
                let mut state = PropTableaux::parse_formula("a,b;!a,!b", Some(opts())).unwrap();
                assert!(!PropTableaux::check_close(state.clone()).closed);

                let mut nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(0), "b".into(), false, None),
                    Node::new(Some(1), "a".into(), true, None),
                    Node::new(Some(2), "b".into(), true, None),
                ];

                state.nodes.append(&mut nodes);
                state.nodes.get_mut(0).unwrap().children.push(1);
                state.nodes.get_mut(0).unwrap().children.push(2);
                state.nodes.get_mut(1).unwrap().children.push(3);
                state.nodes.get_mut(2).unwrap().children.push(4);

                assert!(!PropTableaux::check_close(state.clone()).closed);

                state = PropTableaux::apply_move(state, Move::AutoClose(3, 1)).unwrap();
                state = PropTableaux::apply_move(state, Move::AutoClose(4, 2)).unwrap();

                assert!(PropTableaux::check_close(state).closed)
            })
        }

        #[test]
        fn complex() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;!b;!a", Some(opts())).unwrap();

                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(2, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(4, 2)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(5, 1)).unwrap();

                assert!(!PropTableaux::check_close(state.clone()).closed);

                let state = PropTableaux::apply_move(state, Move::AutoClose(3, 2)).unwrap();

                assert!(!PropTableaux::check_close(state.clone()).closed);

                let state = PropTableaux::apply_move(state, Move::AutoClose(7, 5)).unwrap();

                assert!(!PropTableaux::check_close(state.clone()).closed);

                let state = PropTableaux::apply_move(state, Move::AutoClose(6, 4)).unwrap();

                assert!(PropTableaux::check_close(state).closed);
            })
        }

        #[test]
        fn negative() {
            session(|| {
                let mut state = PropTableaux::parse_formula("a,b;!b;!a", Some(opts())).unwrap();

                let mut nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(0), "b".into(), false, None),
                    Node::new(Some(0), "c".into(), false, None),
                    Node::new(Some(1), "a".into(), true, None),
                    Node::new(Some(2), "b".into(), true, None),
                    Node::new(Some(3), "c".into(), true, None),
                ];

                state.nodes.append(&mut nodes);
                state
                    .nodes
                    .get_mut(0)
                    .unwrap()
                    .children
                    .append(&mut vec![1, 2, 3]);
                state.nodes.get_mut(1).unwrap().children.push(4);
                state.nodes.get_mut(2).unwrap().children.push(5);
                state.nodes.get_mut(3).unwrap().children.push(6);

                state = PropTableaux::apply_move(state, Move::AutoClose(6, 3)).unwrap();
                state = PropTableaux::apply_move(state, Move::AutoClose(4, 1)).unwrap();

                assert!(!PropTableaux::check_close(state).closed)
            })
        }
    }

    mod connectedness {
        use super::*;
        use crate::{parse::clause_set::CNFStrategy, tamper_protect::ProtectedState, Calculus};

        fn opts_weak() -> Option<Params> {
            Some(Params {
                tab_type: TableauxType::WeaklyConnected,
                backtracking: false,
                regular: false,
                cnf_strategy: CNFStrategy::Optimal,
            })
        }

        fn opts_strong() -> Option<Params> {
            Some(Params {
                tab_type: TableauxType::StronglyConnected,
                backtracking: false,
                regular: false,
                cnf_strategy: CNFStrategy::Optimal,
            })
        }

        #[test]
        fn valid_a() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;!a,b", opts_weak()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(4, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(5, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(6, 1)).unwrap();

                let is_connected = check_connectedness(&state, TableauxType::WeaklyConnected);
                assert!(is_connected);

                assert_eq!("tableauxstate|WEAKLYCONNECTED|false|false|false|{a, b, c}, {!a, b}|[true;p;null;-;i;o;(1,2,3)|a;p;0;-;i;o;(4,5)|b;p;0;-;l;o;()|c;p;0;-;l;o;()|a;n;1;1;l;c;()|b;p;1;-;i;o;(6,7)|a;n;5;1;l;c;()|b;p;5;-;l;o;()]|[]", state.compute_seal_info());
            })
        }

        #[test]
        fn valid_b() {
            session(|| {
                let state = PropTableaux::parse_formula("!a,b;a", opts_weak()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(3, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(4, 1)).unwrap();

                let is_connected = check_connectedness(&state, TableauxType::WeaklyConnected);
                assert!(is_connected);

                assert_eq!("tableauxstate|WEAKLYCONNECTED|false|false|false|{!a, b}, {a}|[true;p;null;-;i;o;(1)|a;p;0;-;i;o;(2,3)|a;n;1;1;l;c;()|b;p;1;-;i;o;(4,5)|a;n;3;1;l;c;()|b;p;3;-;l;o;()]|[]", state.compute_seal_info());
            })
        }

        #[test]
        fn invalid_a() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;!a,b", opts_strong()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(4, 1)).unwrap();

                let res = PropTableaux::apply_move(state, Move::Expand(5, 1)).unwrap_err();

                assert_eq!(Err::WouldMakeNotStronglyConnected("b".to_string()), res);
            })
        }

        #[test]
        fn invalid_b() {
            session(|| {
                let state = PropTableaux::parse_formula("!a,b;a", opts_strong()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap();

                let res = PropTableaux::apply_move(state, Move::Expand(3, 0)).unwrap_err();

                assert_eq!(Err::WouldMakeNotStronglyConnected("b".to_string()), res);
            })
        }

        #[test]
        fn weak_not_closing() {
            session(|| {
                let state = PropTableaux::parse_formula("!a,b;a", opts_weak()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::AutoClose(2, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(3, 0)).unwrap();

                let res = PropTableaux::apply_move(state, Move::Expand(5, 1)).unwrap_err();

                assert_eq!(Err::NotConnected, res);
            })
        }

        #[test]
        fn strong_wrong_expand() {
            session(|| {
                let state = PropTableaux::parse_formula("!a,b;a", opts_strong()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();

                let res = PropTableaux::apply_move(state, Move::Expand(1, 0)).unwrap_err();

                assert_eq!(Err::WouldMakeNotStronglyConnected("!a".to_string()), res);
            })
        }
    }

    mod regularity {
        use super::*;
        use crate::{parse::clause_set::CNFStrategy, tamper_protect::ProtectedState, Calculus};

        fn opts() -> Option<Params> {
            Some(Params {
                tab_type: TableauxType::Unconnected,
                regular: true,
                backtracking: false,
                cnf_strategy: CNFStrategy::Optimal,
            })
        }

        #[test]
        fn valid_a() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;!a;!b", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(0), "b".into(), false, None),
                    Node::new(Some(2), "b".into(), true, None),
                    Node::new(Some(1), "a".into(), true, None),
                ];

                let state = create_artificial_expand_state(state, nodes);

                assert!(check_regularity(&state));
            })
        }

        #[test]
        fn valid_b() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;!a;!b;a", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "a".into(), false, None),
                    Node::new(Some(0), "b".into(), false, None),
                    Node::new(Some(1), "a".into(), true, None),
                    Node::new(Some(2), "b".into(), true, None),
                    Node::new(Some(4), "a".into(), false, None),
                ];

                let state = create_artificial_expand_state(state, nodes);

                assert!(check_regularity(&state));
            })
        }

        #[test]
        fn valid_c() {
            session(|| {
                let state = PropTableaux::parse_formula("true,false;!true", opts()).unwrap();

                let nodes = vec![
                    Node::new(Some(0), "true".into(), false, None),
                    Node::new(Some(0), "false".into(), false, None),
                    Node::new(Some(1), "true".into(), true, None),
                ];

                let state = create_artificial_expand_state(state, nodes);

                assert!(check_regularity(&state));
            })
        }

        #[test]
        fn valid_d() {
            session(|| {
                let state = PropTableaux::parse_formula("true,false;!true", opts()).unwrap();

                assert!(check_regularity(&state));
            })
        }

        #[test]
        fn valid_e() {
            session(|| {
                let state = PropTableaux::parse_formula("a", opts()).unwrap();
                let state = create_artificial_expand_state(
                    state,
                    vec![Node::new(Some(0), "a".into(), false, None)],
                );
                assert!(check_regularity(&state));
            })
        }

        #[test]
        fn invalid_a() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;a;b;!a;!b", opts()).unwrap();
                let state = create_artificial_expand_state(
                    state,
                    vec![
                        Node::new(Some(0), "a".into(), false, None),
                        Node::new(Some(1), "a".into(), false, None),
                    ],
                );

                assert!(!check_regularity(&state));
            })
        }

        #[test]
        fn invalid_b() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;a;b;!a;!b", opts()).unwrap();
                let state = create_artificial_expand_state(
                    state,
                    vec![
                        Node::new(Some(0), "a".into(), false, None),
                        Node::new(Some(1), "a".into(), true, None),
                        Node::new(Some(2), "b".into(), false, None),
                        Node::new(Some(3), "a".into(), false, None),
                    ],
                );

                assert!(!check_regularity(&state));
            })
        }

        #[test]
        fn invalid_c() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b;a;b;!a;!b", opts()).unwrap();
                let state = create_artificial_expand_state(
                    state,
                    vec![
                        Node::new(Some(0), "a".into(), false, None),
                        Node::new(Some(0), "b".into(), false, None),
                        Node::new(Some(1), "b".into(), false, None),
                        Node::new(Some(2), "a".into(), false, None),
                        Node::new(Some(2), "b".into(), false, None),
                    ],
                );

                assert!(!check_regularity(&state));
            })
        }

        #[test]
        fn invalid_d() {
            session(|| {
                let state = PropTableaux::parse_formula("true;!true", opts()).unwrap();
                let state = create_artificial_expand_state(
                    state,
                    vec![
                        Node::new(Some(0), "true".into(), false, None),
                        Node::new(Some(1), "true".into(), true, None),
                        Node::new(Some(2), "true".into(), false, None),
                    ],
                );

                assert!(!check_regularity(&state));
            })
        }

        #[test]
        fn expand_valid_a() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;!a;!b;!c", opts()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();

                assert_eq!(
                "tableauxstate|UNCONNECTED|true|false|false|{a, b, c}, {!a}, {!b}, {!c}|[true;p;null;-;i;o;(1,2,3)|a;p;0;-;l;o;()|b;p;0;-;l;o;()|c;p;0;-;l;o;()]|[]", 
                state.compute_seal_info()
            );
            })
        }

        #[test]
        fn expand_valid_b() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;!a;!b;!c", opts()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 0)).unwrap();

                assert_eq!(
                "tableauxstate|UNCONNECTED|true|false|false|{a, b, c}, {!a}, {!b}, {!c}|[true;p;null;-;i;o;(1)|a;n;0;-;i;o;(2,3,4)|a;p;1;-;l;o;()|b;p;1;-;l;o;()|c;p;1;-;l;o;()]|[]", 
                state.compute_seal_info()
            );
            })
        }

        #[test]
        fn expand_invalid_a() {
            session(|| {
                let state = PropTableaux::parse_formula("a,b,c;a;b;c", opts()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();

                let res = PropTableaux::apply_move(state.clone(), Move::Expand(2, 0)).unwrap_err();
                assert_eq!(Err::WouldMakeIrregular("b".to_string()), res);
                let res = PropTableaux::apply_move(state.clone(), Move::Expand(1, 1)).unwrap_err();
                assert_eq!(Err::WouldMakeIrregular("a".to_string()), res);
                let res = PropTableaux::apply_move(state.clone(), Move::Expand(2, 2)).unwrap_err();
                assert_eq!(Err::WouldMakeIrregular("b".to_string()), res);
                let res = PropTableaux::apply_move(state, Move::Expand(3, 3)).unwrap_err();
                assert_eq!(Err::WouldMakeIrregular("c".to_string()), res);
            })
        }

        #[test]
        fn expand_invalid_b() {
            session(|| {
                let state = PropTableaux::parse_formula("a;b;!a", opts()).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(0, 0)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(1, 1)).unwrap();
                let state = PropTableaux::apply_move(state, Move::Expand(2, 2)).unwrap();

                let res = PropTableaux::apply_move(state, Move::Expand(3, 0)).unwrap_err();
                assert_eq!(Err::WouldMakeIrregular("a".to_string()), res);
            })
        }
    }
}
