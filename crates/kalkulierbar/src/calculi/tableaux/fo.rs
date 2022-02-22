use std::fmt;

use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{
    calculus::CloseMsg,
    clause::Atom,
    clause::{Clause, ClauseSet},
    logic::transform::{term_manipulator::VariableSuffixAppend, visitor::FOTermVisitor},
    logic::unify::Unifier,
    logic::{
        fo::Relation,
        transform::fo_cnf::fo_cnf,
        unify::{unifier_eq::is_mgu_or_not_unifiable, unify, UnificationErr},
    },
    logic::{transform::fo_cnf::FOCNFErr, unify},
    parse::{fo::parse_fo_formula, ParseErr},
    symbol::Symbol,
    tamper_protect::ProtectedState,
    Calculus,
};

use super::{TableauxErr, TableauxNode, TableauxType};

#[derive(Debug, PartialEq, Eq)]
pub enum FOTabErr {
    Parse(ParseErr),
    CNF(FOCNFErr),
    InvalidNodeId(usize),
    InvalidClauseId(usize),
    ExpectedLeaf(FOTabNode),
    AlreadyClosed(FOTabNode),
    ExpectedClosed(FOTabNode),
    LemmaRoot,
    LemmaLeaf,
    ExpectedSiblings(FOTabNode, FOTabNode),
    AutoCloseNotEnabled,
    ExpectedSameLit(FOTabNode, FOTabNode),
    CloseRoot,
    ExpectedParent(FOTabNode, FOTabNode),
    CloseBothNeg(FOTabNode, FOTabNode),
    CloseBothPos(FOTabNode, FOTabNode),
    Unification(UnificationErr),
    UnEqAfterInst(FOTabNode, FOTabNode),
    InstWouldViolateReg,
    WouldMakeIrregular(Atom<Relation>),
    WouldMakeNotWeaklyUnconnected,
    WouldMakeNotStronglyUnconnected(FOTabNode),
    NotConnected,
    BacktrackingDisabled,
}

impl From<ParseErr> for FOTabErr {
    fn from(e: ParseErr) -> Self {
        FOTabErr::Parse(e)
    }
}

impl From<FOCNFErr> for FOTabErr {
    fn from(e: FOCNFErr) -> Self {
        FOTabErr::CNF(e)
    }
}

impl From<UnificationErr> for FOTabErr {
    fn from(e: UnificationErr) -> Self {
        FOTabErr::Unification(e)
    }
}

impl fmt::Display for FOTabErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FOTabErr::Parse(e) => fmt::Display::fmt(e, f),
            FOTabErr::CNF(e) => fmt::Display::fmt(e, f),
            FOTabErr::InvalidNodeId(id) => write!(f, "Node with ID {id} does not exist"),
            FOTabErr::InvalidClauseId(id) => write!(f, "Clause with ID {id} does not exist"),
            FOTabErr::ExpectedLeaf(n) => write!(f, "Node '{n}' is not a leaf"),
            FOTabErr::AlreadyClosed(n) => write!(f, "Node '{n}' is already closed"),
            FOTabErr::ExpectedClosed(n) => {
                write!(f, "Node '{n}' is not the root of a closed subtableaux")
            }
            FOTabErr::LemmaRoot => write!(f, "Root node cannot be used for lemma creation"),
            FOTabErr::LemmaLeaf => write!(f, "Cannot create lemma from a leaf"),
            FOTabErr::ExpectedSiblings(n1, n2) => {
                write!(f, "Nodes '{n1}' and '{n2}' are not siblings")
            }
            FOTabErr::AutoCloseNotEnabled => write!(f, "Auto-close is not enabled for this proof"),
            FOTabErr::ExpectedSameLit(leaf, node) => write!(f, "Leaf '{leaf}' and node '{node}' do not reference the same literal"),
            FOTabErr::CloseRoot => write!(f, "The root node cannot be used for branch closure"),
            FOTabErr::ExpectedParent(node, leaf) => write!(f, "Node '{node}' is not an ancestor of leaf '{leaf}'"),
            FOTabErr::CloseBothNeg(leaf, node) => write!(f, "Leaf '{leaf}' and node '{node}' reference the same literal, but both of them are negated"),
            FOTabErr::CloseBothPos(leaf, node) => write!(f, "Leaf '{leaf}' and node '{node}' reference the same literal, but neither of them are negated"),
            FOTabErr::Unification(e) => fmt::Display::fmt(e, f),
            FOTabErr::UnEqAfterInst(n1, n2) => write!(
                f,
                "Nodes '{n1}' and '{n2}' are not equal after variable instantiation"
            ),
            FOTabErr::InstWouldViolateReg => write!(
                f,
                "This variable instantiation would violate the proof regularity"
            ),
            FOTabErr::WouldMakeIrregular(a) => write!(f, "Expanding this clause would introduce a duplicate node {a} on the branch, making the tree irregular"),
            FOTabErr::WouldMakeNotWeaklyUnconnected => write!(f, "No literal in this clause would be closeable, making the tree unconnected"),
            FOTabErr::WouldMakeNotStronglyUnconnected(n) => write!(f, "No literal in this clause would be closeable with '{n}', making the tree not strongly connected"),
            FOTabErr::NotConnected => write!(f, "The proof tree is currently not sufficiently connected, please close branches first to restore connectedness before expanding more leaves"),
            FOTabErr::BacktrackingDisabled => write!(f, "Backtracking is not enabled for this proof"),
        }
    }
}

pub type FOTabResult<T> = Result<T, FOTabErr>;

#[derive(Clone, Copy, Serialize, Deserialize)]
#[serde(default)]
pub struct FOTabParams {
    #[serde(rename = "type")]
    ty: TableauxType,
    regular: bool,
    backtracking: bool,
    #[serde(rename = "manualVarAssign")]
    manual_var_assign: bool,
}

impl Default for FOTabParams {
    fn default() -> Self {
        Self {
            ty: TableauxType::Unconnected,
            regular: false,
            backtracking: false,
            manual_var_assign: false,
        }
    }
}

pub struct FOTableaux;

impl<'f> Calculus<'f> for FOTableaux {
    type Params = FOTabParams;

    type State = FOTabState;

    type Move = FOTabMove;

    type Error = FOTabErr;

    fn parse_formula(
        formula: &'f str,
        params: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        let clauses = fo_cnf(parse_fo_formula(formula)?)?;

        Ok(FOTabState::new(
            clauses,
            formula,
            params.unwrap_or_default(),
        ))
    }

    fn apply_move(state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        let mut state = state;
        state.status_msg.take();
        match k_move {
            FOTabMove::AutoClose(leaf, node) => apply_auto_close(state, leaf, node),
            FOTabMove::CloseAssign(leaf, node, var_assign) => {
                apply_close_assign(state, leaf, node, var_assign)
            }
            FOTabMove::Expand(leaf, clause) => apply_expand(state, leaf, clause),
            FOTabMove::Lemma(leaf, lemma) => apply_lemma(state, leaf, lemma),
            FOTabMove::Undo => apply_undo(state),
        }
    }

    fn check_close(state: Self::State) -> crate::calculus::CloseMsg {
        state.get_close_msg()
    }
}

pub fn apply_auto_close(
    state: FOTabState,
    leaf_id: usize,
    node_id: usize,
) -> FOTabResult<FOTabState> {
    if state.manual_var_assign {
        return Err(FOTabErr::AutoCloseNotEnabled);
    }

    ensure_basic_closeability(&state, leaf_id, node_id)?;

    let leaf = state.node(leaf_id)?;
    let close_node = state.node(node_id)?;

    // Try to find a unifying variable assignment and pass it to the internal close method
    // which will handle the verification, tree modification, and history management for us
    let mgu = unify(&leaf.relation, &close_node.relation)?;
    close_branch_common(state, leaf_id, node_id, mgu)
}

pub fn apply_close_assign(
    mut state: FOTabState,
    leaf_id: usize,
    node_id: usize,
    unifier: Unifier,
) -> FOTabResult<FOTabState> {
    ensure_basic_closeability(&state, leaf_id, node_id)?;

    if !is_mgu_or_not_unifiable(
        unifier.clone(),
        state.nodes[leaf_id].relation.clone(),
        state.nodes[node_id].relation.clone(),
    ) {
        state.status_msg = Some("The unifier you specified is not an MGU".to_string());
    }

    close_branch_common(state, leaf_id, node_id, unifier)
}

pub fn apply_expand(
    mut state: FOTabState,
    leaf_id: usize,
    clause_id: usize,
) -> FOTabResult<FOTabState> {
    // Ensure that preconditions (correct indices, regularity) are met
    ensure_expandable(&state, leaf_id, clause_id)?;
    let clause = &state.clause_set.clauses()[clause_id];
    let len = state.nodes.len();

    // Quantified variables need to be unique in every newly expanded clause
    // So we append a suffix with the number of the current expansion to every variable
    let atoms = state.clause_expand_preprocessing(clause);

    for (i, atom) in atoms.into_iter().enumerate() {
        let negated = atom.negated();
        let new_leaf = FOTabNode::new(Some(leaf_id), atom.take_lit(), negated, None);
        state.nodes.push(new_leaf);
        let leaf = &mut state.nodes[leaf_id];
        leaf.children.push(len + i)
    }

    // Verify compliance with connectedness criteria
    verify_expand_connectedness(&state, leaf_id)?;

    // Record expansion for backtracking
    if state.backtracking {
        state.moves.push(FOTabMove::Expand(leaf_id, clause_id))
    }

    state.expansion_counter += 1;

    Ok(state)
}

pub fn apply_lemma(
    mut state: FOTabState,
    leaf_id: usize,
    lemma_id: usize,
) -> FOTabResult<FOTabState> {
    // Get lemma atom and verify all preconditions
    let atom = state.get_lemma(leaf_id, lemma_id)?;

    // Add lemma atom to leaf
    // NOTE: We explicitly do not apply clause preprocessing for Lemma expansions
    let negated = atom.negated();
    let new_leaf = FOTabNode::new(Some(leaf_id), atom.take_lit(), negated, Some(lemma_id));
    let size = state.nodes.len();
    state.nodes.push(new_leaf);
    state.nodes.get_mut(leaf_id).unwrap().children.push(size);

    // Verify compliance with connectedness criteria
    verify_expand_connectedness(&state, leaf_id)?;

    // Add move to state history
    if state.backtracking {
        state.moves.push(FOTabMove::Lemma(leaf_id, lemma_id));
    }

    Ok(state)
}

pub fn apply_undo(mut state: FOTabState) -> FOTabResult<FOTabState> {
    if !state.backtracking {
        return Err(FOTabErr::BacktrackingDisabled);
    }

    // Can't undo any more moves in initial state
    if state.moves.is_empty() {
        return Ok(state);
    }

    // Create a fresh clone-state with the same parameters and input formula
    let params = FOTabParams {
        ty: state.ty,
        regular: state.regular,
        backtracking: state.backtracking,
        manual_var_assign: state.manual_var_assign,
    };
    let mut fresh_state = FOTableaux::parse_formula(&state.formula, Some(params))?;
    fresh_state.used_backtracking = true;

    // We don't want to re-do the last move
    state.moves.pop();

    // Re-build the proof tree in the clone state
    for m in state.moves {
        fresh_state = FOTableaux::apply_move(fresh_state, m)?;
    }

    Ok(fresh_state)
}

fn close_branch_common(
    mut state: FOTabState,
    leaf_id: usize,
    node_id: usize,
    unifier: Unifier,
) -> FOTabResult<FOTabState> {
    state.apply_unifier(unifier.clone());
    let close_node = state.node(node_id)?;
    let leaf = state.node(leaf_id)?;

    if !leaf.relation.syn_eq(&close_node.relation) {
        return Err(FOTabErr::UnEqAfterInst(leaf.clone(), close_node.clone()));
    }

    if state.regular && !check_regularity(&state) {
        return Err(FOTabErr::InstWouldViolateReg);
    }

    let leaf = state.node_mut(leaf_id).unwrap();
    leaf.close_ref = Some(node_id);
    state.mark_node_closed(leaf_id);

    if state.backtracking {
        let r#move = FOTabMove::CloseAssign(leaf_id, node_id, unifier);
        state.moves.push(r#move);
    }

    Ok(state)
}

fn verify_expand_regularity(
    state: &FOTabState,
    leaf_id: usize,
    clause: &Clause<Relation>,
) -> FOTabResult<()> {
    let leaf = &state.nodes[leaf_id];
    let mut lst: Vec<Atom<Relation>> = vec![leaf.into()];

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

    let suffix_app =
        VariableSuffixAppend(Symbol::intern(&format!("_{}", state.expansion_counter + 1)));
    let mut atom_list = vec![];

    for atom in clause {
        let rel = Relation::new(
            atom.lit().spelling,
            atom.lit()
                .args
                .iter()
                .map(|a| suffix_app.visit(a))
                .collect(),
        );
        atom_list.push(Atom::new(rel, atom.negated()));
    }

    let clause = clause.atoms();

    for atom in clause {
        if lst.contains(atom) {
            return Err(FOTabErr::WouldMakeIrregular(atom.clone()));
        }
    }

    Ok(())
}

fn verify_expand_connectedness(state: &FOTabState, leaf_id: usize) -> FOTabResult<()> {
    if leaf_id == 0 {
        return Ok(());
    }
    let leaf = state.node(leaf_id)?;
    let children = &leaf.children;

    if state.ty.is_weakly_connected() {
        if !children.iter().any(|c| state.node_is_closable(*c)) {
            return Err(FOTabErr::WouldMakeNotWeaklyUnconnected);
        }
    } else if state.ty.is_strongly_connected()
        && !children.iter().any(|c| state.node_is_directly_closable(*c))
    {
        return Err(FOTabErr::WouldMakeNotStronglyUnconnected(leaf.clone()));
    }
    Ok(())
}

fn check_connectedness(state: &FOTabState, ty: TableauxType) -> bool {
    if ty.is_unconnected() {
        return true;
    }
    let start_nodes = state.root().children();

    let strong = ty.is_strongly_connected();
    start_nodes
        .iter()
        .all(|n| check_connectedness_subtree(state, *n, strong))
}

fn check_connectedness_subtree(state: &FOTabState, root: usize, strong: bool) -> bool {
    let node = &state.nodes[root];

    // A subtree is weakly/strongly connected iff:
    // 1. The root is a leaf OR at least one child of the root is a closed leaf
    // 1a. For strong connectedness: The closed child is closed with the root
    // 2. All child-subtrees are weakly/strongly connected themselves

    // Leaves are trivially connected
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

fn ensure_basic_closeability(
    state: &FOTabState,
    leaf_id: usize,
    node_id: usize,
) -> FOTabResult<()> {
    let leaf = state.node(leaf_id)?;
    let node = state.node(node_id)?;

    if !leaf.is_leaf() {
        return Err(FOTabErr::ExpectedLeaf(leaf.clone()));
    }

    if leaf.is_closed {
        return Err(FOTabErr::AlreadyClosed(leaf.clone()));
    }

    if leaf.lit_stem() != node.lit_stem() {
        return Err(FOTabErr::ExpectedSameLit(leaf.clone(), node.clone()));
    }

    if node_id == 0 {
        return Err(FOTabErr::CloseRoot);
    }

    if !state.node_is_parent_of(node_id, leaf_id)? {
        return Err(FOTabErr::ExpectedParent(node.clone(), leaf.clone()));
    }

    match (leaf.negated, node.negated) {
        (true, true) => Err(FOTabErr::CloseBothNeg(leaf.clone(), node.clone())),
        (false, false) => Err(FOTabErr::CloseBothPos(leaf.clone(), node.clone())),
        _ => Ok(()),
    }
}

fn check_regularity(state: &FOTabState) -> bool {
    let start = &state.root().children;

    start
        .iter()
        .all(|id| check_regularity_subtree(state, *id, vec![]))
}

fn check_regularity_subtree(state: &FOTabState, root: usize, mut lst: Vec<Atom<Relation>>) -> bool {
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

fn ensure_expandable(state: &FOTabState, leaf_id: usize, clause_id: usize) -> FOTabResult<()> {
    if !check_connectedness(state, state.ty) {
        return Err(FOTabErr::NotConnected);
    }

    if leaf_id >= state.nodes.len() {
        return Err(FOTabErr::InvalidNodeId(leaf_id));
    }
    if clause_id >= state.clause_set.size() {
        return Err(FOTabErr::InvalidClauseId(clause_id));
    }

    let leaf = &state.nodes[leaf_id];

    if !leaf.is_leaf() {
        return Err(FOTabErr::ExpectedLeaf(leaf.clone()));
    }
    if leaf.is_closed() {
        return Err(FOTabErr::AlreadyClosed(leaf.clone()));
    }

    let clause = &state.clause_set.clauses()[clause_id];

    if state.regular {
        verify_expand_regularity(state, leaf_id, clause)
    } else {
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FOTabMove {
    AutoClose(usize, usize),
    CloseAssign(usize, usize, Unifier),
    Expand(usize, usize),
    Lemma(usize, usize),
    Undo,
}

impl fmt::Display for FOTabMove {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            FOTabMove::AutoClose(l, r) => write!(f, "AutoClose({},{})", l, r),
            FOTabMove::CloseAssign(l, r, v) => write!(f, "CloseAssign({},{}, {})", l, r, v),
            FOTabMove::Expand(l, r) => write!(f, "Expand({},{})", l, r),
            FOTabMove::Lemma(l, r) => write!(f, "Lemma({},{})", l, r),
            FOTabMove::Undo => write!(f, "Undo"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FOTabState {
    clause_set: ClauseSet<Relation>,
    formula: String,
    ty: TableauxType,
    regular: bool,
    backtracking: bool,
    manual_var_assign: bool,
    nodes: Vec<FOTabNode>,
    moves: Vec<FOTabMove>,
    used_backtracking: bool,
    expansion_counter: u32,
    status_msg: Option<String>,
}

impl ProtectedState for FOTabState {
    fn compute_seal_info(&self) -> String {
        let various = format!("{}|{}", self.formula, self.expansion_counter);
        let opts = format!(
            "{}|{}|{}|{}|{}",
            self.ty.to_string().to_uppercase(),
            self.regular,
            self.backtracking,
            self.used_backtracking,
            self.manual_var_assign
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
            "fotableaux|{}|{}|{}|[{}]|[{}]",
            various, opts, clause_set, nodes, history
        )
    }
}

impl FOTabState {
    pub fn new(clause_set: ClauseSet<Relation>, formula: &str, params: FOTabParams) -> Self {
        Self {
            clause_set,
            formula: formula.to_string(),
            ty: params.ty,
            regular: params.regular,
            backtracking: params.backtracking,
            manual_var_assign: params.manual_var_assign,
            nodes: vec![FOTabNode::new(
                None,
                Relation::new("true".into(), vec![]),
                false,
                None,
            )],
            moves: vec![],
            used_backtracking: false,
            expansion_counter: 0,
            status_msg: None,
        }
    }

    fn root(&self) -> &FOTabNode {
        self.node(0).unwrap()
    }

    fn nodes(&self) -> &Vec<FOTabNode> {
        &self.nodes
    }

    fn node(&self, id: usize) -> FOTabResult<&FOTabNode> {
        if let Some(node) = self.nodes.get(id) {
            Ok(node)
        } else {
            Err(FOTabErr::InvalidNodeId(id))
        }
    }

    fn node_mut(&mut self, id: usize) -> super::TableauxResult<&mut FOTabNode> {
        if let Some(node) = self.nodes.get_mut(id) {
            Ok(node)
        } else {
            Err(TableauxErr::InvalidNodeId(id))
        }
    }

    fn node_is_parent_of(&self, parent_id: usize, child: usize) -> FOTabResult<bool> {
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

    fn mark_node_closed(&mut self, leaf: usize) {
        let mut id = leaf;
        while self.is_leaf(id) || self.all_children_closed(id) {
            let node = &mut self.node_mut(id).unwrap();
            node.mark_closed();
            if node.parent().is_none() {
                break;
            }
            id = node.parent().unwrap();
        }
    }

    fn is_leaf(&self, id: usize) -> bool {
        match self.node(id) {
            Ok(n) => n.is_leaf(),
            Err(_) => false,
        }
    }

    fn all_children_closed(&self, id: usize) -> bool {
        match self.node(id) {
            Ok(n) => n.children().iter().all(|e| self.nodes()[*e].is_closed()),
            Err(_) => false,
        }
    }

    fn get_close_msg(&self) -> CloseMsg {
        let msg = if self.root().is_closed() {
            "The proof tree is not closed".to_string()
        } else {
            "The proof is closed and valid in a $connectedness ${regularity}tableaux $withWithoutBT backtracking".to_string()
        };

        CloseMsg {
            closed: self.root().is_closed(),
            msg,
        }
    }

    fn node_is_closable(&self, id: usize) -> bool {
        match self.node(id) {
            Ok(n) => n.is_leaf() && self.node_ancestry_contains_unifiable(id, n.into()),
            _ => false,
        }
    }

    fn node_is_directly_closable(&self, id: usize) -> bool {
        let node = match self.node(id) {
            Ok(n) => n,
            _ => return false,
        };

        if node.parent.is_none()
            || !node.is_leaf()
            || node.negated == self.nodes[node.parent.unwrap()].negated
        {
            return false;
        }

        let parent = &self.nodes[node.parent.unwrap()];

        matches!(unify::unify(&node.relation, &parent.relation), Ok(_))
    }

    fn clause_expand_preprocessing(
        &self,
        clause: &crate::clause::Clause<Relation>,
    ) -> Vec<crate::clause::Atom<Relation>> {
        let suffix_appender =
            VariableSuffixAppend(Symbol::intern(&format!("_{}", self.expansion_counter + 1)));
        let mut atom_list = Vec::new();

        for atom in clause.atoms() {
            let new_args = atom
                .lit()
                .args
                .iter()
                .map(|a| suffix_appender.visit(&a.clone()))
                .collect();
            let rel = Relation::new(atom.lit().spelling, new_args);
            atom_list.push(Atom::new(rel, atom.negated()));
        }

        atom_list
    }

    fn node_ancestry_contains_unifiable(&self, id: usize, atom: Atom<Relation>) -> bool {
        let mut node = match self.node(id) {
            Ok(n) => n,
            _ => {
                return false;
            }
        };

        while node.parent.is_some() {
            node = &self.nodes[node.parent.unwrap()];

            if node.negated != atom.negated()
                && node.relation.spelling == atom.lit().spelling
                && unify::unify(&node.relation, atom.lit()).is_ok()
            {
                return true;
            }
        }

        false
    }

    fn apply_unifier(&mut self, u: Unifier) {
        for n in &mut self.nodes {
            n.apply_unifier(&u);
        }
    }

    pub fn get_lemma(&self, leaf_id: usize, lemma_id: usize) -> FOTabResult<Atom<Relation>> {
        let leaf = self.node(leaf_id)?;
        let lemma = self.node(lemma_id)?;

        if !leaf.is_leaf() {
            return Err(FOTabErr::ExpectedLeaf(leaf.clone()));
        }

        if leaf.is_closed() {
            return Err(FOTabErr::AlreadyClosed(leaf.clone()));
        }

        if !lemma.is_closed() {
            return Err(FOTabErr::ExpectedClosed(lemma.clone()));
        }

        if lemma.parent().is_none() {
            return Err(FOTabErr::LemmaRoot);
        }

        if lemma.is_leaf() {
            return Err(FOTabErr::LemmaLeaf);
        }

        let common_parent = lemma.parent().unwrap();

        if !self.node_is_parent_of(common_parent, leaf_id)? {
            return Err(FOTabErr::ExpectedSiblings(leaf.clone(), lemma.clone()));
        }

        let atom: Atom<Relation> = lemma.into();
        let atom = atom.not();

        if self.regular {
            verify_expand_regularity(self, leaf_id, &Clause::new(vec![atom.clone()]))?;
        }

        Ok(atom)
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct FOTabNode {
    parent: Option<usize>,
    pub relation: Relation,
    negated: bool,
    lemma_source: Option<usize>,
    is_closed: bool,
    close_ref: Option<usize>,
    children: Vec<usize>,
}

impl<'f> FOTabNode {
    pub fn new(
        parent: Option<usize>,
        relation: Relation,
        negated: bool,
        lemma_source: Option<usize>,
    ) -> Self {
        Self {
            parent,
            relation,
            negated,
            lemma_source,
            is_closed: false,
            close_ref: None,
            children: Vec::new(),
        }
    }

    pub(crate) fn lit_stem(&self) -> (Symbol, usize) {
        (self.relation.spelling, self.relation.args.len())
    }

    fn apply_unifier(&mut self, u: &Unifier) {
        self.relation.apply_unifier(u);
    }

    pub fn info(&self) -> String {
        let neg = if self.negated { "n" } else { "p" };
        let parent = match self.parent {
            Some(p) => p.to_string(),
            None => "null".to_string(),
        };
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
            "{};{};{};{};{};({})",
            self.relation, neg, parent, r#ref, closed, child_list
        )
    }
}

impl<'f> From<FOTabNode> for Atom<Relation> {
    fn from(n: FOTabNode) -> Self {
        Atom::new(n.relation, n.negated)
    }
}

impl<'f> From<&FOTabNode> for Atom<Relation> {
    fn from(n: &FOTabNode) -> Self {
        Atom::new(n.relation.clone(), n.negated)
    }
}

impl<'f> TableauxNode<Relation> for FOTabNode {
    fn parent(&self) -> Option<usize> {
        self.parent
    }

    fn spelling(&self) -> String {
        self.relation.to_string()
    }

    fn literal_stem(&self) -> String {
        format!("{}{}", self.relation.spelling, self.relation.args.len())
    }

    fn negated(&self) -> bool {
        self.negated
    }

    fn is_closed(&self) -> bool {
        self.is_closed
    }

    fn close_ref(&self) -> Option<usize> {
        self.close_ref
    }

    fn children(&self) -> &Vec<usize> {
        &self.children
    }

    fn lemma_source(&self) -> Option<usize> {
        self.lemma_source
    }

    fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }

    fn mark_closed(&mut self) {
        self.is_closed = true;
    }

    fn to_atom(&self) -> Atom<Relation> {
        self.into()
    }
}

impl fmt::Display for FOTabNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.negated {
            write!(f, "!{}", self.relation)
        } else {
            write!(f, "{}", self.relation)
        }
    }
}

impl Serialize for FOTabState {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("FOTabState", 13)?;
        state.serialize_field("clauseSet", &self.clause_set)?;
        state.serialize_field("formula", &self.formula)?;
        state.serialize_field("type", &self.ty)?;
        state.serialize_field("regular", &self.regular)?;
        state.serialize_field("backtracking", &self.backtracking)?;
        state.serialize_field("manualVarAssign", &self.manual_var_assign)?;
        state.serialize_field("tree", &self.nodes)?;
        state.serialize_field("moveHistory", &self.moves)?;
        state.serialize_field("usedBacktracking", &self.used_backtracking)?;
        state.serialize_field("expansionCounter", &self.expansion_counter)?;
        state.serialize_field("seal", &self.compute_seal_info())?;
        let rendered: Vec<String> = self
            .clause_set
            .clauses()
            .iter()
            .map(|c| {
                c.atoms()
                    .iter()
                    .map(Atom::to_string)
                    .fold(String::new(), |a, b| a + &b + ", ")
            })
            .collect();
        state.serialize_field("renderedClauseSet", &rendered)?;
        state.serialize_field("statusMessage", &self.status_msg)?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for FOTabState {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "clauseSet")]
            ClauseSet,
            #[serde(rename = "formula")]
            Formula,
            #[serde(rename = "type")]
            Ty,
            #[serde(rename = "regular")]
            Regular,
            #[serde(rename = "backtracking")]
            Backtracking,
            #[serde(rename = "manualVarAssign")]
            ManualVarAssign,
            #[serde(rename = "tree")]
            Nodes,
            #[serde(rename = "moveHistory")]
            Moves,
            #[serde(rename = "usedBacktracking")]
            UsedBacktracking,
            #[serde(rename = "expansionCounter")]
            ExpansionCounter,
            #[serde(rename = "seal")]
            Seal,
            #[serde(rename = "renderedClauseSet")]
            RenderedClauseSet,
            #[serde(rename = "statusMessage")]
            StatusMessage,
        }

        struct StateVisitor;

        impl<'de> Visitor<'de> for StateVisitor {
            type Value = FOTabState;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct FOTabState")
            }

            fn visit_map<V>(self, mut map: V) -> Result<FOTabState, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut clause_set: Option<ClauseSet<Relation>> = None;
                let mut formula: Option<String> = None;
                let mut ty: Option<TableauxType> = None;
                let mut regular: Option<bool> = None;
                let mut backtracking: Option<bool> = None;
                let mut manual_var_assign: Option<bool> = None;
                let mut nodes: Option<Vec<FOTabNode>> = None;
                let mut moves: Option<Vec<FOTabMove>> = None;
                let mut used_backtracking: Option<bool> = None;
                let mut expansion_counter: Option<u32> = None;
                let mut seal: Option<String> = None;
                let mut rendered_clause_set: Option<Vec<String>> = None;
                let mut status_msg: Option<String> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::ClauseSet => {
                            if clause_set.is_some() {
                                return Err(de::Error::duplicate_field("clauseSet"));
                            }
                            clause_set = Some(map.next_value()?);
                        }
                        Field::Formula => {
                            if formula.is_some() {
                                return Err(de::Error::duplicate_field("formula"));
                            }
                            formula = Some(map.next_value()?);
                        }
                        Field::Ty => {
                            if ty.is_some() {
                                return Err(de::Error::duplicate_field("type"));
                            }
                            ty = Some(map.next_value()?);
                        }
                        Field::Regular => {
                            if regular.is_some() {
                                return Err(de::Error::duplicate_field("regular"));
                            }
                            regular = Some(map.next_value()?);
                        }
                        Field::Backtracking => {
                            if backtracking.is_some() {
                                return Err(de::Error::duplicate_field("backtracking"));
                            }
                            backtracking = Some(map.next_value()?);
                        }
                        Field::ManualVarAssign => {
                            if manual_var_assign.is_some() {
                                return Err(de::Error::duplicate_field("manualVarAssign"));
                            }
                            manual_var_assign = Some(map.next_value()?);
                        }
                        Field::Nodes => {
                            if nodes.is_some() {
                                return Err(de::Error::duplicate_field("tree"));
                            }
                            nodes = Some(map.next_value()?);
                        }
                        Field::Moves => {
                            if moves.is_some() {
                                return Err(de::Error::duplicate_field("moveHistory"));
                            }
                            moves = Some(map.next_value()?);
                        }
                        Field::UsedBacktracking => {
                            if used_backtracking.is_some() {
                                return Err(de::Error::duplicate_field("usedBacktracking"));
                            }
                            used_backtracking = Some(map.next_value()?);
                        }
                        Field::ExpansionCounter => {
                            if expansion_counter.is_some() {
                                return Err(de::Error::duplicate_field("expansionCounter"));
                            }
                            expansion_counter = Some(map.next_value()?);
                        }
                        Field::Seal => {
                            if seal.is_some() {
                                return Err(de::Error::duplicate_field("seal"));
                            }
                            seal = Some(map.next_value()?);
                        }
                        Field::RenderedClauseSet => {
                            if rendered_clause_set.is_some() {
                                return Err(de::Error::duplicate_field("renderedClauseSet"));
                            }
                            rendered_clause_set = Some(map.next_value()?);
                        }
                        Field::StatusMessage => {
                            if status_msg.is_some() {
                                return Err(de::Error::duplicate_field("statusMsg"));
                            }
                            status_msg = Some(map.next_value()?);
                        }
                    }
                }

                let clause_set = clause_set.ok_or_else(|| de::Error::missing_field("clauseSet"))?;
                let formula = formula.ok_or_else(|| de::Error::missing_field("formula"))?;
                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                let regular = regular.ok_or_else(|| de::Error::missing_field("regular"))?;
                let backtracking =
                    backtracking.ok_or_else(|| de::Error::missing_field("backtracking"))?;
                let manual_var_assign =
                    manual_var_assign.ok_or_else(|| de::Error::missing_field("manualVarAssign"))?;
                let nodes = nodes.ok_or_else(|| de::Error::missing_field("tree"))?;
                let moves = moves.ok_or_else(|| de::Error::missing_field("moveHistory"))?;
                let used_backtracking = used_backtracking
                    .ok_or_else(|| de::Error::missing_field("usedBacktracking"))?;
                let expansion_counter = expansion_counter
                    .ok_or_else(|| de::Error::missing_field("expansionCounter"))?;
                let seal = seal.ok_or_else(|| de::Error::missing_field("seal"))?;
                if rendered_clause_set.is_none() {
                    return Err(de::Error::missing_field("renderedClauseSet"));
                }

                let s = FOTabState {
                    clause_set,
                    formula,
                    ty,
                    regular,
                    backtracking,
                    manual_var_assign,
                    nodes,
                    moves,
                    used_backtracking,
                    expansion_counter,
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
            "formula",
            "type",
            "regular",
            "backtracking",
            "manualVarAssign",
            "tree",
            "moveHistory",
            "usedBacktracking",
            "expansionCounter",
            "seal",
            "renderedClauseSet",
            "statusMessage",
        ];
        deserializer.deserialize_struct("FOTabState", FIELDS, StateVisitor)
    }
}

impl Serialize for FOTabMove {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let num_fields = match self {
            FOTabMove::Undo => 1,
            FOTabMove::CloseAssign(..) => 4,
            _ => 3,
        };
        let mut state = serializer.serialize_struct("FOTabMove", num_fields)?;
        let ty = match self {
            FOTabMove::Undo => "tableaux-undo",
            FOTabMove::AutoClose(..) => "tableaux-close",
            FOTabMove::CloseAssign(..) => "tableaux-close-assign",
            FOTabMove::Expand(..) => "tableaux-expand",
            FOTabMove::Lemma(..) => "tableaux-lemma",
        };
        state.serialize_field("type", ty)?;
        if num_fields == 3 {
            let (id1, id2) = match self {
                FOTabMove::Undo => panic!(),
                FOTabMove::AutoClose(id1, id2) => (id1, id2),
                FOTabMove::Expand(id1, id2) => (id1, id2),
                FOTabMove::Lemma(id1, id2) => (id1, id2),
                FOTabMove::CloseAssign(id1, id2, _) => (id1, id2),
            };
            state.serialize_field("id1", id1)?;
            state.serialize_field("id2", id2)?;
        }
        if let FOTabMove::CloseAssign(_, _, u) = self {
            state.serialize_field("varAssign", u)?;
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for FOTabMove {
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
            #[serde(rename = "varAssign")]
            VarAssign,
        }

        struct MoveVisitor;

        impl<'de> Visitor<'de> for MoveVisitor {
            type Value = FOTabMove;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct FOTabMove")
            }

            fn visit_map<V>(self, mut map: V) -> Result<FOTabMove, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut id1: Option<usize> = None;
                let mut id2: Option<usize> = None;
                let mut unifier: Option<Unifier> = None;

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
                        Field::VarAssign => {
                            if unifier.is_some() {
                                return Err(de::Error::duplicate_field("varAssign"));
                            }
                            unifier = Some(map.next_value()?);
                        }
                    }
                }

                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                Ok(if ty == "tableaux-undo" {
                    FOTabMove::Undo
                } else {
                    let id1 = id1.ok_or_else(|| de::Error::missing_field("id1"))?;
                    let id2 = id2.ok_or_else(|| de::Error::missing_field("id2"))?;

                    let ty: &str = &ty;
                    match ty {
                        "tableaux-expand" => FOTabMove::Expand(id1, id2),
                        "tableaux-close" => FOTabMove::AutoClose(id1, id2),
                        "tableaux-lemma" => FOTabMove::Lemma(id1, id2),
                        "tableaux-close-assign" => {
                            let unifier =
                                unifier.ok_or_else(|| de::Error::missing_field("varAssign"))?;
                            FOTabMove::CloseAssign(id1, id2, unifier)
                        }
                        _ => panic!(),
                    }
                })
            }
        }

        const FIELDS: &[&str] = &["type", "id1", "id2", "varAssign"];
        deserializer.deserialize_struct("FOTabMove", FIELDS, MoveVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    pub use crate::session;

    mod auto_close {
        use super::{super::*, *};

        fn param() -> Option<FOTabParams> {
            Some(FOTabParams {
                ty: TableauxType::Unconnected,
                regular: false,
                backtracking: false,
                manual_var_assign: false,
            })
        }

        fn formula(i: u8) -> &'static str {
            match i {
                0 => r"\all A: (\all B: (R(A) -> R(B) & !R(A) | !R(B)))",
                1 => "(R(a) <-> !R(b)) | (!R(a) -> R(b))",
                2 => r"\ex A : (R(A) & (\all B: !R(B) & !R(A)))",
                3 => r"\ex Usk: (R(Usk) -> (!\ex Usk: (R(sk1) & !R(Usk) | R(Usk) & !R(sk1))))",
                4 => r"\all A: (Sk1(A) -> !\ex B: (R(A) & !R(B) -> Sk1(B) | !Sk1(A)))",
                5 => r"\all X: (R(g(X)) & !R(f(X)))",
                _ => panic!(),
            }
        }

        fn state(i: u8) -> FOTabState {
            FOTableaux::parse_formula(formula(i), param()).unwrap()
        }

        #[test]
        fn state1() {
            session(|| {
                let s = state(0);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(2, 1)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::AutoClose(6, 2)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::AutoClose(4, 2)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::AutoClose(5, 2)).unwrap();

                assert!(s.nodes[6].is_closed);
                assert_eq!(2, s.nodes[6].close_ref.unwrap());

                assert!(FOTableaux::apply_move(s.clone(), FOTabMove::AutoClose(4, 1)).is_err());
                assert!(FOTableaux::apply_move(s, FOTabMove::AutoClose(4, 3)).is_err());
            })
        }

        #[test]
        fn state2() {
            session(|| {
                let s = state(1);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(3, 2)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(4, 3)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::AutoClose(6, 3)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::AutoClose(9, 4)).unwrap();

                assert!(s.nodes[6].is_closed);
                assert_eq!(3, s.nodes[6].close_ref.unwrap());

                assert!(s.nodes[9].is_closed);
                assert_eq!(4, s.nodes[9].close_ref.unwrap());

                assert!(FOTableaux::apply_move(s.clone(), FOTabMove::AutoClose(5, 1)).is_err());
                assert!(FOTableaux::apply_move(s, FOTabMove::AutoClose(6, 3)).is_err());
            })
        }

        #[test]
        fn state3() {
            session(|| {
                let s = state(2);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(1, 1)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(2, 2)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::AutoClose(3, 1)).unwrap();

                assert!(s.nodes[3].is_closed);
                assert_eq!(1, s.nodes[3].close_ref.unwrap());

                assert!(s.nodes[1].is_closed);

                assert!(FOTableaux::apply_move(s.clone(), FOTabMove::AutoClose(3, 1)).is_err());
                assert!(FOTableaux::apply_move(s, FOTabMove::AutoClose(2, 1)).is_err());
            })
        }

        #[test]
        fn invalid() {
            session(|| {
                let s = state(0);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(2, 1)).unwrap();

                assert_eq!(
                    FOTabErr::InvalidNodeId(42),
                    FOTableaux::apply_move(s.clone(), FOTabMove::AutoClose(6, 42)).unwrap_err()
                );
                assert!(FOTableaux::apply_move(s.clone(), FOTabMove::AutoClose(6, 0)).is_err());
                assert_eq!(
                    FOTabErr::InvalidNodeId(777),
                    FOTableaux::apply_move(s.clone(), FOTabMove::AutoClose(777, 2)).unwrap_err()
                );
                assert_eq!(
                    FOTabErr::InvalidNodeId(usize::MAX),
                    FOTableaux::apply_move(s, FOTabMove::AutoClose(usize::MAX, 5)).unwrap_err()
                );
            })
        }

        #[test]
        fn impossible_uni() {
            session(|| {
                let s = state(5);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(1, 1)).unwrap();

                assert!(FOTableaux::apply_move(s, FOTabMove::AutoClose(2, 1)).is_err());
            })
        }
    }

    mod close {
        use super::{super::*, *};
        use crate::parse::fo::parse_fo_term;
        use std::collections::HashMap;
        use unify::Unifier;

        fn param() -> Option<FOTabParams> {
            Some(FOTabParams {
                ty: TableauxType::Unconnected,
                regular: true,
                backtracking: false,
                manual_var_assign: true,
            })
        }

        fn param_non_reg() -> Option<FOTabParams> {
            Some(FOTabParams {
                ty: TableauxType::Unconnected,
                regular: false,
                backtracking: false,
                manual_var_assign: true,
            })
        }

        fn formula(i: u8) -> &'static str {
            match i {
                0 => r"\all X: R(X) & R(c) & !R(c)",
                1 => r"\all X: \ex Y: R(X,Y) & \ex Z: \all W: !R(Z, W)", // R(X, sk1(X)), !R(sk2, W)
                2 => r"\all A: (\all B: (R(A) -> R(B) & !R(A) | !R(B)))",
                3 => r"\all A: (R(A) -> !\ex B: (R(A) & !R(B) -> R(B) | R(A)))",
                _ => panic!(),
            }
        }

        fn state(i: u8) -> FOTabState {
            FOTableaux::parse_formula(formula(i), param()).unwrap()
        }

        fn state_non_reg(i: u8) -> FOTabState {
            FOTableaux::parse_formula(formula(i), param_non_reg()).unwrap()
        }

        macro_rules! unifier {
           ($( $f:expr, $t:expr );*) => {{
            let mut map = HashMap::new();
            $(
                map.insert(Symbol::intern($f), parse_fo_term($t).unwrap());
            )*
            Unifier::from_map(map)
        }};
        }

        #[test]
        fn reg_violation() {
            session(|| {
                let s = state(0);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(1, 1)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(2, 2)).unwrap();

                assert_eq!(
                    FOTabErr::InstWouldViolateReg,
                    FOTableaux::apply_move(s, FOTabMove::CloseAssign(3, 1, unifier!("X_1", "c")))
                        .unwrap_err()
                )
            })
        }

        #[test]
        fn manual_assign() {
            session(|| {
                let s = state(0);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 1)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(1, 2)).unwrap();

                assert_eq!(
                    FOTabErr::AutoCloseNotEnabled,
                    FOTableaux::apply_move(s, FOTabMove::AutoClose(2, 1)).unwrap_err()
                )
            })
        }

        #[test]
        fn incorrect_inst() {
            session(|| {
                let s = state(1);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(1, 1)).unwrap();

                assert!(FOTableaux::apply_move(
                    s,
                    FOTabMove::CloseAssign(2, 1, unifier!("X_1", "sk2"; "W_2", "sk1(c)")),
                )
                .is_err(),)
            })
        }

        #[test]
        fn valid1() {
            session(|| {
                let s = state(1);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(1, 1)).unwrap();

                let s = FOTableaux::apply_move(
                    s,
                    FOTabMove::CloseAssign(2, 1, unifier!("X_1", "sk2"; "W_2", "sk1(sk2)")),
                )
                .unwrap();
                assert!(FOTableaux::check_close(s).closed)
            })
        }

        #[test]
        fn valid2() {
            session(|| {
                let s = state_non_reg(2);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(2, 1)).unwrap();

                let u = unifier!("B_2", "B_1"; "A_2", "B_1");

                let s = FOTableaux::apply_move(s, FOTabMove::CloseAssign(6, 2, u.clone())).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::CloseAssign(4, 2, u.clone())).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::CloseAssign(5, 2, u)).unwrap();

                assert!(s.nodes[2].is_closed);
                assert!(s.nodes[4].is_closed);
                assert_eq!(2, s.nodes[4].close_ref.unwrap());
                assert!(s.nodes[5].is_closed);
                assert_eq!(2, s.nodes[5].close_ref.unwrap());
                assert!(s.nodes[6].is_closed);
                assert_eq!(2, s.nodes[6].close_ref.unwrap());
            })
        }
    }

    mod json {
        use super::*;
        use crate::session;
        use crate::tamper_protect::ProtectedState;

        #[test]
        fn move_valid() {
            session(|| {
                let json = "{\"type\": \"tableaux-expand\", \"id1\": 0, \"id2\": 42}";
                let r#move = serde_json::from_str(json).unwrap();
                assert_eq!(FOTabMove::Expand(0, 42), r#move);
            });
        }

        #[test]
        fn move_null() {
            session(|| {
                let json = "{\"type\": \"tableaux-expand\", \"id1\": 0, \"id2\": null}";
                let r#move: Result<FOTabMove, serde_json::Error> = serde_json::from_str(json);
                assert!(r#move.is_err());
            });
        }

        #[test]
        fn move_missing_field() {
            session(|| {
                let json = "{\"type\": \"tableaux-expand\", \"id2\": 42, \"varAssign\":{}}";
                let r#move: Result<FOTabMove, serde_json::Error> = serde_json::from_str(json);
                assert!(r#move.is_err());
            });
        }

        #[test]
        fn move_type_mismatch() {
            session(|| {
                let json = "{\"type\": \"tableaux-expand\", \"id2\": \"dream\", \"varAssign\":{}}";
                let r#move: Result<FOTabMove, serde_json::Error> = serde_json::from_str(json);
                assert!(r#move.is_err());
            });
        }

        #[test]
        fn state_empty() {
            session(|| {
                let json = "{\"clauseSet\":{\"clauses\":[{\"atoms\":[{\"lit\":{\"spelling\":\"R\",\"arguments\":[{\"type\":\"QuantifiedVariable\",\"spelling\":\"X\"}]},\"negated\":false}]},{\"atoms\":[{\"lit\":{\"spelling\":\"R\",\"arguments\":[{\"type\":\"Constant\",\"spelling\":\"c\"}]},\"negated\":true}]}]},\"formula\":\"\\\\all X: R(X) & !R(c)\",\"type\":\"UNCONNECTED\",\"regular\":false,\"backtracking\":false,\"manualVarAssign\":false,\"tree\":[{\"parent\":null,\"relation\":{\"spelling\":\"true\",\"arguments\":[]},\"negated\":false,\"isClosed\":false,\"closeRef\":null,\"children\":[],\"spelling\":\"true()\"}],\"moveHistory\":[],\"usedBacktracking\":false,\"expansionCounter\":0,\"seal\":\"47E0E51B486CDF0FEB644B195CFBCB08E61C2556BD67D84B86B08CB658055ACB\",\"renderedClauseSet\":[\"R(X)\",\"!R(c)\"]}";
                let state: FOTabState = serde_json::from_str(json).unwrap();
                let hash = "fotableaux|\\all X: R(X) & !R(c)|0|UNCONNECTED|false|false|false|false|{R(X)}, {!R(c)}|[true();p;null;-;o;()]|[]";
                assert_eq!(hash, state.compute_seal_info())
            });
        }

        #[test]
        fn state_mod() {
            session(|| {
                let json = "{\"clauseSet\":{\"clauses\":[{\"atoms\":[{\"lit\":{\"spelling\":\"R\",\"arguments\":[{\"type\":\"Constant\",\"spelling\":\"sk1\"}]},\"negated\":false}]}]},\"formula\":\"\\\\ex X: R(X)\",\"type\":\"UNCONNECTED\",\"regular\":false,\"backtracking\":false,\"manualVarAssign\":false,\"tree\":[{\"parent\":null,\"relation\":{\"spelling\":\"true\",\"arguments\":[]},\"negated\":false,\"lemmaSource\":null,\"isClosed\":false,\"closeRef\":null,\"children\":[],\"spelling\":\"true()\"}],\"moveHistory\":[],\"usedBacktracking\":false,\"expansionCounter\":0,\"seal\":\"22B8CEDC626EBF36DAAA3E50356CD328C075805A0538EA0F91B4C88658D8C465\",\"renderedClauseSet\":[\"R(sk1)\"],\"statusMessage\":null}";
                assert!(serde_json::from_str::<FOTabState>(json).is_err())
            });
        }
    }

    mod lemma {
        use super::*;
        use crate::parse::fo::parse_fo_term;
        use crate::session;
        use std::collections::HashMap;

        fn auto_param() -> Option<FOTabParams> {
            Some(FOTabParams {
                ty: TableauxType::Unconnected,
                regular: false,
                backtracking: false,
                manual_var_assign: false,
            })
        }

        fn manual_param() -> Option<FOTabParams> {
            Some(FOTabParams {
                ty: TableauxType::Unconnected,
                regular: false,
                backtracking: false,
                manual_var_assign: true,
            })
        }

        fn formula(i: u8) -> &'static str {
            match i {
                0 => r"\all A: (\all B: (R(A) -> R(B) & !R(A) | !R(B)))",
                1 => "\\all A: (R(A) -> !\\ex B: (R(A) & !R(B) -> R(B) & R(A)))",
                _ => panic!(),
            }
        }

        fn auto_state(i: u8) -> FOTabState {
            FOTableaux::parse_formula(formula(i), auto_param()).unwrap()
        }

        fn manual_state(i: u8) -> FOTabState {
            FOTableaux::parse_formula(formula(i), manual_param()).unwrap()
        }

        macro_rules! unifier {
            ($( $f:expr, $t:expr );*) => {{
                let mut map = HashMap::new();
                $(
                    map.insert(Symbol::intern($f), parse_fo_term($t).unwrap());
                )*
                Unifier::from_map(map)
            }};
        }

        #[test]
        fn valid1() {
            session(|| {
                let state = manual_state(0);
                // {!R(A), R(B), !R(B)}, {!R(A), !R(A), !R(B)}
                let u = unifier!("B_1", "c"; "A_2", "c"; "B_2", "c");
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(2, 1)).unwrap();

                let state =
                    FOTableaux::apply_move(state, FOTabMove::CloseAssign(4, 2, u.clone())).unwrap();
                let state =
                    FOTableaux::apply_move(state, FOTabMove::CloseAssign(5, 2, u.clone())).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::CloseAssign(6, 2, u)).unwrap();

                let state = FOTableaux::apply_move(state, FOTabMove::Lemma(1, 2)).unwrap();

                assert_eq!(2, state.nodes[7].lemma_source.unwrap());
                assert!(state.nodes[7].negated);
            });
        }

        #[test]
        fn valid2() {
            session(|| {
                let state = auto_state(0);
                // {!R(A), R(B), !R(B)}, {!R(A), !R(A), !R(B)}
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(2, 1)).unwrap();

                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(4, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(5, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(6, 2)).unwrap();

                let state = FOTableaux::apply_move(state, FOTabMove::Lemma(1, 2)).unwrap();

                assert_eq!(2, state.nodes[7].lemma_source.unwrap());
                assert!(state.nodes[7].negated);
            });
        }

        #[test]
        fn valid3() {
            session(|| {
                let state = auto_state(1);
                // {!R(A), R(A)}, {!R(A), !R(B)}, {!R(A), !R(B), !R(A)}
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(2, 2)).unwrap();

                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(3, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(4, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(5, 2)).unwrap();

                let state = FOTableaux::apply_move(state, FOTabMove::Lemma(1, 2)).unwrap();

                assert_eq!(2, state.nodes[6].lemma_source.unwrap());
                assert!(state.nodes[6].negated);

                let state = FOTableaux::apply_move(state, FOTabMove::Expand(6, 0)).unwrap();
                FOTableaux::apply_move(state, FOTabMove::AutoClose(8, 6)).unwrap();
            });
        }

        #[test]
        fn valid4() {
            session(|| {
                let state = auto_state(1);
                // {!R(A), R(A)}, {!R(A), !R(B)}, {!R(A), !R(B), !R(A)}
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(2, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(1, 1)).unwrap();

                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(3, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(4, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(5, 2)).unwrap();

                FOTableaux::apply_move(state, FOTabMove::Lemma(6, 2)).unwrap();
            });
        }

        #[test]
        fn invalid() {
            session(|| {
                let state = auto_state(1);
                // {!R(A), R(A)}, {!R(A), !R(B)}, {!R(A), !R(B), !R(A)}
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(2, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(1, 1)).unwrap();

                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(3, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(4, 2)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::AutoClose(5, 2)).unwrap();

                assert!(FOTableaux::apply_move(state.clone(), FOTabMove::Lemma(0, 2)).is_err());
                assert!(FOTableaux::apply_move(state.clone(), FOTabMove::Lemma(0, 2)).is_err());
                assert!(FOTableaux::apply_move(state, FOTabMove::Lemma(5, 3)).is_err());
            });
        }

        #[test]
        fn special_case() {
            session(|| {
                let state = auto_state(0);
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                assert!(FOTableaux::apply_move(state.clone(), FOTabMove::Lemma(0, 0)).is_err());
                assert!(FOTableaux::apply_move(state, FOTabMove::Lemma(usize::MAX, 0)).is_err());
            })
        }
    }

    mod mgu_warning {
        use super::*;
        use crate::parse::fo::parse_fo_term;
        use crate::session;
        use std::collections::HashMap;

        macro_rules! unifier {
            ($( $f:expr, $t:expr );*) => {{
                let mut map = HashMap::new();
                $(
                    map.insert(Symbol::intern($f), parse_fo_term($t).unwrap());
                )*
                Unifier::from_map(map)
            }};
        }

        #[test]
        fn non_mgu() {
            session(|| {
                let state =
                    FOTableaux::parse_formula("/all X: R(X) & /all Y: !R(Y)", None).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(1, 1)).unwrap();

                let r#move = FOTabMove::CloseAssign(2, 1, unifier!("X_1", "c"; "Y_2", "c"));
                let state = FOTableaux::apply_move(state, r#move).unwrap();

                assert!(state.status_msg.is_some())
            });
        }

        #[test]
        fn valid_mgu() {
            session(|| {
                let state = FOTableaux::parse_formula("/all X: R(X) & !R(c)", None).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(1, 1)).unwrap();

                let r#move = FOTabMove::CloseAssign(2, 1, unifier!("X_1", "c"));
                let state = FOTableaux::apply_move(state, r#move).unwrap();

                assert_eq!(None, state.status_msg);

                let state =
                    FOTableaux::parse_formula("/all X: R(X) & /all Y: !R(Y)", None).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(1, 1)).unwrap();

                let r#move = FOTabMove::CloseAssign(2, 1, unifier!("Y_2", "X_1"));
                let state = FOTableaux::apply_move(state, r#move).unwrap();

                assert_eq!(None, state.status_msg)
            });
        }

        #[test]
        fn ambiguous_mgu() {
            session(|| {
                let state =
                    FOTableaux::parse_formula("/all X: R(X) & /all Y: !R(Y)", None).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(1, 1)).unwrap();

                let r#move = FOTabMove::CloseAssign(2, 1, unifier!("X_1", "X_1"; "Y_2", "X_1"));
                let state = FOTableaux::apply_move(state, r#move).unwrap();

                assert_eq!(None, state.status_msg);

                let state =
                    FOTableaux::parse_formula("/all X: R(X) & /all Y: !R(Y)", None).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 0)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(1, 1)).unwrap();

                let r#move = FOTabMove::CloseAssign(2, 1, unifier!("X_1", "Y_2"; "Y_2", "Y_2"));
                let state = FOTableaux::apply_move(state, r#move).unwrap();

                assert_eq!(None, state.status_msg)
            });
        }

        #[test]
        fn extra_vars() {
            session(|| {
                let state =
                    FOTableaux::parse_formula("/all X: /all Z: (R(X)|Q(Z)) & /all Y: !R(Y)", None)
                        .unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 1)).unwrap();
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(1, 0)).unwrap();

                let r#move = FOTabMove::CloseAssign(
                    2,
                    1,
                    unifier!("X_2", "X_2"; "Y_1", "X_2"; "Z_2", "X_2"),
                );
                let state = FOTableaux::apply_move(state, r#move).unwrap();

                assert_eq!(None, state.status_msg);
            });
        }

        #[test]
        fn msg_reset() {
            session(|| {
                let state =
                    FOTableaux::parse_formula("/all X: (R(X)|Q(c)) & /all Y: !R(Y)", None).unwrap();
                assert_eq!(None, state.status_msg);
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(0, 1)).unwrap();
                assert_eq!(None, state.status_msg);
                let state = FOTableaux::apply_move(state, FOTabMove::Expand(1, 0)).unwrap();
                assert_eq!(None, state.status_msg);

                let r#move = FOTabMove::CloseAssign(2, 1, unifier!("X_2", "c"; "Y_1", "c"));
                let state = FOTableaux::apply_move(state, r#move).unwrap();
                assert!(state.status_msg.is_some());

                let state = FOTableaux::apply_move(state, FOTabMove::Expand(3, 1)).unwrap();
                assert_eq!(None, state.status_msg)
            });
        }
    }

    mod undo {
        use super::*;
        use crate::parse::fo::parse_fo_term;
        use crate::session;
        use std::collections::HashMap;

        fn param() -> Option<FOTabParams> {
            Some(FOTabParams {
                ty: TableauxType::Unconnected,
                regular: false,
                backtracking: true,
                manual_var_assign: false,
            })
        }

        fn manual_param() -> Option<FOTabParams> {
            Some(FOTabParams {
                ty: TableauxType::Unconnected,
                regular: false,
                backtracking: true,
                manual_var_assign: true,
            })
        }

        fn formula(i: u8) -> &'static str {
            match i {
                0 => "\\all X: R(X) & R(c) & !R(c)",
                1 => "\\all A: (\\all B: (R(A) -> R(B) & !R(A) | !R(B)))",
                2 => "\\all A: (R(A) -> !\\ex B: (R(A) & !R(B) -> R(B) | R(A)))",
                _ => panic!(),
            }
        }

        fn state(i: u8) -> FOTabState {
            FOTableaux::parse_formula(formula(i), param()).unwrap()
        }

        fn manual_state(i: u8) -> FOTabState {
            FOTableaux::parse_formula(formula(i), manual_param()).unwrap()
        }

        macro_rules! unifier {
            ($( $f:expr, $t:expr );*) => {{
                let mut map = HashMap::new();
                $(
                    map.insert(Symbol::intern($f), parse_fo_term($t).unwrap());
                )*
                Unifier::from_map(map)
            }};
        }

        #[test]
        fn true_node() {
            session(|| {
                let state = state(0);
                assert!(!state.used_backtracking);

                let state = FOTableaux::apply_move(state, FOTabMove::Undo).unwrap();
                assert_eq!(1, state.nodes.len());
                assert!(state.moves.is_empty());
                assert!(!state.used_backtracking);
            });
        }

        #[test]
        fn undo1() {
            session(|| {
                // {!R(a), R(b), !R(b)}, {!R(a), !R(a), !R(b)}
                let s = state(1);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(2, 1)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::AutoClose(6, 2)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::AutoClose(4, 2)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::AutoClose(5, 2)).unwrap();

                let s = FOTableaux::apply_move(s, FOTabMove::Undo).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Undo).unwrap();

                assert!(s.nodes[6].is_closed);
                assert_eq!(2, s.nodes[6].close_ref.unwrap());

                assert!(!s.nodes[2].is_closed);
                assert!(!s.nodes[4].is_closed);
                assert!(s.nodes[4].close_ref.is_none());
                assert!(!s.nodes[5].is_closed);
                assert!(s.nodes[5].close_ref.is_none());

                assert!(s.used_backtracking);
            });
        }

        #[test]
        fn undo2() {
            session(|| {
                let u = unifier!("B_2", "A_1"; "A_2", "A_1");
                // {!R(A), R(A)}, {!R(A), !R(B)}, {!R(A), !R(B)}, {!R(A), !R(A)}
                let s = manual_state(2);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(2, 1)).unwrap();

                let s = FOTableaux::apply_move(s, FOTabMove::CloseAssign(3, 2, u.clone())).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::CloseAssign(4, 2, u)).unwrap();

                assert_eq!("R(A_1)", &s.nodes[2].spelling());
                assert_eq!("R(A_1)", &s.nodes[3].spelling());
                assert_eq!("R(A_1)", &s.nodes[4].spelling());

                let s = FOTableaux::apply_move(s, FOTabMove::Undo).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Undo).unwrap();

                assert_eq!("R(A_1)", &s.nodes[2].spelling());
                assert_eq!("R(A_2)", &s.nodes[3].spelling());
                assert_eq!("R(B_2)", &s.nodes[4].spelling());

                assert!(!s.nodes[2].is_closed);
                assert!(!s.nodes[3].is_closed);
                assert!(s.nodes[3].close_ref.is_none());
                assert!(!s.nodes[4].is_closed);
                assert!(s.nodes[4].close_ref.is_none());

                assert!(s.used_backtracking);
            });
        }

        #[test]
        fn undo_expand3() {
            session(|| {
                // {!R(A), R(A)}, {!R(A), !R(B)}, {!R(A), !R(B)}, {!R(A), !R(A)}
                let s = state(2);
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(0, 0)).unwrap();
                let s = FOTableaux::apply_move(s, FOTabMove::Expand(2, 1)).unwrap();

                let s = FOTableaux::apply_move(s, FOTabMove::Undo).unwrap();

                assert_eq!(1, s.moves.len());
                assert!(s.used_backtracking);
                assert_eq!(3, s.nodes.len());
            });
        }
    }
}
