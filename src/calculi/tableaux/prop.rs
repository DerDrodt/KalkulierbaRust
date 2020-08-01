use std::fmt;

use super::TableauxType;
use crate::calculus::CloseMsg;
use crate::clause::{Atom, Clause, ClauseSet};
use crate::parse::clause_set::{parse_flexible, CNFStrategy};
use crate::parse::ParseErr;
use crate::Calculus;

pub type PropTabResult<T> = Result<T, PropTabError>;

impl From<ParseErr> for PropTabError {
    fn from(e: ParseErr) -> Self {
        PropTabError::ParseErr(e)
    }
}

#[derive(Debug, Eq, PartialEq)]
pub enum PropTabError {
    ParseErr(ParseErr),
    InvalidNodeId(usize),
    Backtracking,
    BacktrackingEmpty,
    IllegalMove,
}

pub struct PropTableauxParams {
    pub tab_type: TableauxType,
    pub regular: bool,
    pub backtracking: bool,
    pub cnf_strategy: CNFStrategy,
}

impl Default for PropTableauxParams {
    fn default() -> Self {
        PropTableauxParams {
            tab_type: TableauxType::Unconnected,
            regular: false,
            backtracking: false,
            cnf_strategy: CNFStrategy::Optimal,
        }
    }
}

#[derive(Debug)]
pub struct PropTableauxState {
    clause_set: ClauseSet<String>,
    ty: TableauxType,
    regular: bool,
    backtracking: bool,
    nodes: Vec<PropTabNode>,
    moves: Vec<PropTableauxMove>,
    used_backtracking: bool,
}

impl PropTableauxState {
    pub fn new(
        clause_set: ClauseSet<String>,
        ty: TableauxType,
        regular: bool,
        backtracking: bool,
    ) -> Self {
        Self {
            clause_set,
            ty,
            regular,
            backtracking,
            nodes: vec![PropTabNode::new(None, "true".to_string(), false, None)],
            moves: vec![],
            used_backtracking: false,
        }
    }

    pub fn root(&self) -> &PropTabNode {
        &self.nodes[0]
    }

    pub fn node(&self, id: usize) -> PropTabResult<&PropTabNode> {
        if let Some(node) = self.nodes.get(id) {
            Ok(node)
        } else {
            Err(PropTabError::InvalidNodeId(id))
        }
    }

    pub fn node_mut(&mut self, id: usize) -> PropTabResult<&mut PropTabNode> {
        if let Some(node) = self.nodes.get_mut(id) {
            Ok(node)
        } else {
            Err(PropTabError::InvalidNodeId(id))
        }
    }

    pub fn node_is_closable(&self, id: usize) -> PropTabResult<bool> {
        let node = self.nodes.get(id);
        if let Some(node) = node {
            todo!()
        } else {
            Err(PropTabError::InvalidNodeId(id))
        }
    }

    pub fn node_is_directly_closable(&self, id: usize) -> bool {
        todo!()
    }

    pub fn clause_expand_preprocessing<'c>(
        &self,
        clause: &'c Clause<String>,
    ) -> &'c Vec<Atom<String>> {
        &clause.atoms()
    }

    pub fn node_ancestry_contains_atom(
        &self,
        node_id: usize,
        atom: Atom<String>,
    ) -> PropTabResult<bool> {
        let node = self.nodes.get(node_id);
        if let Some(node) = node {
            todo!()
        } else {
            Err(PropTabError::InvalidNodeId(node_id))
        }
    }

    pub fn mark_node_closed<'a>(&'a mut self, leaf: usize) {
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
        self.nodes[leaf].is_closed
    }

    pub fn all_children_closed(&self, node_id: usize) -> bool {
        let node = &self.nodes[node_id];
        node.children
            .iter()
            .fold(true, |acc, e| acc && self.nodes[*e].is_closed())
    }

    pub fn get_close_msg(&self) -> CloseMsg {
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

    pub fn info(&self) -> String {
        let opts = format!(
            "{}|{}|{}|{}",
            self.ty, self.regular, self.backtracking, self.used_backtracking
        );
        let clause_set = self.clause_set.to_string();
        let nodes = {
            let mut ns = String::new();
            for (i, n) in self.nodes.iter().enumerate() {
                ns.push_str(&n.info());
                if i < self.nodes.len() - 1 {
                    ns.push_str("|");
                }
            }
            ns
        };
        let history = {
            let mut ms = String::new();
            for m in self.moves.iter() {
                ms.push_str(&m.to_string());
                ms.push_str(",");
            }
            ms
        };
        format!(
            "tableauxstate|{}|{}|[{}]|[{}]",
            opts, clause_set, nodes, history
        )
    }
}

#[derive(Debug)]
pub struct PropTabNode {
    parent: Option<usize>,
    spelling: String,
    negated: bool,
    lemma_source: Option<usize>,
    is_closed: bool,
    close_ref: Option<usize>,
    children: Vec<usize>,
}

impl PropTabNode {
    pub fn new(
        parent: Option<usize>,
        spelling: String,
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

    pub fn spelling(&self) -> &String {
        &self.spelling
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
            for c in self.children.iter() {
                cs.push_str(&c.to_string());
            }
            cs
        };

        format!(
            "{};{};{};{};{};{};({})",
            self.spelling, neg, parent, r#ref, leaf, closed, child_list
        )
    }
}

impl From<&PropTabNode> for Atom<String> {
    fn from(node: &PropTabNode) -> Self {
        Atom::new(node.spelling.clone(), node.negated)
    }
}

impl fmt::Display for PropTabNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}{}",
            if self.negated { "!" } else { "" },
            self.spelling
        )
    }
}

#[derive(Debug)]
pub enum PropTableauxMove {
    Expand(usize, usize),
    AutoClose(usize, usize),
    Lemma(usize, usize),
    Undo,
}

impl fmt::Display for PropTableauxMove {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PropTableauxMove::Expand(l, r) => write!(f, "{}({},{})", "Expand", l, r),
            PropTableauxMove::AutoClose(l, r) => write!(f, "{}({},{})", "AutoClose", l, r),
            PropTableauxMove::Lemma(l, r) => write!(f, "{}({},{})", "Lemma", l, r),
            PropTableauxMove::Undo => write!(f, "{}", "Undo"),
        }
    }
}

pub struct PropTableaux {}

impl Calculus for PropTableaux {
    type Params = PropTableauxParams;
    type State = PropTableauxState;
    type Move = PropTableauxMove;
    type Error = PropTabError;

    fn parse_formula(formula: &str, params: Option<Self::Params>) -> PropTabResult<Self::State> {
        let Self::Params {
            tab_type,
            backtracking,
            regular,
            cnf_strategy,
        } = params.unwrap_or_default();

        let clauses = parse_flexible(formula, cnf_strategy)?;
        Ok(PropTableauxState::new(
            clauses,
            tab_type,
            regular,
            backtracking,
        ))
    }

    fn apply_move(state: Self::State, k_move: Self::Move) -> PropTabResult<Self::State> {
        use PropTableauxMove::*;
        match k_move {
            Expand(leaf, clause) => apply_expand(state, leaf, clause),
            AutoClose(leaf, node) => apply_close(state, leaf, node),
            Lemma(leaf, lemma) => apply_lemma(state, leaf, lemma),
            Undo => apply_undo(state),
        }
    }

    fn check_close(state: Self::State) -> CloseMsg {
        state.get_close_msg()
    }

    fn validate(_state: Self::State) -> bool {
        true
    }
}

pub fn apply_expand(
    mut state: PropTableauxState,
    leaf_id: usize,
    clause_id: usize,
) -> PropTabResult<PropTableauxState> {
    // ensureExpandability(state, leafID, clauseID)

    let clause = &state.clause_set.clauses()[clause_id];
    let len = state.nodes.len();

    for (i, atom) in clause.atoms().iter().enumerate() {
        let new_leaf = PropTabNode::new(Some(leaf_id), atom.lit().clone(), atom.negated(), None);
        state.nodes.push(new_leaf);
        let leaf = &mut state.nodes[leaf_id];
        leaf.children.push(len + i);
    }

    // verifyExpandConnectedness(state, leafID)

    if state.backtracking {
        state
            .moves
            .push(PropTableauxMove::Expand(leaf_id, clause_id));
    }

    Ok(state)
}

pub fn apply_close(
    mut state: PropTableauxState,
    leaf_id: usize,
    node_id: usize,
) -> PropTabResult<PropTableauxState> {
    // ensure closability
    let leaf = state.node_mut(leaf_id)?;
    leaf.close_ref = Some(node_id);
    state.mark_node_closed(leaf_id);

    if state.backtracking {
        state
            .moves
            .push(PropTableauxMove::AutoClose(leaf_id, node_id));
    }

    Ok(state)
}

pub fn apply_lemma(
    state: PropTableauxState,
    leaf_id: usize,
    node_id: usize,
) -> PropTabResult<PropTableauxState> {
    todo!()
}

pub fn apply_undo(mut state: PropTableauxState) -> PropTabResult<PropTableauxState> {
    if !state.backtracking {
        return Err(PropTabError::Backtracking);
    }

    let mut history = state.moves;

    if history.is_empty() {
        return Err(PropTabError::BacktrackingEmpty);
    }

    let last = history.pop().unwrap();

    state.used_backtracking = true;
    state.moves = history;

    match last {
        PropTableauxMove::AutoClose(leaf, ..) => undo_close(state, leaf),
        PropTableauxMove::Expand(id1, _) | PropTableauxMove::Lemma(id1, _) => {
            undo_expand(state, id1)
        }
        _ => Err(PropTabError::IllegalMove),
    }
}

fn undo_close(mut state: PropTableauxState, leaf: usize) -> PropTabResult<PropTableauxState> {
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

fn undo_expand(mut state: PropTableauxState, leaf: usize) -> PropTabResult<PropTableauxState> {
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

#[cfg(test)]
mod tests {
    use super::{
        PropTabError, PropTableaux, PropTableauxMove, PropTableauxParams, PropTableauxState,
        TableauxType,
    };
    use crate::{parse::clause_set::CNFStrategy, Calculus};

    fn opts() -> PropTableauxParams {
        PropTableauxParams {
            tab_type: TableauxType::Unconnected,
            regular: false,
            backtracking: true,
            cnf_strategy: CNFStrategy::Optimal,
        }
    }

    #[test]
    fn undo_disabled() {
        let state = PropTableaux::parse_formula("a,b;c", None).unwrap();
        let res = PropTableaux::apply_move(state, PropTableauxMove::Undo).unwrap_err();

        assert_eq!(res, PropTabError::Backtracking);
    }

    #[test]
    fn undo_init() {
        let state = PropTableaux::parse_formula("a,b,c;d", Some(opts())).unwrap();
        let res = PropTableaux::apply_move(state, PropTableauxMove::Undo).unwrap_err();

        assert_eq!(res, PropTabError::BacktrackingEmpty);
    }

    #[test]
    fn undo_flag() {
        let mut state = PropTableaux::parse_formula("a,b,c;d", Some(opts())).unwrap();

        state = PropTableaux::apply_move(state, PropTableauxMove::Expand(0, 0)).unwrap();

        assert!(!state.used_backtracking);

        state = PropTableaux::apply_move(state, PropTableauxMove::Undo).unwrap();

        assert!(state.used_backtracking);

        state = PropTableaux::apply_move(state, PropTableauxMove::Expand(0, 0)).unwrap();

        assert!(state.used_backtracking);
    }

    #[test]
    fn undo_expand_simple() {
        let mut state = PropTableaux::parse_formula("a,b;c;!a", Some(opts())).unwrap();
        state.used_backtracking = true;

        let info = state.info();

        state = PropTableaux::apply_move(state, PropTableauxMove::Expand(0, 0)).unwrap();
        state = PropTableaux::apply_move(state, PropTableauxMove::Undo).unwrap();

        assert_eq!(info, state.info());
    }

    #[test]
    fn undo_close_simple() {
        let mut state = PropTableaux::parse_formula("a;!a", Some(opts())).unwrap();
        state.used_backtracking = true;

        state = PropTableaux::apply_move(state, PropTableauxMove::Expand(0, 0)).unwrap();
        state = PropTableaux::apply_move(state, PropTableauxMove::Expand(1, 1)).unwrap();

        let info = state.info();

        state = PropTableaux::apply_move(state, PropTableauxMove::AutoClose(2, 1)).unwrap();
        state = PropTableaux::apply_move(state, PropTableauxMove::Undo).unwrap();

        assert_eq!(info, state.info());
    }

    fn move_and_info(
        state: PropTableauxState,
        r#move: PropTableauxMove,
    ) -> (PropTableauxState, String) {
        let msg = r#move.to_string();
        let state = PropTableaux::apply_move(state, r#move).expect(&msg);
        let info = state.info();
        (state, info)
    }

    #[test]
    fn undo_complex() {
        let mut state = PropTableaux::parse_formula("a,b,c;!a;!b;!c", Some(opts())).unwrap();
        state.used_backtracking = true;

        let e6 = state.info();
        let (state, e5) = move_and_info(state, PropTableauxMove::Expand(0, 0));
        let (state, e4) = move_and_info(state, PropTableauxMove::Expand(1, 1));
        let (state, e3) = move_and_info(state, PropTableauxMove::Expand(4, 1));
        let (state, e2) = move_and_info(state, PropTableauxMove::Expand(3, 0));
        let (state, e1) = move_and_info(state, PropTableauxMove::Expand(5, 1));
        let (state, _) = move_and_info(state, PropTableauxMove::AutoClose(8, 5));

        let (state, s1) = move_and_info(state, PropTableauxMove::Undo);
        let (state, s2) = move_and_info(state, PropTableauxMove::Undo);
        let (state, s3) = move_and_info(state, PropTableauxMove::Undo);
        let (state, s4) = move_and_info(state, PropTableauxMove::Undo);
        let (state, s5) = move_and_info(state, PropTableauxMove::Undo);
        let (_, s6) = move_and_info(state, PropTableauxMove::Undo);

        assert_eq!(e1, s1);
        assert_eq!(e2, s2);
        assert_eq!(e3, s3);
        assert_eq!(e4, s4);
        assert_eq!(e5, s5);
        assert_eq!(e6, s6);
    }
}
