use std::{fmt, ops::Deref};

use serde::{
    de::{self, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{
    calculus::CloseMsg,
    logic::LogicNode,
    parse::{modal::parse_modal_formula, ParseErr},
    tamper_protect::ProtectedState,
    Calculus, SynEq,
};

#[derive(Debug, Clone)]
pub enum Err {
    Parse(ParseErr),
    Backtracking,
    BacktrackingEmpty,
    InvalidNodeId(usize),
    AlreadyClosed(usize),
    RuleNotApplicable(&'static str, &'static str),
    RuleNotApplicableSign {
        rule: &'static str,
        on: &'static str,
        sign: bool,
    },
    RuleCannotBeAppliedOn(&'static str, Node),
    PrefixNotInUse,
    PrefixAlreadyInUse,
    ExpectedParent(usize, usize),
    ExpectedOppositeSign,
    ExpectedSamePrefix,
    ExpectedSynEq,
}

impl From<ParseErr> for Err {
    fn from(value: ParseErr) -> Self {
        Self::Parse(value)
    }
}

impl fmt::Display for Err {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Err::Parse(e) => fmt::Display::fmt(e, f),
            Err::Backtracking => {
                write!(f, "Backtracking is not enabled for this proof")
            }
            Err::BacktrackingEmpty => write!(f, "Can't undo in initial state"),
            Err::InvalidNodeId(id) => write!(f, "Node with ID {id} does not exist"),
            Err::AlreadyClosed(id) => write!(f, "Node '{id}' is already closed"),
            Err::RuleNotApplicable(rule, on) => {
                write!(f, "{rule} rule can only be applied on a {on}")
            }
            Err::RuleNotApplicableSign { rule, on, sign } => write!(
                f,
                "{rule} rule can only be applied on {on} if the sign is {sign}"
            ),
            Err::RuleCannotBeAppliedOn(rule, node) => {
                write!(f, "{rule} rule can not be applied on the node '{node}'")
            }
            Err::PrefixNotInUse => {
                write!(f, "Prefix has to be already in use on the selected branch")
            }
            Err::PrefixAlreadyInUse => {
                write!(f, "Prefix is already in use on the selected branch")
            }
            Err::ExpectedParent(parent, node) => {
                write!(f, "Node '{parent}' is not an ancestor of node '{node}'")
            }
            Err::ExpectedOppositeSign => {
                write!(f, "The selected formulas are not of opposite sign")
            }
            Err::ExpectedSamePrefix => {
                write!(f, "The selected formulas do not have the same prefix")
            }
            Err::ExpectedSynEq => {
                write!(f, "The selected formulas are not syntactically equivalent")
            }
        }
    }
}

pub type SignedModalTabResult<T> = Result<T, Err>;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SignedModalTabParams {
    backtracking: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Move {
    Negation(usize, Option<usize>),
    Alpha(usize, Option<usize>),
    Beta(usize, Option<usize>),
    Nu(usize, usize, Option<usize>),
    Pi(usize, usize, Option<usize>),
    Prune(usize),
    Close(usize, usize),
    Undo,
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Move::Negation(node_id, _) => write!(f, "(negation|{node_id})"),
            Move::Alpha(node_id, _) => write!(f, "(alphaMove|{node_id})"),
            Move::Beta(node_id, _) => write!(f, "(betaMove|{node_id})"),
            Move::Nu(node_id, _, _) => write!(f, "(nuMove|{node_id})"),
            Move::Pi(node_id, _, _) => write!(f, "(piMove|{node_id})"),
            Move::Prune(node_id) => write!(f, "(prune|{node_id})"),
            Move::Close(node_id, leaf_id) => {
                write!(f, "(negation|{node_id}|{leaf_id})")
            }
            Move::Undo => write!(f, "(undo)"),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct State {
    formula: LogicNode,
    assumption: bool,
    backtracking: bool,
    nodes: Vec<Node>,
    moves: Vec<Move>,
    used_backtracking: bool,
    status_msg: Option<String>,
}

impl ProtectedState for State {
    fn compute_seal_info(&self) -> String {
        let nodes = self
            .nodes
            .iter()
            .map(Node::info)
            .collect::<Vec<_>>()
            .join(",");
        let moves = self
            .moves
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(",");
        format!(
            "signed-modal-tableaux|{}|{}|{}|{}|{}",
            self.backtracking, self.used_backtracking, self.formula, nodes, moves
        )
    }
}

impl State {
    pub fn new(formula: LogicNode, assumption: bool, backtracking: bool) -> Self {
        Self {
            formula: formula.clone(),
            assumption,
            backtracking,
            nodes: vec![Node::new(None, vec![1], assumption, formula)],
            moves: vec![],
            used_backtracking: false,
            status_msg: None,
        }
    }

    fn child_leaves_of(&self, node_id: usize) -> Vec<usize> {
        let mut wl = vec![node_id];
        let mut leaves = vec![];

        while let Some(id) = wl.pop() {
            let node = &self.nodes[id];
            for c in &node.children {
                wl.push(*c);
            }
            if node.is_leaf() {
                leaves.push(id);
            }
        }

        leaves
    }

    fn mark_node_closed(&mut self, node_id: usize) {
        let mut id = node_id;
        while id == node_id || self.all_children_closed(id) {
            let node = &mut self.nodes[id];
            node.mark_closed();
            if node.parent().is_none() {
                break;
            }
            id = node.parent.unwrap();
        }
        let node = &self.nodes[node_id];
        if !node.is_leaf() {}
    }

    fn all_children_closed(&self, node_id: usize) -> bool {
        let node = &self.nodes[node_id];
        node.children.iter().all(|e| self.nodes[*e].is_closed())
    }

    fn prefix_is_used_on_branch(&self, leaf_id: usize, prefix: &[usize]) -> bool {
        let mut node = &self.nodes[leaf_id];
        if prefix == node.prefix {
            return true;
        }

        while let Some(parent) = node.parent {
            node = &self.nodes[parent];
            if prefix == node.prefix {
                return true;
            }
        }

        false
    }

    fn add_child(&mut self, parent_id: usize, child: Node) {
        self.nodes.push(child);
        let len = self.nodes.len();
        self.nodes[parent_id].children.push(len - 1);
    }

    fn node_is_parent_of(&self, parent_id: usize, child_id: usize) -> bool {
        let child = &self.nodes[child_id];
        if child.parent.map(|p| p == parent_id).unwrap_or(false) {
            return true;
        }
        match child.parent {
            Some(0) | None => false,
            Some(p) => self.node_is_parent_of(parent_id, p),
        }
    }

    fn get_close_msg(&self) -> CloseMsg {
        let closed = self.nodes[0].is_closed;
        let msg = if closed && self.used_backtracking {
            "The proof is closed and valid in signed modal-logic tableaux with backtracking"
        } else if closed && !self.used_backtracking {
            "The proof is closed and valid in signed modal-logic tableaux without backtracking"
        } else {
            "The proof tree is not closed"
        }
        .to_string();
        CloseMsg { msg, closed }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "camelCase")]
pub struct Node {
    parent: Option<usize>,
    prefix: Vec<usize>,
    sign: bool,
    formula: LogicNode,
    is_closed: bool,
    close_ref: Option<usize>,
    children: Vec<usize>,
}

impl Node {
    pub fn new(parent: Option<usize>, prefix: Vec<usize>, sign: bool, formula: LogicNode) -> Self {
        Self {
            parent,
            prefix,
            sign,
            formula,
            is_closed: false,
            close_ref: None,
            children: vec![],
        }
    }

    pub fn spelling(&self) -> String {
        self.formula.to_string()
    }

    fn mark_closed(&mut self) {
        self.is_closed = true
    }

    fn parent(&self) -> Option<usize> {
        self.parent
    }

    fn is_closed(&self) -> bool {
        self.is_closed
    }

    fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }

    fn info(&self) -> String {
        let parent = if let Some(p) = self.parent {
            p.to_string()
        } else {
            "null".to_string()
        };
        let children = self
            .children
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(",");
        let is_closed = self.is_closed;
        let close_ref = if let Some(r) = self.close_ref {
            r.to_string()
        } else {
            "null".to_string()
        };
        let formula = &self.formula;
        format!("({parent}|{children}|{is_closed}|{close_ref}|{formula})")
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pre = self
            .prefix
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(".");
        let sign = if self.sign { "True" } else { "False" };
        write!(f, "{pre} {sign} {}", self.formula)
    }
}

pub struct SignedModalTableaux;

impl<'f> Calculus<'f> for SignedModalTableaux {
    type Params = SignedModalTabParams;

    type State = State;

    type Move = Move;

    type Error = Err;

    fn parse_formula(
        formula: &'f str,
        params: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        let (assumption, node) = parse_modal_formula(formula)?;
        Ok(State::new(
            node,
            assumption,
            params.map(|p| p.backtracking).unwrap_or(true),
        ))
    }

    fn apply_move(mut state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        state.status_msg = None;
        match k_move {
            Move::Negation(node_id, leaf_id) => apply_negation(state, node_id, leaf_id),
            Move::Alpha(node_id, leaf_id) => apply_alpha(state, node_id, leaf_id),
            Move::Beta(node_id, leaf_id) => apply_beta(state, node_id, leaf_id),
            Move::Nu(prefix, node_id, leaf_id) => apply_nu(state, prefix, node_id, leaf_id),
            Move::Pi(prefix, node_id, leaf_id) => apply_pi(state, prefix, node_id, leaf_id),
            Move::Prune(node_id) => apply_prune(state, node_id),
            Move::Close(node_id, leaf_id) => apply_close(state, node_id, leaf_id),
            Move::Undo => apply_undo(state),
        }
    }

    fn check_close(state: Self::State) -> crate::calculus::CloseMsg {
        state.get_close_msg()
    }
}

fn apply_negation(
    mut state: State,
    node_id: usize,
    leaf_id: Option<usize>,
) -> SignedModalTabResult<State> {
    if let Some(leaf_id) = leaf_id {
        check_node_restrctions(&state, node_id)?;

        let node = &state.nodes[node_id];
        match &node.formula {
            LogicNode::Not(child) => {
                state.add_child(
                    leaf_id,
                    Node::new(
                        Some(leaf_id),
                        node.prefix.clone(),
                        !node.sign,
                        child.deref().clone(),
                    ),
                );

                if state.backtracking {
                    state.moves.push(Move::Negation(node_id, Some(leaf_id)));
                }
                Ok(state)
            }
            _ => Err(Err::RuleNotApplicable("negation", "negation")),
        }
    } else {
        for l in state.child_leaves_of(node_id) {
            state = apply_negation(state, node_id, Some(l))?;
        }
        Ok(state)
    }
}

fn apply_alpha(
    mut state: State,
    node_id: usize,
    leaf_id: Option<usize>,
) -> SignedModalTabResult<State> {
    if let Some(leaf_id) = leaf_id {
        check_node_restrctions(&state, node_id)?;

        let node = &state.nodes[node_id];

        let (a1, a2) = match &node.formula {
            LogicNode::And(c1, c2) => {
                if !node.sign {
                    return Err(Err::RuleNotApplicableSign {
                        rule: "alpha",
                        on: "a conjunction",
                        sign: true,
                    });
                }
                (
                    Node::new(Some(leaf_id), node.prefix.clone(), true, c1.deref().clone()),
                    Node::new(
                        Some(state.nodes.len()),
                        node.prefix.clone(),
                        true,
                        c2.deref().clone(),
                    ),
                )
            }
            LogicNode::Or(c1, c2) => {
                if node.sign {
                    return Err(Err::RuleNotApplicableSign {
                        rule: "alpha",
                        on: "a disjunction",
                        sign: false,
                    });
                }
                (
                    Node::new(
                        Some(leaf_id),
                        node.prefix.clone(),
                        false,
                        c1.deref().clone(),
                    ),
                    Node::new(
                        Some(state.nodes.len()),
                        node.prefix.clone(),
                        false,
                        c2.deref().clone(),
                    ),
                )
            }
            LogicNode::Impl(c1, c2) => {
                if node.sign {
                    return Err(Err::RuleNotApplicableSign {
                        rule: "alpha",
                        on: "an implication",
                        sign: false,
                    });
                }
                (
                    Node::new(Some(leaf_id), node.prefix.clone(), true, c1.deref().clone()),
                    Node::new(
                        Some(state.nodes.len()),
                        node.prefix.clone(),
                        false,
                        c2.deref().clone(),
                    ),
                )
            }
            _ => return Err(Err::RuleCannotBeAppliedOn("alpha", node.clone())),
        };

        state.add_child(leaf_id, a1);
        state.add_child(state.nodes.len() - 1, a2);

        if state.backtracking {
            state.moves.push(Move::Alpha(node_id, Some(leaf_id)));
        }

        Ok(state)
    } else {
        for l in state.child_leaves_of(node_id) {
            state = apply_alpha(state, node_id, Some(l))?;
        }
        Ok(state)
    }
}

fn apply_beta(
    mut state: State,
    node_id: usize,
    leaf_id: Option<usize>,
) -> SignedModalTabResult<State> {
    if let Some(leaf_id) = leaf_id {
        check_node_restrctions(&state, node_id)?;

        let node = &state.nodes[node_id];

        let (b1, b2) = match &node.formula {
            LogicNode::And(c1, c2) => {
                if node.sign {
                    return Err(Err::RuleNotApplicableSign {
                        rule: "beta",
                        on: "a conjunction",
                        sign: false,
                    });
                }
                (
                    Node::new(
                        Some(leaf_id),
                        node.prefix.clone(),
                        false,
                        c1.deref().clone(),
                    ),
                    Node::new(
                        Some(leaf_id),
                        node.prefix.clone(),
                        false,
                        c2.deref().clone(),
                    ),
                )
            }
            LogicNode::Or(c1, c2) => {
                if !node.sign {
                    return Err(Err::RuleNotApplicableSign {
                        rule: "beta",
                        on: "a disjunction",
                        sign: true,
                    });
                }
                (
                    Node::new(Some(leaf_id), node.prefix.clone(), true, c1.deref().clone()),
                    Node::new(Some(leaf_id), node.prefix.clone(), true, c2.deref().clone()),
                )
            }
            LogicNode::Impl(c1, c2) => {
                if !node.sign {
                    return Err(Err::RuleNotApplicableSign {
                        rule: "beta",
                        on: "an implication",
                        sign: true,
                    });
                }
                (
                    Node::new(
                        Some(leaf_id),
                        node.prefix.clone(),
                        false,
                        c1.deref().clone(),
                    ),
                    Node::new(Some(leaf_id), node.prefix.clone(), true, c2.deref().clone()),
                )
            }
            _ => return Err(Err::RuleCannotBeAppliedOn("beta", node.clone())),
        };

        state.add_child(leaf_id, b1);
        state.add_child(leaf_id, b2);

        if state.backtracking {
            state.moves.push(Move::Beta(node_id, Some(leaf_id)));
        }

        Ok(state)
    } else {
        for l in state.child_leaves_of(node_id) {
            state = apply_beta(state, node_id, Some(l))?;
        }
        Ok(state)
    }
}

fn apply_nu(
    mut state: State,
    prefix: usize,
    node_id: usize,
    leaf_id: Option<usize>,
) -> SignedModalTabResult<State> {
    if let Some(leaf_id) = leaf_id {
        check_node_restrctions(&state, node_id)?;

        let node = &state.nodes[node_id];

        let mut np = node.prefix.clone();
        np.push(prefix);

        if !state.prefix_is_used_on_branch(leaf_id, &np) {
            return Err(Err::PrefixNotInUse);
        }

        // Check if the node is T Box ( [] ) or F DIAMOND ( <> ) : only then can be NU move applied
        let n = match (node.sign, &node.formula) {
            (true, LogicNode::Box(c)) => Node::new(Some(leaf_id), np, true, c.deref().clone()),
            (false, LogicNode::Box(_)) => {
                return Err(Err::RuleNotApplicableSign {
                    rule: "nu",
                    on: "BOX",
                    sign: true,
                })
            }
            (true, LogicNode::Diamond(_)) => {
                return Err(Err::RuleNotApplicableSign {
                    rule: "nu",
                    on: "DIAMOND",
                    sign: false,
                })
            }
            (false, LogicNode::Diamond(c)) => {
                Node::new(Some(leaf_id), np, false, c.deref().clone())
            }
            _ => return Err(Err::RuleCannotBeAppliedOn("nu", node.clone())),
        };

        state.add_child(leaf_id, n);

        if state.backtracking {
            state.moves.push(Move::Nu(prefix, node_id, Some(leaf_id)));
        }

        Ok(state)
    } else {
        for l in state.child_leaves_of(node_id) {
            state = apply_nu(state, prefix, node_id, Some(l))?;
        }
        Ok(state)
    }
}

fn apply_pi(
    mut state: State,
    prefix: usize,
    node_id: usize,
    leaf_id: Option<usize>,
) -> SignedModalTabResult<State> {
    if let Some(leaf_id) = leaf_id {
        check_node_restrctions(&state, node_id)?;

        let node = &state.nodes[node_id];

        let mut np = node.prefix.clone();
        np.push(prefix);

        if state.prefix_is_used_on_branch(leaf_id, &np) {
            return Err(Err::PrefixAlreadyInUse);
        }

        // Check if the node is F Box ( [] ) or T DIAMOND ( <> ) : only then can be NU move applied
        let n = match (node.sign, &node.formula) {
            (false, LogicNode::Box(c)) => Node::new(Some(leaf_id), np, false, c.deref().clone()),
            (true, LogicNode::Box(_)) => {
                return Err(Err::RuleNotApplicableSign {
                    rule: "pi",
                    on: "BOX",
                    sign: false,
                })
            }
            (false, LogicNode::Diamond(_)) => {
                return Err(Err::RuleNotApplicableSign {
                    rule: "pi",
                    on: "DIAMOND",
                    sign: true,
                })
            }
            (true, LogicNode::Diamond(c)) => Node::new(Some(leaf_id), np, true, c.deref().clone()),
            _ => return Err(Err::RuleCannotBeAppliedOn("pi", node.clone())),
        };

        state.add_child(leaf_id, n);

        if state.backtracking {
            state.moves.push(Move::Pi(prefix, node_id, Some(leaf_id)));
        }

        Ok(state)
    } else {
        for l in state.child_leaves_of(node_id) {
            state = apply_pi(state, prefix, node_id, Some(l))?;
        }
        Ok(state)
    }
}

fn apply_prune(mut state: State, node_id: usize) -> SignedModalTabResult<State> {
    if !state.backtracking {
        return Err(Err::Backtracking);
    }

    state.moves.push(Move::Prune(node_id));

    if node_id >= state.nodes.len() {
        return Err(Err::InvalidNodeId(node_id));
    }

    let n = &state.nodes[node_id];

    // Collect all transitive children of the node
    // (not deleting anything yet to keep index structures intact)
    let mut q = vec![];
    let mut to_del = vec![];
    for c in &n.children {
        q.push(*c);
    }

    while let Some(idx) = q.first() {
        let idx = *idx;
        q.remove(0);

        let n = &state.nodes[idx];
        for c in &n.children {
            q.push(*c);
        }
        to_del.push(idx)
    }

    // Remove each identified child, keeping parent references but not children references
    // We remove items from the largest index to the smallest to keep the indices of the other
    // items in the list consistent

    to_del.sort_unstable();
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

fn apply_close(mut state: State, node_id: usize, leaf_id: usize) -> SignedModalTabResult<State> {
    check_close_id_restrictions(&state, node_id, leaf_id)?;

    let node = &state.nodes[node_id];
    let leaf = &state.nodes[leaf_id];

    if node.sign == leaf.sign {
        return Err(Err::ExpectedOppositeSign);
    }

    if node.prefix != leaf.prefix {
        return Err(Err::ExpectedSamePrefix);
    }

    if !node.formula.syn_eq(&leaf.formula) {
        return Err(Err::ExpectedSynEq);
    }

    state.nodes[leaf_id].close_ref = Some(node_id);
    state.mark_node_closed(leaf_id);

    if state.backtracking {
        state.moves.push(Move::Close(node_id, leaf_id));
    }

    Ok(state)
}

fn apply_undo(mut state: State) -> SignedModalTabResult<State> {
    if !state.backtracking {
        return Err(Err::Backtracking);
    }
    if state.moves.is_empty() {
        return Err(Err::BacktrackingEmpty);
    }
    state.moves.pop();

    let mut ns = State::new(state.formula, state.assumption, state.backtracking);
    ns.used_backtracking = true;

    for m in state.moves {
        ns = SignedModalTableaux::apply_move(ns, m)?;
    }

    Ok(ns)
}

fn check_close_id_restrictions(
    state: &State,
    node_id: usize,
    leaf_id: usize,
) -> SignedModalTabResult<()> {
    check_node_restrctions(state, node_id)?;
    check_valid_node_id(state, leaf_id)?;

    if !state.node_is_parent_of(node_id, leaf_id) {
        return Err(Err::ExpectedParent(node_id, leaf_id));
    }

    Ok(())
}

#[inline]
fn check_valid_node_id(state: &State, node_id: usize) -> SignedModalTabResult<()> {
    if node_id >= state.nodes.len() {
        return Err(Err::InvalidNodeId(node_id));
    }

    Ok(())
}

#[inline]
fn check_node_restrctions(state: &State, node_id: usize) -> SignedModalTabResult<()> {
    check_valid_node_id(state, node_id)?;
    if state.nodes[node_id].is_closed {
        return Err(Err::AlreadyClosed(node_id));
    }

    Ok(())
}

impl Serialize for Move {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let num_fields = match self {
            Self::Nu(..) | Self::Pi(..) => 4,
            Self::Negation(..) | Self::Alpha(..) | Self::Beta(..) | Self::Close(..) => 3,
            Self::Prune(..) => 2,
            Self::Undo => 1,
        };
        let mut state = serializer.serialize_struct("SignedModalTabMove", num_fields)?;
        let ty = match self {
            Self::Negation(..) => "negation",
            Self::Alpha(_, _) => "alphaMove",
            Self::Beta(_, _) => "betaMove",
            Self::Nu(_, _, _) => "nuMove",
            Self::Pi(_, _, _) => "piMove",
            Self::Prune(_) => "prune",
            Self::Close(_, _) => "close",
            Self::Undo => "undo",
        };
        state.serialize_field("type", ty)?;
        match self {
            Self::Negation(n, l) | Self::Alpha(n, l) | Self::Beta(n, l) => {
                state.serialize_field("nodeID", n)?;
                state.serialize_field("leafID", l)?;
            }
            Self::Nu(p, n, l) | Self::Pi(p, n, l) => {
                state.serialize_field("prefix", p)?;
                state.serialize_field("nodeID", n)?;
                state.serialize_field("leafID", l)?;
            }
            Self::Prune(n) => {
                state.serialize_field("nodeID", n)?;
            }
            Self::Close(n, l) => {
                state.serialize_field("nodeID", n)?;
                state.serialize_field("leafID", l)?;
            }
            Self::Undo => {}
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
            #[serde(rename = "nodeID")]
            NodeId,
            #[serde(rename = "leafID")]
            LeafId,
            #[serde(rename = "prefix")]
            Prefix,
        }

        struct MoveVisitor;

        impl<'de> Visitor<'de> for MoveVisitor {
            type Value = Move;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct SignedModalTabMove")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: serde::de::MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut node_id: Option<usize> = None;
                let mut leaf_id: Option<usize> = None;
                let mut prefix: Option<usize> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Ty => {
                            if ty.is_some() {
                                return Err(de::Error::duplicate_field("type"));
                            }
                            ty = Some(map.next_value()?);
                        }
                        Field::NodeId => {
                            if node_id.is_some() {
                                return Err(de::Error::duplicate_field("nodeID"));
                            }
                            node_id = Some(map.next_value()?);
                        }
                        Field::LeafId => {
                            if leaf_id.is_some() {
                                return Err(de::Error::duplicate_field("leafID"));
                            }
                            leaf_id = Some(map.next_value()?);
                        }
                        Field::Prefix => {
                            if prefix.is_some() {
                                return Err(de::Error::duplicate_field("prefix"));
                            }
                            prefix = Some(map.next_value()?);
                        }
                    }
                }

                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                if ty == "undo" {
                    return Ok(Move::Undo);
                }
                let node_id = node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?;
                if ty == "prune" {
                    return Ok(Move::Prune(node_id));
                }
                if ty == "close" {
                    let leaf_id = leaf_id.ok_or_else(|| de::Error::missing_field("leafID"))?;
                    return Ok(Move::Close(node_id, leaf_id));
                }
                let ty: &str = &ty;
                let m = match ty {
                    "negation" => Move::Negation(node_id, leaf_id),
                    "alphaMove" => Move::Alpha(node_id, leaf_id),
                    "betaMove" => Move::Beta(node_id, leaf_id),
                    "nuMove" => {
                        let prefix = prefix.ok_or_else(|| de::Error::missing_field("prefix"))?;
                        Move::Nu(prefix, node_id, leaf_id)
                    }
                    "piMove" => {
                        let prefix = prefix.ok_or_else(|| de::Error::missing_field("prefix"))?;
                        Move::Pi(prefix, node_id, leaf_id)
                    }
                    _ => {
                        return Err(de::Error::invalid_value(
                            de::Unexpected::Str(ty),
                            &"Valid move type",
                        ))
                    }
                };
                Ok(m)
            }
        }

        const FIELDS: &[&str] = &["type", "nodeID", "leafID", "prefix"];
        deserializer.deserialize_struct("SignedModalTabMove", FIELDS, MoveVisitor)
    }
}

impl Serialize for State {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("SignedModalTabState", 8)?;
        state.serialize_field("formula", &self.formula)?;
        state.serialize_field("assumption", &self.assumption)?;
        state.serialize_field("backtracking", &self.backtracking)?;
        state.serialize_field("tree", &self.nodes)?;
        state.serialize_field("moveHistory", &self.moves)?;
        state.serialize_field("usedBacktracking", &self.used_backtracking)?;
        state.serialize_field("statusMessage", &self.status_msg)?;
        state.serialize_field("seal", &self.compute_seal_info())?;

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
            #[serde(rename = "formula")]
            Formula,
            #[serde(rename = "assumption")]
            Assumption,
            #[serde(rename = "backtracking")]
            Backtracking,
            #[serde(rename = "tree")]
            Nodes,
            #[serde(rename = "moveHistory")]
            Moves,
            #[serde(rename = "usedBacktracking")]
            UsedBacktracking,
            #[serde(rename = "statusMessage")]
            StatusMessage,
            #[serde(rename = "seal")]
            Seal,
        }

        struct StateVisitor;

        impl<'de> Visitor<'de> for StateVisitor {
            type Value = State;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct SignedModalTabState")
            }

            fn visit_map<A>(self, mut map: A) -> Result<Self::Value, A::Error>
            where
                A: de::MapAccess<'de>,
            {
                let mut formula = None;
                let mut assumption = None;
                let mut backtracking = None;
                let mut nodes = None;
                let mut moves = None;
                let mut used_backtracking = None;
                let mut status_msg = None;
                let mut seal = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Formula => {
                            if formula.is_some() {
                                return Err(de::Error::duplicate_field("formula"));
                            }
                            formula = Some(map.next_value()?);
                        }
                        Field::Assumption => {
                            if assumption.is_some() {
                                return Err(de::Error::duplicate_field("assumption"));
                            }
                            assumption = Some(map.next_value()?);
                        }
                        Field::Backtracking => {
                            if backtracking.is_some() {
                                return Err(de::Error::duplicate_field("backtracking"));
                            }
                            backtracking = Some(map.next_value()?);
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
                        Field::StatusMessage => {
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

                let formula = formula.ok_or_else(|| de::Error::missing_field("formula"))?;
                let assumption =
                    assumption.ok_or_else(|| de::Error::missing_field("assumption"))?;
                let backtracking =
                    backtracking.ok_or_else(|| de::Error::missing_field("backtracking"))?;
                let nodes = nodes.ok_or_else(|| de::Error::missing_field("tree"))?;
                let moves = moves.ok_or_else(|| de::Error::missing_field("moveHistory"))?;
                let used_backtracking = used_backtracking
                    .ok_or_else(|| de::Error::missing_field("usedBacktracking"))?;
                let status_msg =
                    status_msg.ok_or_else(|| de::Error::missing_field("statusMessage"))?;
                let seal: String = seal.ok_or_else(|| de::Error::missing_field("seal"))?;

                let s = State {
                    formula,
                    assumption,
                    backtracking,
                    nodes,
                    moves,
                    used_backtracking,
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
            "formula",
            "assumption",
            "backtracking",
            "tree",
            "moveHistory",
            "usedBacktracking",
            "statusMessage",
            "seal",
        ];
        deserializer.deserialize_struct("SignedModalTabState", FIELDS, StateVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session;

    mod alpha {
        use super::*;

        #[test]
        fn basic_and() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(a & b)", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(1, None)).unwrap();

                let s2 = SignedModalTableaux::apply_move(
                    SignedModalTableaux::parse_formula("!a", None).unwrap(),
                    Move::Negation(0, None),
                )
                .unwrap();
                let s3 = SignedModalTableaux::apply_move(
                    SignedModalTableaux::parse_formula("!b", None).unwrap(),
                    Move::Negation(0, None),
                )
                .unwrap();

                assert_eq!(1, s.nodes[1].children.len());
                assert!(s.nodes[2].sign);
                assert!(s.nodes[3].sign);
                assert!(s.nodes[2].formula.syn_eq(&s2.nodes[1].formula));
                assert!(s.nodes[3].formula.syn_eq(&s3.nodes[1].formula));
            })
        }

        #[test]
        fn wrong_and() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("(a & b)", None).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Alpha(0, None));
                assert!(r.is_err())
            })
        }

        #[test]
        fn basic_or() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("a | b", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();

                let f1 = parse_modal_formula("a").unwrap().1;
                let f2 = parse_modal_formula("b").unwrap().1;

                assert_eq!(1, s.nodes[0].children.len());
                assert!(!s.nodes[1].sign);
                assert!(!s.nodes[2].sign);
                assert!(s.nodes[1].formula.syn_eq(&f1));
                assert!(s.nodes[2].formula.syn_eq(&f2));
            })
        }

        #[test]
        fn wrong_or() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(a | b)", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(0, None)).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Alpha(1, None));
                assert!(r.is_err())
            })
        }

        #[test]
        fn basic_impl() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("a -> b", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();

                let f1 = parse_modal_formula("a").unwrap().1;
                let f2 = parse_modal_formula("b").unwrap().1;

                assert_eq!(1, s.nodes[0].children.len());
                assert!(s.nodes[1].sign);
                assert!(!s.nodes[2].sign);
                assert!(s.nodes[1].formula.syn_eq(&f1));
                assert!(s.nodes[2].formula.syn_eq(&f2));
            })
        }

        #[test]
        fn wrong_impl() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(a -> b)", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(0, None)).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Alpha(1, None));
                assert!(r.is_err())
            })
        }
    }

    mod beta {
        use super::*;

        #[test]
        fn basic_or() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(a | b)", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Beta(1, None)).unwrap();

                let s2 = SignedModalTableaux::apply_move(
                    SignedModalTableaux::parse_formula("!a", None).unwrap(),
                    Move::Negation(0, None),
                )
                .unwrap();
                let s3 = SignedModalTableaux::apply_move(
                    SignedModalTableaux::parse_formula("!b", None).unwrap(),
                    Move::Negation(0, None),
                )
                .unwrap();

                assert_eq!(2, s.nodes[1].children.len());
                assert!(s.nodes[2].sign);
                assert!(s.nodes[3].sign);
                assert!(s.nodes[2].formula.syn_eq(&s2.nodes[1].formula));
                assert!(s.nodes[3].formula.syn_eq(&s3.nodes[1].formula));
            })
        }

        #[test]
        fn wrong_or() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("(a | b)", None).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Beta(0, None));
                assert!(r.is_err())
            })
        }

        #[test]
        fn basic_and() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("a & b", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Beta(0, None)).unwrap();

                let f1 = parse_modal_formula("a").unwrap().1;
                let f2 = parse_modal_formula("b").unwrap().1;

                assert_eq!(2, s.nodes[0].children.len());
                assert!(!s.nodes[1].sign);
                assert!(!s.nodes[2].sign);
                assert!(s.nodes[1].formula.syn_eq(&f1));
                assert!(s.nodes[2].formula.syn_eq(&f2));
            })
        }

        #[test]
        fn wrong_and() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(a & b)", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(0, None)).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Beta(1, None));
                assert!(r.is_err())
            })
        }

        #[test]
        fn basic_impl() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign T: a -> b", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Beta(0, None)).unwrap();

                let f1 = parse_modal_formula("a").unwrap().1;
                let f2 = parse_modal_formula("b").unwrap().1;

                assert_eq!(2, s.nodes[0].children.len());
                assert!(!s.nodes[1].sign);
                assert!(s.nodes[2].sign);
                assert!(s.nodes[1].formula.syn_eq(&f1));
                assert!(s.nodes[2].formula.syn_eq(&f2));
            })
        }

        #[test]
        fn wrong_impl() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("a -> b", None).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Beta(0, None));
                assert!(r.is_err())
            })
        }
    }

    mod close {
        use super::*;

        #[test]
        fn complex() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(<>(!a)) -> []a", None).unwrap();

                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(1, None)).unwrap();
                let str = s.compute_seal_info();
                println!("{str}");
                let s = SignedModalTableaux::apply_move(s, Move::Pi(1, 2, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Nu(1, 3, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(5, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Close(4, 6)).unwrap();

                for n in s.nodes {
                    assert!(n.is_closed);
                }
            })
        }
    }

    mod negation {
        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(!a)", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(1, None)).unwrap();

                let f1 = parse_modal_formula("!a").unwrap().1;
                let f2 = parse_modal_formula("a").unwrap().1;

                assert!(
                    s.nodes[1].formula.syn_eq(&f1),
                    "{} != {}",
                    s.nodes[1].formula,
                    f1
                );
                assert!(s.nodes[2].formula.syn_eq(&f2));
            })
        }

        #[test]
        fn complex() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(a | b)", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Beta(1, None)).unwrap();

                let f = parse_modal_formula("a | b").unwrap().1;
                let s1 =
                    SignedModalTableaux::apply_move(s.clone(), Move::Negation(0, Some(2))).unwrap();

                assert!(s1.nodes[4].formula.syn_eq(&f));
                let s2 = SignedModalTableaux::apply_move(s, Move::Negation(0, Some(3))).unwrap();
                assert!(s2.nodes[4].formula.syn_eq(&f));
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("a & b", None).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Negation(0, None));
                assert!(r.is_err())
            })
        }
    }

    mod nu {
        use super::*;

        #[test]
        fn basic_box() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign T: <>a & []a", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Pi(1, 1, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Nu(1, 2, None)).unwrap();

                let f = parse_modal_formula("a").unwrap().1;

                assert!(s.nodes[4].formula.syn_eq(&f));
                assert_eq!(vec![1, 1], s.nodes[4].prefix);
            })
        }

        #[test]
        fn basic_diamond() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign F: []a | <>a", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Pi(1, 1, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Nu(1, 2, None)).unwrap();

                let f = parse_modal_formula("a").unwrap().1;

                assert!(s.nodes[4].formula.syn_eq(&f));
                assert_eq!(vec![1, 1], s.nodes[4].prefix);
            })
        }

        #[test]
        fn wrong_sign_box() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign F: []a | []a", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Pi(1, 1, None)).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Nu(1, 2, None));

                assert!(r.is_err())
            })
        }

        #[test]
        fn wrong_sign_diamond() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign T: <>a & <>a", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Pi(1, 1, None)).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Nu(1, 2, None));

                assert!(r.is_err())
            })
        }
    }

    mod pi {
        use super::*;

        #[test]
        fn basic_box() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign F: []a", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Pi(2, 0, None)).unwrap();

                let f = parse_modal_formula("a").unwrap().1;

                assert!(s.nodes[1].formula.syn_eq(&f));
                assert_eq!(vec![1, 2], s.nodes[1].prefix);
            })
        }

        #[test]
        fn basic_diamond() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign T: <>a", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Pi(1, 0, None)).unwrap();

                let f = parse_modal_formula("a").unwrap().1;

                assert!(s.nodes[1].formula.syn_eq(&f));
                assert_eq!(vec![1, 1], s.nodes[1].prefix);
            })
        }

        #[test]
        fn wrong_sign_box() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign T: []a", None).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Pi(1, 0, None));

                assert!(r.is_err())
            })
        }

        #[test]
        fn wrong_sign_diamond() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign F: <>a", None).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Pi(1, 0, None));

                assert!(r.is_err())
            })
        }
    }

    mod prune {
        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign T: a & (b & c)", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Prune(0)).unwrap();
                assert_eq!(1, s.nodes.len())
            })
        }

        #[test]
        fn complex() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("\\sign T: a & (b | c)", None).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Beta(2, None)).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Alpha(0, Some(3))).unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Prune(3)).unwrap();

                assert_eq!(5, s.nodes.len())
            })
        }

        #[test]
        fn wrong() {
            session(|| {
                let s = SignedModalTableaux::parse_formula(
                    "!(a -> b)",
                    Some(SignedModalTabParams {
                        backtracking: false,
                    }),
                )
                .unwrap();
                let s = SignedModalTableaux::apply_move(s, Move::Negation(0, None)).unwrap();
                let r = SignedModalTableaux::apply_move(s, Move::Prune(0));
                assert!(r.is_err())
            })
        }

        #[test]
        fn nothing_to_prune() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(a -> b)", None).unwrap();
                let _r = SignedModalTableaux::apply_move(s, Move::Prune(0)).unwrap();
            })
        }
    }

    mod undo {
        use super::*;

        #[test]
        fn complex() {
            session(|| {
                let s1 = SignedModalTableaux::parse_formula("!(<>(!a)) -> []a", None).unwrap();
                let mut s2 = SignedModalTableaux::parse_formula("!(<>(!a)) -> []a", None).unwrap();
                s2.used_backtracking = true;

                let h0 = s2.compute_seal_info();

                let s1 = SignedModalTableaux::apply_move(s1, Move::Alpha(0, None)).unwrap();
                let s2 = SignedModalTableaux::apply_move(s2, Move::Alpha(0, None)).unwrap();
                let h1 = s2.compute_seal_info();

                let s1 = SignedModalTableaux::apply_move(s1, Move::Negation(1, None)).unwrap();
                let s2 = SignedModalTableaux::apply_move(s2, Move::Negation(1, None)).unwrap();
                let h2 = s2.compute_seal_info();

                let s1 = SignedModalTableaux::apply_move(s1, Move::Pi(1, 2, None)).unwrap();
                let s2 = SignedModalTableaux::apply_move(s2, Move::Pi(1, 2, None)).unwrap();
                let h3 = s2.compute_seal_info();

                let s1 = SignedModalTableaux::apply_move(s1, Move::Nu(1, 3, None)).unwrap();
                let s2 = SignedModalTableaux::apply_move(s2, Move::Nu(1, 3, None)).unwrap();
                let h4 = s2.compute_seal_info();

                let s1 = SignedModalTableaux::apply_move(s1, Move::Negation(5, None)).unwrap();

                let s1 = SignedModalTableaux::apply_move(s1, Move::Undo).unwrap();
                assert_eq!(h4, s1.compute_seal_info());

                let s1 = SignedModalTableaux::apply_move(s1, Move::Undo).unwrap();
                assert_eq!(h3, s1.compute_seal_info());

                let s1 = SignedModalTableaux::apply_move(s1, Move::Undo).unwrap();
                assert_eq!(h2, s1.compute_seal_info());

                let s1 = SignedModalTableaux::apply_move(s1, Move::Undo).unwrap();
                assert_eq!(h1, s1.compute_seal_info());

                let s1 = SignedModalTableaux::apply_move(s1, Move::Undo).unwrap();
                assert_eq!(h0, s1.compute_seal_info());
            })
        }

        #[test]
        fn undo_two_children() {
            session(|| {
                let s1 = SignedModalTableaux::parse_formula("a & b", None).unwrap();
                let mut s2 = SignedModalTableaux::parse_formula("a & b", None).unwrap();
                s2.used_backtracking = true;

                let h0 = s2.compute_seal_info();

                let s1 = SignedModalTableaux::apply_move(s1, Move::Beta(0, None)).unwrap();
                let s1 = SignedModalTableaux::apply_move(s1, Move::Undo).unwrap();

                assert_eq!(h0, s1.compute_seal_info())
            })
        }

        #[test]
        fn wrong() {
            session(|| {
                let s = SignedModalTableaux::parse_formula("!(a -> b)", None).unwrap();
                assert!(SignedModalTableaux::apply_move(s, Move::Undo).is_err())
            })
        }
    }
}
