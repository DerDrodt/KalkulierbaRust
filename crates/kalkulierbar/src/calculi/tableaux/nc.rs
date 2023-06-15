use std::{
    collections::{HashMap, HashSet},
    fmt,
    iter::FromIterator,
};

use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{
    logic::{
        fo::{FOTerm, Relation},
        transform::{
            collectors::collect_free_vars,
            logic_node_manipulation::append_suffix_selectively,
            negation_normal_form,
            signature::Signature,
            transformer::{FOTermTransformer, LogicNodeTransformer},
        },
        unify::{
            try_to_parse_unifier, unifier_eq::is_mgu_or_not_unifiable, unify, Substitution,
            UnificationErr,
        },
        LogicNode,
    },
    parse::{fo::parse_fo_formula, ParseErr},
    tamper_protect::ProtectedState,
    Calculus, Symbol,
};

pub struct NCTableaux;

impl<'f> Calculus<'f> for NCTableaux {
    type Params = ();

    type State = State;

    type Move = Move;

    type Error = Err;

    fn parse_formula(
        formula: &'f str,
        _: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        let p = parse_fo_formula(formula)?;
        let nnf = negation_normal_form(p)?;
        Ok(State::new(nnf, true))
    }

    fn apply_move(mut state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        state.status_msg.take();
        match k_move {
            Move::Alpha(node) => apply_alpha(state, node),
            Move::Beta(node) => apply_beta(state, node),
            Move::Gamma(node) => apply_gamma(state, node),
            Move::Delta(node) => apply_delta(state, node),
            Move::Close(node, close, u) => apply_close(state, node, close, u),
            Move::Undo => apply_undo(state),
        }
    }

    fn check_close(state: Self::State) -> crate::calculus::CloseMsg {
        let closed = state.nodes[0].is_closed;
        let msg = match (closed, state.used_backtracking) {
            (false, _) => "The proof tree is not closed",
            (_, false) => {
                "The proof is closed and valid in non-clausal tableaux without backtracking"
            }
            _ => "The proof is closed and valid in non-clausal tableaux with backtracking",
        };
        crate::calculus::CloseMsg {
            closed,
            msg: msg.to_string(),
        }
    }
}

pub struct State {
    formula: LogicNode,
    backtracking: bool,
    nodes: Vec<Node>,
    moves: Vec<Move>,
    idents: HashSet<Symbol>,
    used_backtracking: bool,
    gamma_suffix_counter: u32,
    skolem_counter: u32,
    status_msg: Option<String>,
}

impl State {
    pub fn new(formula: LogicNode, backtracking: bool) -> Self {
        let idents = Signature::of_node(&formula).get_const_and_fn_names();
        Self {
            formula: formula.clone(),
            backtracking,
            nodes: vec![Node::new(None, formula)],
            moves: vec![],
            idents,
            used_backtracking: false,
            gamma_suffix_counter: 0,
            skolem_counter: 0,
            status_msg: None,
        }
    }

    pub fn set_closed(&mut self, node_id: usize) {
        let mut id = node_id;
        // Set isClosed to true for all nodes dominated by node in reverse tree
        loop {
            let node = &mut self.nodes[id];
            node.is_closed = true;
            if let Some(p) = &node.parent {
                id = *p;
            } else {
                break;
            }

            if self.nodes[id]
                .children
                .iter()
                .any(|c| !self.nodes[*c].is_closed)
            {
                break;
            }
        }
        // Set isClosed for all descendants of the node
        let mut wv = vec![node_id];
        while !wv.is_empty() {
            let e = wv.remove(0);
            let n = &mut self.nodes[e];
            for c in &n.children {
                wv.push(*c);
            }
            n.is_closed = true;
        }
    }

    pub fn node_is_ancestor_of(&self, a_id: usize, child_id: usize) -> bool {
        let child = &self.nodes[child_id];
        match child.parent {
            None => false,
            Some(p) => {
                if p == a_id {
                    true
                } else {
                    self.node_is_ancestor_of(a_id, p)
                }
            }
        }
    }
}

impl ProtectedState for State {
    fn compute_seal_info(&self) -> String {
        let various = format!(
            "{}|{}|{}|{}|{}",
            self.backtracking,
            self.used_backtracking,
            self.gamma_suffix_counter,
            self.skolem_counter,
            self.formula
        );
        let identifiers = self
            .idents
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<String>>()
            .join(",");
        let nodes = self
            .nodes
            .iter()
            .map(Node::info)
            .collect::<Vec<String>>()
            .join(",");
        let history = self
            .moves
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<String>>()
            .join(",");
        format!("nctableaux|{various}|{identifiers}|{nodes}|{history}")
    }
}

#[derive(Debug, Clone)]
pub enum Move {
    Alpha(usize),
    Beta(usize),
    Gamma(usize),
    Delta(usize),
    Close(usize, usize, Option<Substitution>),
    Undo,
}

impl fmt::Display for Move {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Move::Alpha(id) => write!(f, "(alpha|{id})"),
            Move::Beta(id) => write!(f, "(beta|{id})"),
            Move::Gamma(id) => write!(f, "(gamma|{id})"),
            Move::Delta(id) => write!(f, "(delta|{id})"),
            Move::Close(node, close, u) => write!(
                f,
                "(close|{node}|{close}|{})",
                match u {
                    Some(u) => u.to_string(),
                    _ => "null".to_string(),
                }
            ),
            Move::Undo => write!(f, "(undo)"),
        }
    }
}

#[derive(Debug)]
pub enum Err {
    ParseErr(ParseErr),
    Str(&'static str),
    UnificationErr(UnificationErr),
    BacktrackingDisabled,
    IllegalNodeId(usize),
    AlreadyClosed(Node),
    ExpectedAnd,
    ExpectedOr,
    ExpectedAll,
    ExpectedEx,
    ExpectedAncestor(Node, Node),
    NodeFormulaNotNegRel(String),
    CloseFormulaNotPosRel(String),
    NodeFormulaNotPosRel(String),
    CloseFormulaNotNegRel(String),
    NeitherAreNegated(String, String),
}

impl From<ParseErr> for Err {
    fn from(e: ParseErr) -> Self {
        Self::ParseErr(e)
    }
}

impl From<&'static str> for Err {
    fn from(e: &'static str) -> Self {
        Self::Str(e)
    }
}

impl From<UnificationErr> for Err {
    fn from(e: UnificationErr) -> Self {
        Self::UnificationErr(e)
    }
}

impl fmt::Display for Err {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Err::ParseErr(e) => fmt::Display::fmt(e, f),
            Err::Str(e) => fmt::Display::fmt(e, f),
            Err::UnificationErr(e) => fmt::Display::fmt(e, f),
            Err::BacktrackingDisabled => {
                write!(f, "Backtracking is not enabled for this proof")
            }
            Err::IllegalNodeId(n) => write!(f, "Node with ID {n} does not exist"),
            Err::AlreadyClosed(n) => write!(f, "Node '{n}' is already closed"),
            Err::ExpectedAnd => write!(f, "Outermost logic operator is not AND"),
            Err::ExpectedOr => write!(f, "Outermost logic operator is not OR"),
            Err::ExpectedAll => {
                write!(f, "Outermost logic operator is not a universal quantifier")
            }
            Err::ExpectedEx => write!(
                f,
                "Outermost logic operator is not an existential quantifier"
            ),
            Err::ExpectedAncestor(c, n) => {
                write!(f, "Node '{c}' is not an ancestor of node '{n}'")
            }
            Err::NodeFormulaNotNegRel(n) => {
                write!(f, "Node formula '{n}' is not a negated relation")
            }
            Err::CloseFormulaNotPosRel(c) => {
                write!(f, "Close node formula '{c}' has to be a positive relation")
            }
            Err::NodeFormulaNotPosRel(n) => {
                write!(f, "Node formula '{n}' has to be a positive relation")
            }
            Err::CloseFormulaNotNegRel(c) => {
                write!(f, "Close node formula '{c}' is not a negated relation")
            }
            Err::NeitherAreNegated(n, c) => write!(f, "Neither '{n}' nor '{c}' are negated"),
        }
    }
}

pub type NCTabResult<T> = Result<T, Err>;

#[derive(Debug, Clone)]
pub struct Node {
    parent: Option<usize>,
    formula: LogicNode,
    is_closed: bool,
    close_ref: Option<usize>,
    children: Vec<usize>,
}

impl Node {
    pub fn new(parent: Option<usize>, formula: LogicNode) -> Self {
        Self {
            parent,
            formula,
            is_closed: false,
            close_ref: None,
            children: vec![],
        }
    }

    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
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
            .join(", ");
        let is_closed = self.is_closed;
        let close_ref = match self.close_ref {
            Some(p) => p.to_string(),
            _ => "null".to_string(),
        };
        let formula = self.formula.to_string();
        format!("({parent}|{children}|{is_closed}|{close_ref}|{formula})")
    }
}

impl fmt::Display for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.formula, f)
    }
}

fn apply_alpha(mut state: State, node: usize) -> NCTabResult<State> {
    check_node_restrictions(&state, node)?;
    let n = &mut state.nodes[node];
    let formula = n.formula.clone();
    let children = n.children.clone();
    n.children.clear();

    if !matches!(formula, LogicNode::And(..)) {
        return Err(Err::ExpectedAnd);
    }

    let mut w = vec![formula];
    let mut p_id = node;

    while !w.is_empty() {
        let f = w.remove(0);
        match f {
            LogicNode::And(l, r) => {
                w.push(*r);
                w.push(*l);
            }
            f => {
                let len = state.nodes.len();
                state.nodes.push(Node::new(Some(p_id), f));
                state.nodes[p_id].children.push(len);
                p_id = len;
            }
        }
    }

    // Add the node's children to the last inserted node to restore the tree structure
    for c in children {
        state.nodes[p_id].children.push(c);
        state.nodes[c].parent = Some(p_id);
    }

    if state.backtracking {
        state.moves.push(Move::Alpha(node));
    }

    Ok(state)
}

fn apply_beta(mut state: State, node: usize) -> NCTabResult<State> {
    check_node_restrictions(&state, node)?;
    let n = &mut state.nodes[node];
    let formula = n.formula.clone();

    if !matches!(formula, LogicNode::Or(..)) {
        return Err(Err::ExpectedOr);
    }

    // Collect all leaves in the current branch where the split nodes
    // will have to be appended
    // If the node is a leaf, this will only be the nodeID
    let leave_ids = open_child_leaves_of(&state, node);

    let mut w = vec![formula];

    while !w.is_empty() {
        let f = w.remove(0);
        match f {
            LogicNode::Or(l, r) => {
                w.push(*r);
                w.push(*l);
            }
            f => {
                for l in &leave_ids {
                    let l = *l;
                    let n = Node::new(Some(l), f.clone());
                    let len = state.nodes.len();
                    state.nodes[l].children.push(len);
                    state.nodes.push(n);
                }
            }
        }
    }

    if state.backtracking {
        state.moves.push(Move::Alpha(node));
    }

    Ok(state)
}

fn apply_gamma(mut state: State, node: usize) -> NCTabResult<State> {
    check_node_restrictions(&state, node)?;
    let n = &mut state.nodes[node];
    let formula = &n.formula;

    let (fs, fc) = match formula {
        LogicNode::All(s, c) => (*s, *(c.clone())),
        _ => return Err(Err::ExpectedAll),
    };

    let children = n.children.clone();
    n.children.clear();

    // Transform new Formula + remove UniversalQuantifier
    state.gamma_suffix_counter += 1;
    let suffix = format!("_{}", state.gamma_suffix_counter);
    let nf = append_suffix_selectively(fc, fs, &suffix);

    // Add new identifiers to the set
    // This is not strictly speaking necessary as Skolem term names can never be in
    // conflict with suffixed variable names, but we'll do it still to ensure
    // that state.identifiers contains _all_ identifiers in the tableaux

    for s in Signature::of_node(&nf).get_const_and_fn_names() {
        state.idents.insert(s);
    }

    // Add new node to tree
    let mut nn = Node::new(Some(node), nf);
    let idx = state.nodes.len();
    for c in children {
        nn.children.push(c);
        state.nodes[c].parent = Some(idx);
    }
    state.nodes.push(nn);

    if state.backtracking {
        state.moves.push(Move::Gamma(node));
    }

    Ok(state)
}

fn apply_delta(mut state: State, node: usize) -> NCTabResult<State> {
    check_node_restrictions(&state, node)?;
    let n = &mut state.nodes[node];
    let formula = &n.formula;

    let (fs, fc) = match formula {
        LogicNode::Ex(s, c) => (*s, *(c.clone())),
        _ => return Err(Err::ExpectedEx),
    };

    let children = n.children.clone();
    n.children.clear();

    // Apply Skolemization to the top-level existential quantifier
    // This adds the newly created Skolem term identifier to the state.identifiers set
    state.skolem_counter += 1;
    let (new_sym, nf) = delta_skolem(fs, fc, &state.idents, state.skolem_counter);
    state.idents.insert(new_sym);

    // Add new node to tree
    let mut nn = Node::new(Some(node), nf);
    let idx = state.nodes.len();
    for c in children {
        nn.children.push(c);
        state.nodes[c].parent = Some(idx);
    }
    state.nodes.push(nn);

    if state.backtracking {
        state.moves.push(Move::Delta(node));
    }

    Ok(state)
}

fn apply_close(
    mut state: State,
    node_id: usize,
    close_id: usize,
    u: Option<Substitution>,
) -> NCTabResult<State> {
    check_close_id_restrictions(&state, node_id, close_id)?;
    let node = &state.nodes[node_id];
    let close = &state.nodes[close_id];

    // Verify that node and closeNode are (negated) Relations of compatible polarity
    let (node_rel, close_rel) = check_close_relation(&node.formula, &close.formula)?;

    // Use user-supplied variable assignment if given, calculate MGU otherwise
    let u = match u {
        Some(u) => u,
        _ => unify(&node_rel, &close_rel)?,
    };

    if !is_mgu_or_not_unifiable(&u, &node_rel, &close_rel) {
        state.status_msg = Some("The unifier you specified is not an MGU".to_string());
    }

    // Apply all specified variable instantiations globally
    for n in &mut state.nodes {
        n.formula = n.formula.instantiate(&u);
    }

    // Close branch
    let node = &mut state.nodes[node_id];
    node.close_ref = Some(close_id);
    state.set_closed(node_id);

    // Record close move for backtracking purposes
    if state.backtracking {
        state.moves.push(Move::Close(node_id, close_id, Some(u)));
    }

    Ok(state)
}

fn apply_undo(state: State) -> NCTabResult<State> {
    if !state.backtracking {
        return Err(Err::BacktrackingDisabled);
    }

    // Can't undo any more moves in initial state
    if state.moves.is_empty() {
        return Ok(state);
    }

    // Create a fresh clone-state with the same parameters and input formula
    let mut moves = state.moves;
    moves.pop();
    let formula = state.formula;
    let mut state = State::new(formula, true);
    state.used_backtracking = true;

    // Re-build the proof tree in the clone state
    for m in moves {
        state = NCTableaux::apply_move(state, m)?;
    }

    Ok(state)
}

fn check_node_restrictions(state: &State, n_id: usize) -> NCTabResult<()> {
    if n_id >= state.nodes.len() {
        return Err(Err::IllegalNodeId(n_id));
    }
    let n = &state.nodes[n_id];
    if n.is_closed {
        return Err(Err::AlreadyClosed(n.clone()));
    }
    Ok(())
}

fn check_close_id_restrictions(state: &State, node_id: usize, close_id: usize) -> NCTabResult<()> {
    check_node_restrictions(state, node_id)?;
    if close_id >= state.nodes.len() {
        return Err(Err::IllegalNodeId(close_id));
    }

    let node = &state.nodes[node_id];
    let close = &state.nodes[close_id];

    // Verify that closeNode is transitive parent of node
    if !state.node_is_ancestor_of(close_id, node_id) {
        return Err(Err::ExpectedAncestor(close.clone(), node.clone()));
    }

    Ok(())
}

fn check_close_relation(
    node_formula: &LogicNode,
    close_formula: &LogicNode,
) -> NCTabResult<(Relation, Relation)> {
    Ok(if let LogicNode::Not(c) = node_formula {
        let c = c.as_ref();
        match (c, close_formula) {
            (LogicNode::Rel(s1, args1), LogicNode::Rel(s2, args2)) => (
                Relation::new(*s1, args1.clone()),
                Relation::new(*s2, args2.clone()),
            ),
            (_, LogicNode::Rel(..)) => {
                return Err(Err::NodeFormulaNotNegRel(node_formula.to_string()))
            }
            _ => return Err(Err::CloseFormulaNotPosRel(close_formula.to_string())),
        }
    } else if let LogicNode::Not(c) = close_formula {
        let c = c.as_ref();
        match (c, node_formula) {
            (LogicNode::Rel(s1, args1), LogicNode::Rel(s2, args2)) => (
                Relation::new(*s2, args2.clone()),
                Relation::new(*s1, args1.clone()),
            ),
            (_, LogicNode::Rel(..)) => {
                return Err(Err::NodeFormulaNotPosRel(node_formula.to_string()))
            }
            _ => return Err(Err::CloseFormulaNotNegRel(close_formula.to_string())),
        }
    } else {
        return Err(Err::NeitherAreNegated(
            node_formula.to_string(),
            close_formula.to_string(),
        ));
    })
}

fn open_child_leaves_of(state: &State, n_id: usize) -> Vec<usize> {
    let mut w = vec![n_id];
    let mut ls = vec![];

    while !w.is_empty() {
        let idx = w.remove(0);
        let n = &state.nodes[idx];
        if n.is_leaf() {
            ls.push(idx);
        } else {
            for c in &n.children {
                w.push(*c);
            }
        }
    }
    ls
}

fn delta_skolem(
    to_replace: Symbol,
    child: LogicNode,
    blacklist: &HashSet<Symbol>,
    sk_ctr: u32,
) -> (Symbol, LogicNode) {
    let free_vars = collect_free_vars(&child);
    let (new_sym, term) = get_skolem_term(sk_ctr, blacklist, &free_vars);

    // Replace variables bound by top-level quantifier with Skolem term
    let new_node = DeltaSkolemization::new(to_replace, term).visit(child);
    (new_sym, new_node)
}

fn get_skolem_term(
    sk_base_count: u32,
    blacklist: &HashSet<Symbol>,
    free_vars: &HashSet<Symbol>,
) -> (Symbol, FOTerm) {
    let mut sk_counter = sk_base_count;
    let mut sk_name = Symbol::intern(&format!("sk{sk_counter}"));

    // Ensure freshness
    while blacklist.contains(&sk_name) {
        sk_counter += 1;
        sk_name = Symbol::intern(&format!("sk{sk_counter}"));
    }

    let sk_term = if free_vars.is_empty() {
        // Constant iff no free vars
        FOTerm::Const(sk_name)
    } else {
        let args = free_vars
            .iter()
            .map(|v| FOTerm::QuantifiedVar(*v))
            .collect();
        FOTerm::Function(sk_name, args)
    };
    (sk_name, sk_term)
}

struct DeltaSkolemization {
    to_replace: Symbol,
    replacer: DeltaTermReplacer,
}

impl DeltaSkolemization {
    fn new(to_replace: Symbol, replace_with: FOTerm) -> Self {
        Self {
            to_replace,
            replacer: DeltaTermReplacer::new(to_replace, replace_with),
        }
    }
}

impl LogicNodeTransformer for DeltaSkolemization {
    type Ret = LogicNode;

    fn visit_var(&self, _: Symbol) -> Self::Ret {
        panic!()
    }

    fn visit_not(&self, child: LogicNode) -> Self::Ret {
        LogicNode::Not(self.visit(child).into())
    }

    fn visit_and(&self, left: LogicNode, right: LogicNode) -> Self::Ret {
        LogicNode::And(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_or(&self, left: LogicNode, right: LogicNode) -> Self::Ret {
        LogicNode::Or(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_impl(&self, left: LogicNode, right: LogicNode) -> Self::Ret {
        LogicNode::Impl(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_equiv(&self, left: LogicNode, right: LogicNode) -> Self::Ret {
        LogicNode::Equiv(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_rel(&self, spelling: Symbol, args: Vec<FOTerm>) -> Self::Ret {
        LogicNode::Rel(
            spelling,
            args.into_iter().map(|a| self.replacer.visit(a)).collect(),
        )
    }

    fn visit_all(&self, var: Symbol, child: LogicNode) -> Self::Ret {
        let child = if var == self.to_replace {
            child
        } else {
            self.visit(child)
        };
        LogicNode::All(var, child.into())
    }

    fn visit_ex(&self, var: Symbol, child: LogicNode) -> Self::Ret {
        let child = if var == self.to_replace {
            child
        } else {
            self.visit(child)
        };
        LogicNode::Ex(var, child.into())
    }

    fn visit_box(&self, _: LogicNode) -> Self::Ret {
        panic!()
    }

    fn visit_diamond(&self, _: LogicNode) -> Self::Ret {
        panic!()
    }
}

struct DeltaTermReplacer {
    to_replace: Symbol,
    replace_with: FOTerm,
}

impl DeltaTermReplacer {
    fn new(to_replace: Symbol, replace_with: FOTerm) -> Self {
        Self {
            to_replace,
            replace_with,
        }
    }
}

impl FOTermTransformer for DeltaTermReplacer {
    fn visit_quantified_var(&self, s: Symbol) -> FOTerm {
        if s == self.to_replace {
            self.replace_with.clone()
        } else {
            FOTerm::QuantifiedVar(s)
        }
    }

    fn visit_const(&self, s: Symbol) -> FOTerm {
        FOTerm::Const(s)
    }

    fn visit_fn(&self, name: Symbol, args: Vec<FOTerm>) -> FOTerm {
        FOTerm::Function(name, args.into_iter().map(|a| self.visit(a)).collect())
    }
}

impl Serialize for Node {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("NCTabMove", 6)?;
        state.serialize_field("parent", &self.parent)?;
        state.serialize_field("formula", &self.formula)?;
        state.serialize_field("isClosed", &self.is_closed)?;
        state.serialize_field("closeRef", &self.close_ref)?;
        state.serialize_field("children", &self.children)?;
        state.serialize_field("spelling", &self.formula.to_string())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for Node {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "parent")]
            Parent,
            #[serde(rename = "formula")]
            Formula,
            #[serde(rename = "isClosed")]
            IsClosed,
            #[serde(rename = "closeRef")]
            CloseRef,
            #[serde(rename = "children")]
            Children,
            #[serde(rename = "spelling")]
            Spelling,
        }

        struct NodeVisitor;

        impl<'de> Visitor<'de> for NodeVisitor {
            type Value = Node;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct NCTabNode")
            }

            fn visit_map<V>(self, mut map: V) -> Result<Node, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut parent: Option<usize> = None;
                let mut formula: Option<LogicNode> = None;
                let mut is_closed: Option<bool> = None;
                let mut close_ref: Option<usize> = None;
                let mut children: Option<Vec<usize>> = None;
                let mut spelling: Option<String> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Parent => {
                            if parent.is_some() {
                                return Err(de::Error::duplicate_field("parent"));
                            }
                            parent = Some(map.next_value()?);
                        }
                        Field::Formula => {
                            if formula.is_some() {
                                return Err(de::Error::duplicate_field("formula"));
                            }
                            formula = Some(map.next_value()?);
                        }
                        Field::IsClosed => {
                            if is_closed.is_some() {
                                return Err(de::Error::duplicate_field("isClosed"));
                            }
                            is_closed = Some(map.next_value()?);
                        }
                        Field::CloseRef => {
                            if close_ref.is_some() {
                                return Err(de::Error::duplicate_field("closeRef"));
                            }
                            close_ref = Some(map.next_value()?);
                        }
                        Field::Children => {
                            if children.is_some() {
                                return Err(de::Error::duplicate_field("children"));
                            }
                            children = Some(map.next_value()?);
                        }
                        Field::Spelling => {
                            if spelling.is_some() {
                                return Err(de::Error::duplicate_field("spelling"));
                            }
                            spelling = Some(map.next_value()?);
                        }
                    }
                }

                let formula = formula.ok_or_else(|| de::Error::missing_field("formula"))?;
                let is_closed = is_closed.ok_or_else(|| de::Error::missing_field("isClosed"))?;
                let children = children.ok_or_else(|| de::Error::missing_field("children"))?;

                Ok(Node {
                    parent,
                    formula,
                    is_closed,
                    close_ref,
                    children,
                })
            }
        }

        const FIELDS: &[&str] = &[
            "parent", "formula", "isClosed", "closeRef", "children", "spelling",
        ];
        deserializer.deserialize_struct("NCTabNode", FIELDS, NodeVisitor)
    }
}

impl Serialize for Move {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (ty, len, n_id) = match self {
            Move::Alpha(n) => ("alpha", 2, n),
            Move::Beta(n) => ("beta", 2, n),
            Move::Gamma(n) => ("gamma", 2, n),
            Move::Delta(n) => ("delta", 2, n),
            Move::Close(n, _, _) => ("close", 4, n),
            Move::Undo => ("undo", 1, &0),
        };
        let mut state = serializer.serialize_struct("NCTabMove", len)?;
        state.serialize_field("type", ty)?;
        if len > 1 {
            state.serialize_field("nodeID", n_id)?;
        }
        if let Self::Close(_, c_id, u) = self {
            state.serialize_field("closeID", c_id)?;
            state.serialize_field("varAssign", &u.as_ref().map(|u| u.rendered_map()))?;
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
            #[serde(rename = "closeID")]
            CloseID,
            #[serde(rename = "varAssign")]
            VarAssign,
        }

        struct MoveVisitor;

        impl<'de> Visitor<'de> for MoveVisitor {
            type Value = Move;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct NCTabMove")
            }

            fn visit_map<V>(self, mut map: V) -> Result<Move, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut node_id: Option<usize> = None;
                let mut close_id: Option<usize> = None;
                let mut var_assign: Option<HashMap<Symbol, String>> = None;

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
                        Field::CloseID => {
                            if close_id.is_some() {
                                return Err(de::Error::duplicate_field("closeID"));
                            }
                            close_id = Some(map.next_value()?);
                        }
                        Field::VarAssign => {
                            if var_assign.is_some() {
                                return Err(de::Error::duplicate_field("varAssign"));
                            }
                            var_assign = Some(map.next_value()?);
                        }
                    }
                }
                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                let ty: &str = &ty;
                Ok(match ty {
                    "alpha" => {
                        Move::Alpha(node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?)
                    }
                    "beta" => {
                        Move::Beta(node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?)
                    }
                    "gamma" => {
                        Move::Gamma(node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?)
                    }
                    "delta" => {
                        Move::Delta(node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?)
                    }
                    "close" => {
                        let u = if let Some(v) = var_assign {
                            match try_to_parse_unifier(v) {
                                Ok(u) => Some(u),
                                Err(e) => return Err(de::Error::custom(e.to_string())),
                            }
                        } else {
                            None
                        };

                        Move::Close(
                            node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                            close_id.ok_or_else(|| de::Error::missing_field("closeID"))?,
                            u,
                        )
                    }
                    "undo" => Move::Undo,
                    _ => todo!(),
                })
            }
        }

        const FIELDS: &[&str] = &[
            "type",
            "spelling",
            "child",
            "leftChild",
            "rightChild",
            "arguments",
            "varName",
            "boundVariables",
        ];
        deserializer.deserialize_struct("LogicNode", FIELDS, MoveVisitor)
    }
}

impl Serialize for State {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("NCTabState", 10)?;
        state.serialize_field("formula", &self.formula)?;
        state.serialize_field("backtracking", &self.backtracking)?;
        state.serialize_field("tree", &self.nodes)?;
        state.serialize_field("moveHistory", &self.moves)?;
        state.serialize_field("identifiers", &Vec::from_iter(&self.idents))?;
        state.serialize_field("usedBacktracking", &self.used_backtracking)?;
        state.serialize_field("gammaSuffixCounter", &self.gamma_suffix_counter)?;
        state.serialize_field("skolemCounter", &self.skolem_counter)?;
        state.serialize_field("statusMessage", &self.status_msg)?;
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
            #[serde(rename = "formula")]
            Formula,
            #[serde(rename = "backtracking")]
            Backtracking,
            #[serde(rename = "tree")]
            Tree,
            #[serde(rename = "moveHistory")]
            MoveHistory,
            #[serde(rename = "identifiers")]
            Identifiers,
            #[serde(rename = "usedBacktracking")]
            UsedBacktracking,
            #[serde(rename = "gammaSuffixCounter")]
            GammaSuffixCounter,
            #[serde(rename = "skolemCounter")]
            SkolemCounter,
            #[serde(rename = "StatusMessage")]
            StatusMsg,
            #[serde(rename = "seal")]
            Seal,
        }

        struct StateVisitor;

        impl<'de> Visitor<'de> for StateVisitor {
            type Value = State;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct NCTabState")
            }

            fn visit_map<V>(self, mut map: V) -> Result<State, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut formula: Option<LogicNode> = None;
                let mut backtracking: Option<bool> = None;
                let mut tree: Option<Vec<Node>> = None;
                let mut moves: Option<Vec<Move>> = None;
                let mut idents: Option<Vec<Symbol>> = None;
                let mut used_backtracking: Option<bool> = None;
                let mut gamma_suffix_counter: Option<u32> = None;
                let mut skolem_counter: Option<u32> = None;
                let mut status_msg: Option<String> = None;
                let mut seal: Option<String> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Formula => {
                            if formula.is_some() {
                                return Err(de::Error::duplicate_field("formula"));
                            }
                            formula = Some(map.next_value()?);
                        }
                        Field::Backtracking => {
                            if backtracking.is_some() {
                                return Err(de::Error::duplicate_field("backtracking"));
                            }
                            backtracking = Some(map.next_value()?);
                        }
                        Field::Tree => {
                            if tree.is_some() {
                                return Err(de::Error::duplicate_field("tree"));
                            }
                            tree = Some(map.next_value()?);
                        }
                        Field::MoveHistory => {
                            if moves.is_some() {
                                return Err(de::Error::duplicate_field("moveHistory"));
                            }
                            moves = Some(map.next_value()?);
                        }
                        Field::Identifiers => {
                            if idents.is_some() {
                                return Err(de::Error::duplicate_field("identifiers"));
                            }
                            idents = Some(map.next_value()?);
                        }
                        Field::UsedBacktracking => {
                            if used_backtracking.is_some() {
                                return Err(de::Error::duplicate_field("usedBacktracking"));
                            }
                            used_backtracking = Some(map.next_value()?);
                        }
                        Field::GammaSuffixCounter => {
                            if gamma_suffix_counter.is_some() {
                                return Err(de::Error::duplicate_field("gammaSufficCounter"));
                            }
                            gamma_suffix_counter = Some(map.next_value()?);
                        }
                        Field::SkolemCounter => {
                            if skolem_counter.is_some() {
                                return Err(de::Error::duplicate_field("skolemCounter"));
                            }
                            skolem_counter = Some(map.next_value()?);
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

                let formula = formula.ok_or_else(|| de::Error::missing_field("formula"))?;
                let backtracking =
                    backtracking.ok_or_else(|| de::Error::missing_field("backtracking"))?;
                let tree = tree.ok_or_else(|| de::Error::missing_field("tree"))?;
                let moves = moves.ok_or_else(|| de::Error::missing_field("moveHistory"))?;
                let idents = idents.ok_or_else(|| de::Error::missing_field("identifiers"))?;
                let idents = HashSet::from_iter(idents);
                let used_backtracking = used_backtracking
                    .ok_or_else(|| de::Error::missing_field("usedBacktracking"))?;
                let gamma_suffix_counter = gamma_suffix_counter
                    .ok_or_else(|| de::Error::missing_field("gammaSuffixCounter"))?;
                let skolem_counter =
                    skolem_counter.ok_or_else(|| de::Error::missing_field("skolemCounter"))?;
                let seal = seal.ok_or_else(|| de::Error::missing_field("seal"))?;

                let s = State {
                    formula,
                    backtracking,
                    nodes: tree,
                    moves,
                    idents,
                    used_backtracking,
                    gamma_suffix_counter,
                    skolem_counter,
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
            "backtracking",
            "tree",
            "moveHistory",
            "identifiers",
            "usedBacktracking",
            "gammaSuffixCounter",
            "skolemCounter",
            "statusMessage",
            "seal",
        ];
        deserializer.deserialize_struct("NCTabState", FIELDS, StateVisitor)
    }
}
