use std::fmt;

use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{
    calculus::CloseMsg,
    logic::LogicNode,
    parse::{sequent, ParseErr},
    tamper_protect::ProtectedState,
    Calculus, SynEq,
};

use super::{SequentNode, SequentParams};

#[derive(Debug)]
pub enum PropSeqErr {
    ParseErr(ParseErr),
    InvalidNodeId(usize),
    ExpectedLeaf,
    AxNotApplicable,
    InvalidFormulaId(usize),
    RuleNotApplicable(&'static str, &'static str),
    NothingToUndo,
}

impl From<ParseErr> for PropSeqErr {
    fn from(e: ParseErr) -> Self {
        Self::ParseErr(e)
    }
}

impl fmt::Display for PropSeqErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PropSeqErr::ParseErr(e) => fmt::Display::fmt(e, f),
            PropSeqErr::InvalidNodeId(n) => write!(f, "Node with ID {n} does not exist"),
            PropSeqErr::ExpectedLeaf => write!(f, "Rules can only be applied on leaf level"),
            PropSeqErr::AxNotApplicable => write!(
                f,
                "Axiom rule needs two identical formulas on both sides to be applied"
            ),
            PropSeqErr::InvalidFormulaId(id) => {
                write!(
                    f,
                    "Formula with ID {id} does not exist in the selected node"
                )
            }
            PropSeqErr::RuleNotApplicable(rule, expected) => {
                if expected.starts_with("i") {
                    write!(f, "Rule {rule} can only be applied on an {expected}")
                } else {
                    write!(f, "Rule {rule} can only be applied on a {expected}")
                }
            }
            PropSeqErr::NothingToUndo => write!(f, "No move to undo"),
        }
    }
}

pub type PropSeqResult<T> = Result<T, PropSeqErr>;

#[derive(Debug, Clone)]
pub enum PropSeqMove {
    Ax(usize),
    NotL(usize, usize),
    NotR(usize, usize),
    AndL(usize, usize),
    AndR(usize, usize),
    OrL(usize, usize),
    OrR(usize, usize),
    ImplL(usize, usize),
    ImplR(usize, usize),
    Undo,
    Prune(usize),
}

#[derive(Debug)]
pub struct PropSeqState {
    nodes: Vec<SequentNode<PropSeqMove>>,
    show_only_applicable_rules: bool,
}

impl PropSeqState {
    pub fn new(nodes: Vec<SequentNode<PropSeqMove>>, show_only_applicable_rules: bool) -> Self {
        Self {
            nodes,
            show_only_applicable_rules,
        }
    }

    pub fn add_node(&mut self, parent_id: usize, n: SequentNode<PropSeqMove>) -> usize {
        let idx = self.nodes.len();
        let parent = &mut self.nodes[parent_id];
        parent.children.push(idx);
        self.nodes.push(n);
        idx
    }

    fn set_node_closed(&mut self, node_id: usize) {
        let mut node_id = node_id;
        while self.nodes[node_id].is_leaf()
            || self.nodes[node_id]
                .children
                .iter()
                .all(|c| self.nodes[*c].is_closed)
        {
            let node = &mut self.nodes[node_id];
            node.is_closed = true;
            if let Some(p) = node.parent {
                node_id = p;
            } else {
                break;
            }
        }
    }
}

impl ProtectedState for PropSeqState {
    fn compute_seal_info(&self) -> String {
        format!(
            "psc|{}|{}",
            self.nodes
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(""),
            self.show_only_applicable_rules
        )
    }
}

pub struct PropSequent;

impl<'f> Calculus<'f> for PropSequent {
    type Params = SequentParams;

    type State = PropSeqState;

    type Move = PropSeqMove;

    type Error = PropSeqErr;

    fn parse_formula(
        formula: &'f str,
        params: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        let (left, right) = sequent::parse_prop(formula)?;
        Ok(PropSeqState::new(
            vec![SequentNode::new(None, left, right, None)],
            params.unwrap_or_default().show_only_applicable_rules,
        ))
    }

    fn apply_move(state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        match k_move {
            PropSeqMove::Ax(n) => apply_ax(state, n),
            PropSeqMove::NotL(node, formula) => apply_not_l(state, node, formula),
            PropSeqMove::NotR(node, formula) => apply_not_r(state, node, formula),
            PropSeqMove::AndL(node, formula) => apply_and_l(state, node, formula),
            PropSeqMove::AndR(node, formula) => apply_and_r(state, node, formula),
            PropSeqMove::OrL(node, formula) => apply_or_l(state, node, formula),
            PropSeqMove::OrR(node, formula) => apply_or_r(state, node, formula),
            PropSeqMove::ImplL(node, formula) => apply_impl_l(state, node, formula),
            PropSeqMove::ImplR(node, formula) => apply_impl_r(state, node, formula),
            PropSeqMove::Undo => apply_undo(state),
            PropSeqMove::Prune(node) => apply_prune(state, node),
        }
    }

    fn check_close(state: Self::State) -> crate::calculus::CloseMsg {
        if state.nodes.iter().all(|n| n.is_closed) {
            CloseMsg {
                closed: true,
                msg: "The proof is closed and valid in Propositional Logic".to_string(),
            }
        } else {
            CloseMsg {
                closed: false,
                msg: "Not all branches of the proof tree are closed".to_string(),
            }
        }
    }
}

fn apply_ax(mut state: PropSeqState, node_id: usize) -> PropSeqResult<PropSeqState> {
    check_node_id(&state, node_id)?;
    check_leaf(&state, node_id)?;
    let leaf = &state.nodes[node_id];

    for l in &leaf.left_formulas {
        if leaf.right_formulas.iter().any(|r| r.syn_eq(l)) {
            let ax = SequentNode::new(
                Some(node_id),
                vec![],
                vec![],
                Some(PropSeqMove::Ax(node_id)),
            );
            let idx = state.add_node(node_id, ax);
            state.set_node_closed(idx);
            return Ok(state);
        }
    }

    Err(PropSeqErr::AxNotApplicable)
}

fn apply_not_l(
    mut state: PropSeqState,
    node_id: usize,
    f_id: usize,
) -> PropSeqResult<PropSeqState> {
    check_left(&state, node_id, f_id)?;
    let leaf = &state.nodes[node_id];
    let formula = &leaf.left_formulas[f_id];

    if let LogicNode::Not(c) = formula {
        let mut nl = leaf.left_formulas.clone();
        nl.remove(f_id);
        let mut nr = leaf.right_formulas.clone();
        nr.push(*c.to_owned());
        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                nl,
                nr,
                Some(PropSeqMove::NotL(node_id, f_id)),
            ),
        );
        Ok(state)
    } else {
        Err(PropSeqErr::RuleNotApplicable("notLeft", "negation"))
    }
}

fn apply_not_r(
    mut state: PropSeqState,
    node_id: usize,
    f_id: usize,
) -> PropSeqResult<PropSeqState> {
    check_right(&state, node_id, f_id)?;
    let leaf = &state.nodes[node_id];
    let formula = &leaf.right_formulas[f_id];

    if let LogicNode::Not(c) = formula {
        let mut nl = leaf.left_formulas.clone();
        nl.push(*c.to_owned());
        let mut nr = leaf.right_formulas.clone();
        nr.remove(f_id);
        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                nl,
                nr,
                Some(PropSeqMove::NotR(node_id, f_id)),
            ),
        );
        Ok(state)
    } else {
        Err(PropSeqErr::RuleNotApplicable("notRight", "negation"))
    }
}

fn apply_and_l(
    mut state: PropSeqState,
    node_id: usize,
    f_id: usize,
) -> PropSeqResult<PropSeqState> {
    check_left(&state, node_id, f_id)?;
    let leaf = &state.nodes[node_id];
    let formula = &leaf.left_formulas[f_id];

    if let LogicNode::And(l, r) = formula {
        let mut nl = leaf.left_formulas.clone();
        nl.remove(f_id);
        nl.insert(f_id, *l.clone());
        nl.insert(f_id + 1, *r.clone());
        let nr = leaf.right_formulas.clone();
        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                nl,
                nr,
                Some(PropSeqMove::AndL(node_id, f_id)),
            ),
        );
        Ok(state)
    } else {
        Err(PropSeqErr::RuleNotApplicable("andLeft", "conjunction"))
    }
}

fn apply_and_r(
    mut state: PropSeqState,
    node_id: usize,
    f_id: usize,
) -> PropSeqResult<PropSeqState> {
    check_right(&state, node_id, f_id)?;
    let leaf = &state.nodes[node_id];
    let formula = &leaf.right_formulas[f_id];

    if let LogicNode::And(l, r) = formula {
        let nl = leaf.left_formulas.clone();
        let mut r_fs = leaf.right_formulas.clone();
        let mut nr = r_fs.clone();
        let r = *r.clone();
        nr.remove(f_id);
        nr.insert(f_id, *l.clone());
        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                nl.clone(),
                nr,
                Some(PropSeqMove::AndR(node_id, f_id)),
            ),
        );

        r_fs.remove(f_id);
        r_fs.insert(f_id, r);
        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                nl,
                r_fs,
                Some(PropSeqMove::AndR(node_id, f_id)),
            ),
        );
        Ok(state)
    } else {
        Err(PropSeqErr::RuleNotApplicable("andRight", "conjunction"))
    }
}

fn apply_or_l(mut state: PropSeqState, node_id: usize, f_id: usize) -> PropSeqResult<PropSeqState> {
    check_left(&state, node_id, f_id)?;
    let leaf = &state.nodes[node_id];
    let formula = &leaf.left_formulas[f_id];

    if let LogicNode::Or(l, r) = formula {
        let mut nl = leaf.left_formulas.clone();
        let mut l_fs = leaf.left_formulas.clone();
        let nr = leaf.right_formulas.clone();
        let r = *r.clone();
        nl.remove(f_id);
        nl.insert(f_id, *l.clone());
        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                nl,
                nr.clone(),
                Some(PropSeqMove::OrL(node_id, f_id)),
            ),
        );

        l_fs.remove(f_id);
        l_fs.insert(f_id, r);
        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                l_fs,
                nr,
                Some(PropSeqMove::OrL(node_id, f_id)),
            ),
        );
        Ok(state)
    } else {
        Err(PropSeqErr::RuleNotApplicable("orLeft", "disjunction"))
    }
}

fn apply_or_r(mut state: PropSeqState, node_id: usize, f_id: usize) -> PropSeqResult<PropSeqState> {
    check_right(&state, node_id, f_id)?;
    let leaf = &state.nodes[node_id];
    let formula = &leaf.right_formulas[f_id];

    if let LogicNode::Or(l, r) = formula {
        let mut nr = leaf.right_formulas.clone();
        nr.remove(f_id);
        nr.insert(f_id, *l.clone());
        nr.insert(f_id + 1, *r.clone());
        let nl = leaf.left_formulas.clone();
        state.add_node(
            node_id,
            SequentNode::new(Some(node_id), nl, nr, Some(PropSeqMove::OrR(node_id, f_id))),
        );
        Ok(state)
    } else {
        Err(PropSeqErr::RuleNotApplicable("orRight", "disjunction"))
    }
}

fn apply_impl_l(
    mut state: PropSeqState,
    node_id: usize,
    f_id: usize,
) -> PropSeqResult<PropSeqState> {
    check_left(&state, node_id, f_id)?;
    let leaf = &state.nodes[node_id];
    let formula = &leaf.left_formulas[f_id];

    if let LogicNode::Impl(l, r) = formula {
        let mut nlc_l = leaf.left_formulas.clone();
        nlc_l.remove(f_id);
        let mut nlc_r = leaf.right_formulas.clone();
        nlc_r.insert(f_id, *l.clone());

        let mut nrc_l = leaf.left_formulas.clone();
        nrc_l.remove(f_id);
        nrc_l.insert(f_id, *r.clone());
        let nrc_r = leaf.right_formulas.clone();

        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                nlc_l,
                nlc_r,
                Some(PropSeqMove::ImplL(node_id, f_id)),
            ),
        );
        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                nrc_l,
                nrc_r,
                Some(PropSeqMove::ImplL(node_id, f_id)),
            ),
        );

        Ok(state)
    } else {
        Err(PropSeqErr::RuleNotApplicable("implLeft", "implication"))
    }
}

fn apply_impl_r(
    mut state: PropSeqState,
    node_id: usize,
    f_id: usize,
) -> PropSeqResult<PropSeqState> {
    check_right(&state, node_id, f_id)?;
    let leaf = &state.nodes[node_id];
    let formula = &leaf.right_formulas[f_id];

    if let LogicNode::Impl(l, r) = formula {
        let mut nl = leaf.left_formulas.clone();
        nl.push(*l.clone());
        let mut nr = leaf.right_formulas.clone();
        nr.remove(f_id);
        nr.insert(f_id, *r.clone());

        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                nl,
                nr,
                Some(PropSeqMove::ImplR(node_id, f_id)),
            ),
        );

        Ok(state)
    } else {
        Err(PropSeqErr::RuleNotApplicable("implRight", "implication"))
    }
}

fn apply_undo(state: PropSeqState) -> PropSeqResult<PropSeqState> {
    if state.nodes.len() <= 1 {
        return Err(PropSeqErr::NothingToUndo);
    }

    let latest = state.nodes.last().unwrap();
    assert!(latest.is_leaf());

    let p_id = latest.parent.unwrap();
    let mut state = apply_prune(state, p_id)?;

    state.nodes[p_id].is_closed = false;
    let mut n_id = p_id;
    loop {
        let n = &state.nodes[n_id];
        if !n.is_closed {
            break;
        }
        if let Some(p) = &n.parent {
            state.nodes[*p].is_closed;
            n_id = *p;
        } else {
            break;
        }
    }

    Ok(state)
}

fn apply_prune(mut state: PropSeqState, node_id: usize) -> PropSeqResult<PropSeqState> {
    check_node_id(&state, node_id)?;

    let n = &state.nodes[node_id];

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

fn check_node_id(state: &PropSeqState, node_id: usize) -> PropSeqResult<()> {
    if node_id >= state.nodes.len() {
        Err(PropSeqErr::InvalidNodeId(node_id))
    } else {
        Ok(())
    }
}

fn check_leaf(state: &PropSeqState, node_id: usize) -> PropSeqResult<()> {
    let leaf = &state.nodes[node_id];

    if !leaf.is_leaf() {
        Err(PropSeqErr::ExpectedLeaf)
    } else {
        Ok(())
    }
}

fn check_left(state: &PropSeqState, node_id: usize, f_id: usize) -> PropSeqResult<()> {
    check_node_id(state, node_id)?;
    check_leaf(state, node_id)?;
    if f_id >= state.nodes[node_id].left_formulas.len() {
        Err(PropSeqErr::InvalidFormulaId(f_id))
    } else {
        Ok(())
    }
}

fn check_right(state: &PropSeqState, node_id: usize, f_id: usize) -> PropSeqResult<()> {
    check_node_id(state, node_id)?;
    check_leaf(state, node_id)?;
    if f_id >= state.nodes[node_id].right_formulas.len() {
        Err(PropSeqErr::InvalidFormulaId(f_id))
    } else {
        Ok(())
    }
}

impl Serialize for PropSeqMove {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (ty, len, node_id, f_id) = match self {
            PropSeqMove::Ax(n) => ("Ax", 2, n, &0),
            PropSeqMove::NotL(n, f) => ("notLeft", 3, n, f),
            PropSeqMove::NotR(n, f) => ("notRight", 3, n, f),
            PropSeqMove::AndL(n, f) => ("andLeft", 3, n, f),
            PropSeqMove::AndR(n, f) => ("andRight", 3, n, f),
            PropSeqMove::OrL(n, f) => ("orLeft", 3, n, f),
            PropSeqMove::OrR(n, f) => ("orRight", 3, n, f),
            PropSeqMove::ImplL(n, f) => ("impLeft", 3, n, f),
            PropSeqMove::ImplR(n, f) => ("impRight", 3, n, f),
            PropSeqMove::Undo => ("undo", 1, &0, &0),
            PropSeqMove::Prune(n) => ("prune", 2, n, &0),
        };
        let mut state = serializer.serialize_struct("PropSeqMove", len)?;
        state.serialize_field("type", ty)?;
        if len > 1 {
            state.serialize_field("nodeID", node_id)?;
        }
        if len > 2 {
            state.serialize_field("listIndex", f_id)?;
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for PropSeqMove {
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
            #[serde(rename = "listIndex")]
            FormulaId,
        }

        struct MoveVisitor;

        impl<'de> Visitor<'de> for MoveVisitor {
            type Value = PropSeqMove;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct PropSeqMove")
            }

            fn visit_map<V>(self, mut map: V) -> Result<PropSeqMove, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut node_id: Option<usize> = None;
                let mut f_id: Option<usize> = None;

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
                        Field::FormulaId => {
                            if f_id.is_some() {
                                return Err(de::Error::duplicate_field("listIndex"));
                            }
                            f_id = Some(map.next_value()?);
                        }
                    }
                }

                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                let ty: &str = &ty;
                Ok(match ty {
                    "Ax" => {
                        PropSeqMove::Ax(node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?)
                    }
                    "notLeft" => PropSeqMove::NotL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "notRight" => PropSeqMove::NotR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "andLeft" => PropSeqMove::AndL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "andRight" => PropSeqMove::AndR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "orLeft" => PropSeqMove::OrL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "orRight" => PropSeqMove::OrR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "implLeft" => PropSeqMove::ImplL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "implRight" => PropSeqMove::ImplR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "undo" => PropSeqMove::Undo,
                    "prune" => PropSeqMove::Prune(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                    ),
                    _ => todo!(),
                })
            }
        }

        const FIELDS: &[&str] = &["type", "nodeID", "listIndex"];
        deserializer.deserialize_struct("PropSeqMove", FIELDS, MoveVisitor)
    }
}

impl Serialize for PropSeqState {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let mut state = serializer.serialize_struct("PropSeqState", 3)?;
        state.serialize_field("tree", &self.nodes)?;
        state.serialize_field("showOnlyApplicableRules", &self.show_only_applicable_rules)?;
        state.serialize_field("seal", &self.seal())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for PropSeqState {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "tree")]
            Tree,
            #[serde(rename = "showOnlyApplicableRules")]
            ShowOnlyApplicableRules,
            #[serde(rename = "seal")]
            Seal,
        }

        struct MoveVisitor;

        impl<'de> Visitor<'de> for MoveVisitor {
            type Value = PropSeqState;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct PropSeqState")
            }

            fn visit_map<V>(self, mut map: V) -> Result<PropSeqState, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut nodes: Option<Vec<SequentNode<PropSeqMove>>> = None;
                let mut show_only: Option<bool> = None;
                let mut seal: Option<String> = None;

                while let Some(key) = map.next_key()? {
                    match key {
                        Field::Tree => {
                            if nodes.is_some() {
                                return Err(de::Error::duplicate_field("tree"));
                            }
                            nodes = Some(map.next_value()?);
                        }
                        Field::ShowOnlyApplicableRules => {
                            if show_only.is_some() {
                                return Err(de::Error::duplicate_field("showOnlyApplicableRules"));
                            }
                            show_only = Some(map.next_value()?);
                        }
                        Field::Seal => {
                            if seal.is_some() {
                                return Err(de::Error::duplicate_field("seal"));
                            }
                            seal = Some(map.next_value()?);
                        }
                    }
                }

                let nodes = nodes.ok_or_else(|| de::Error::missing_field("tree"))?;
                let show_only_applicable_rules =
                    show_only.ok_or_else(|| de::Error::missing_field("showOnlyApplicableRules"))?;
                let seal = seal.ok_or_else(|| de::Error::missing_field("seal"))?;
                let s = PropSeqState {
                    nodes,
                    show_only_applicable_rules,
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

        const FIELDS: &[&str] = &["type", "nodeID", "listIndex"];
        deserializer.deserialize_struct("PropSeqMove", FIELDS, MoveVisitor)
    }
}
