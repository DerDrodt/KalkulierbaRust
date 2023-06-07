use std::{fmt, marker::PhantomData};

use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{
    logic::{fo::FOTerm, transform::signature::SigAdherenceErr, LogicNode},
    parse::ParseErr,
    tamper_protect::ProtectedState,
    Symbol, SynEq,
};

pub mod fo;
pub mod prop;

#[derive(Debug, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
#[serde(default)]
pub struct SequentParams {
    pub show_only_applicable_rules: bool,
}

#[derive(Debug)]
pub enum SequentErr {
    ParseErr(ParseErr),
    InvalidNodeId(usize),
    ExpectedLeaf,
    AxNotApplicable,
    InvalidFormulaId(usize),
    RuleNotApplicable(&'static str, &'static str),
    NothingToUndo,
    ExpectedConst(FOTerm),
    SymbolAlreadyUsed(Symbol),
    SigAdherenceErr(SigAdherenceErr),
}

impl From<ParseErr> for SequentErr {
    fn from(e: ParseErr) -> Self {
        Self::ParseErr(e)
    }
}

impl From<SigAdherenceErr> for SequentErr {
    fn from(value: SigAdherenceErr) -> Self {
        Self::SigAdherenceErr(value)
    }
}

impl fmt::Display for SequentErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SequentErr::ParseErr(e) => fmt::Display::fmt(e, f),
            SequentErr::SigAdherenceErr(e) => fmt::Display::fmt(e, f),
            SequentErr::InvalidNodeId(n) => write!(f, "Node with ID {n} does not exist"),
            SequentErr::ExpectedLeaf => write!(f, "Rules can only be applied on leaf level"),
            SequentErr::AxNotApplicable => write!(
                f,
                "Axiom rule needs two identical formulas on both sides to be applied"
            ),
            SequentErr::InvalidFormulaId(id) => {
                write!(
                    f,
                    "Formula with ID {id} does not exist in the selected node"
                )
            }
            SequentErr::RuleNotApplicable(rule, expected) => {
                if expected.starts_with('i') {
                    write!(f, "Rule {rule} can only be applied on an {expected}")
                } else {
                    write!(f, "Rule {rule} can only be applied on a {expected}")
                }
            }
            SequentErr::NothingToUndo => write!(f, "No move to undo"),
            SequentErr::ExpectedConst(t) => write!(f, "Expected a constant, got {t}"),
            SequentErr::SymbolAlreadyUsed(s) => write!(f, "Identifier '{s}' is already in use"),
        }
    }
}

pub type SequentResult<T> = Result<T, SequentErr>;

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SequentNode<M> {
    parent: Option<usize>,
    children: Vec<usize>,
    left_formulas: Vec<LogicNode>,
    right_formulas: Vec<LogicNode>,
    is_closed: bool,
    last_move: Option<M>,
}

impl<M> SequentNode<M> {
    pub fn new(
        parent: Option<usize>,
        left_formulas: Vec<LogicNode>,
        right_formulas: Vec<LogicNode>,
        last_move: Option<M>,
    ) -> Self {
        Self {
            parent,
            children: vec![],
            left_formulas: dedupe(left_formulas),
            right_formulas: dedupe(right_formulas),
            is_closed: false,
            last_move,
        }
    }

    pub fn is_leaf(&self) -> bool {
        self.children.is_empty()
    }
}

impl<M> fmt::Display for SequentNode<M> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let left = self
            .left_formulas
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<String>>()
            .join(", ");
        let right = self
            .right_formulas
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, "{left} ⊢ {right}")
    }
}

fn dedupe(formulas: Vec<LogicNode>) -> Vec<LogicNode> {
    let mut v = Vec::new();
    for f in formulas {
        if !v.contains(&f) {
            v.push(f);
        }
    }
    v
}

trait CommonSequentMove {
    fn ax(node_id: usize) -> Self;
    fn not_l(node_id: usize, f_id: usize) -> Self;
    fn not_r(node_id: usize, f_id: usize) -> Self;
    fn and_l(node_id: usize, f_id: usize) -> Self;
    fn and_r(node_id: usize, f_id: usize) -> Self;
    fn or_l(node_id: usize, f_id: usize) -> Self;
    fn or_r(node_id: usize, f_id: usize) -> Self;
    fn impl_l(node_id: usize, f_id: usize) -> Self;
    fn impl_r(node_id: usize, f_id: usize) -> Self;
}

fn apply_ax<M: CommonSequentMove>(
    mut state: SequentState<M>,
    node_id: usize,
) -> SequentResult<SequentState<M>> {
    check_node_id(&state, node_id)?;
    check_leaf(&state, node_id)?;
    let leaf = &state.nodes[node_id];

    for l in &leaf.left_formulas {
        if leaf.right_formulas.iter().any(|r| r.syn_eq(l)) {
            let ax = SequentNode::new(Some(node_id), vec![], vec![], Some(M::ax(node_id)));
            let idx = state.add_node(node_id, ax);
            state.set_node_closed(idx);
            return Ok(state);
        }
    }

    Err(SequentErr::AxNotApplicable)
}

fn apply_not_l<M: CommonSequentMove>(
    mut state: SequentState<M>,
    node_id: usize,
    f_id: usize,
) -> SequentResult<SequentState<M>> {
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
            SequentNode::new(Some(node_id), nl, nr, Some(M::not_l(node_id, f_id))),
        );
        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable("notLeft", "negation"))
    }
}

fn apply_not_r<M: CommonSequentMove>(
    mut state: SequentState<M>,
    node_id: usize,
    f_id: usize,
) -> SequentResult<SequentState<M>> {
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
            SequentNode::new(Some(node_id), nl, nr, Some(M::not_r(node_id, f_id))),
        );
        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable("notRight", "negation"))
    }
}

fn apply_and_l<M: CommonSequentMove>(
    mut state: SequentState<M>,
    node_id: usize,
    f_id: usize,
) -> SequentResult<SequentState<M>> {
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
            SequentNode::new(Some(node_id), nl, nr, Some(M::and_l(node_id, f_id))),
        );
        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable("andLeft", "conjunction"))
    }
}

fn apply_and_r<M: CommonSequentMove>(
    mut state: SequentState<M>,
    node_id: usize,
    f_id: usize,
) -> SequentResult<SequentState<M>> {
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
            SequentNode::new(Some(node_id), nl.clone(), nr, Some(M::and_r(node_id, f_id))),
        );

        r_fs.remove(f_id);
        r_fs.insert(f_id, r);
        state.add_node(
            node_id,
            SequentNode::new(Some(node_id), nl, r_fs, Some(M::and_r(node_id, f_id))),
        );
        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable("andRight", "conjunction"))
    }
}

fn apply_or_l<M: CommonSequentMove>(
    mut state: SequentState<M>,
    node_id: usize,
    f_id: usize,
) -> SequentResult<SequentState<M>> {
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
            SequentNode::new(Some(node_id), nl, nr.clone(), Some(M::or_l(node_id, f_id))),
        );

        l_fs.remove(f_id);
        l_fs.insert(f_id, r);
        state.add_node(
            node_id,
            SequentNode::new(Some(node_id), l_fs, nr, Some(M::or_l(node_id, f_id))),
        );
        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable("orLeft", "disjunction"))
    }
}

fn apply_or_r<M: CommonSequentMove>(
    mut state: SequentState<M>,
    node_id: usize,
    f_id: usize,
) -> SequentResult<SequentState<M>> {
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
            SequentNode::new(Some(node_id), nl, nr, Some(M::or_r(node_id, f_id))),
        );
        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable("orRight", "disjunction"))
    }
}

fn apply_impl_l<M: CommonSequentMove>(
    mut state: SequentState<M>,
    node_id: usize,
    f_id: usize,
) -> SequentResult<SequentState<M>> {
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
            SequentNode::new(Some(node_id), nlc_l, nlc_r, Some(M::impl_l(node_id, f_id))),
        );
        state.add_node(
            node_id,
            SequentNode::new(Some(node_id), nrc_l, nrc_r, Some(M::impl_l(node_id, f_id))),
        );

        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable("implLeft", "implication"))
    }
}

fn apply_impl_r<M: CommonSequentMove>(
    mut state: SequentState<M>,
    node_id: usize,
    f_id: usize,
) -> SequentResult<SequentState<M>> {
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
            SequentNode::new(Some(node_id), nl, nr, Some(M::impl_r(node_id, f_id))),
        );

        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable("implRight", "implication"))
    }
}

fn apply_undo<M>(state: SequentState<M>) -> SequentResult<SequentState<M>> {
    if state.nodes.len() <= 1 {
        return Err(SequentErr::NothingToUndo);
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
            let p = *p;
            state.nodes[p].is_closed = false;
            n_id = p;
        } else {
            break;
        }
    }

    Ok(state)
}

fn apply_prune<M>(mut state: SequentState<M>, node_id: usize) -> SequentResult<SequentState<M>> {
    check_node_id(&state, node_id)?;

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

fn check_node_id<M>(state: &SequentState<M>, node_id: usize) -> SequentResult<()> {
    if node_id >= state.nodes.len() {
        Err(SequentErr::InvalidNodeId(node_id))
    } else {
        Ok(())
    }
}

fn check_leaf<M>(state: &SequentState<M>, node_id: usize) -> SequentResult<()> {
    let leaf = &state.nodes[node_id];

    if !leaf.is_leaf() {
        Err(SequentErr::ExpectedLeaf)
    } else {
        Ok(())
    }
}

fn check_left<M>(state: &SequentState<M>, node_id: usize, f_id: usize) -> SequentResult<()> {
    check_node_id(state, node_id)?;
    check_leaf(state, node_id)?;
    if f_id >= state.nodes[node_id].left_formulas.len() {
        Err(SequentErr::InvalidFormulaId(f_id))
    } else {
        Ok(())
    }
}

fn check_right<M>(state: &SequentState<M>, node_id: usize, f_id: usize) -> SequentResult<()> {
    check_node_id(state, node_id)?;
    check_leaf(state, node_id)?;
    if f_id >= state.nodes[node_id].right_formulas.len() {
        Err(SequentErr::InvalidFormulaId(f_id))
    } else {
        Ok(())
    }
}

#[derive(Debug)]
pub struct SequentState<M> {
    nodes: Vec<SequentNode<M>>,
    show_only_applicable_rules: bool,
}

impl<M> SequentState<M> {
    pub fn new(nodes: Vec<SequentNode<M>>, show_only_applicable_rules: bool) -> Self {
        Self {
            nodes,
            show_only_applicable_rules,
        }
    }

    pub fn add_node(&mut self, parent_id: usize, n: SequentNode<M>) -> usize {
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

impl<M> ProtectedState for SequentState<M> {
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

impl<M> Serialize for SequentState<M>
where
    M: Serialize,
{
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

impl<'de, M> Deserialize<'de> for SequentState<M>
where
    M: Deserialize<'de>,
{
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

        struct StateVisitor<M> {
            _p: PhantomData<M>,
        }

        impl<'de, M: Deserialize<'de>> Visitor<'de> for StateVisitor<M> {
            type Value = SequentState<M>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct SequentState")
            }

            fn visit_map<V>(self, mut map: V) -> Result<SequentState<M>, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut nodes: Option<Vec<SequentNode<M>>> = None;
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
                let s = SequentState {
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

        const FIELDS: &[&str] = &["tree", "showOnlyApplicableRules", "seal"];
        deserializer.deserialize_struct("SequentState", FIELDS, StateVisitor { _p: PhantomData })
    }
}
