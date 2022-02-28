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
    logic::{
        fo::FOTerm,
        transform::collectors::collect_symbols,
        unify::{try_to_parse_unifier, Unifier},
        LogicNode,
    },
    parse::sequent,
    Calculus, Symbol,
};

use super::{
    apply_and_l, apply_and_r, apply_ax, apply_impl_l, apply_impl_r, apply_not_l, apply_not_r,
    apply_or_l, apply_or_r, apply_prune, apply_undo, check_left, check_right, CommonSequentMove,
    SequentErr, SequentNode, SequentParams, SequentResult, SequentState,
};

#[derive(Debug, Clone)]
pub enum FOSeqMove {
    Ax(usize),
    NotL(usize, usize),
    NotR(usize, usize),
    AndL(usize, usize),
    AndR(usize, usize),
    OrL(usize, usize),
    OrR(usize, usize),
    ImplL(usize, usize),
    ImplR(usize, usize),
    AllL(usize, usize, Unifier),
    AllR(usize, usize, Unifier),
    ExL(usize, usize, Unifier),
    ExR(usize, usize, Unifier),
    Undo,
    Prune(usize),
}

impl CommonSequentMove for FOSeqMove {
    fn ax(node_id: usize) -> Self {
        Self::Ax(node_id)
    }

    fn not_l(node_id: usize, f_id: usize) -> Self {
        Self::NotL(node_id, f_id)
    }

    fn not_r(node_id: usize, f_id: usize) -> Self {
        Self::NotR(node_id, f_id)
    }

    fn and_l(node_id: usize, f_id: usize) -> Self {
        Self::AndL(node_id, f_id)
    }

    fn and_r(node_id: usize, f_id: usize) -> Self {
        Self::AndR(node_id, f_id)
    }

    fn or_l(node_id: usize, f_id: usize) -> Self {
        Self::OrL(node_id, f_id)
    }

    fn or_r(node_id: usize, f_id: usize) -> Self {
        Self::OrR(node_id, f_id)
    }

    fn impl_l(node_id: usize, f_id: usize) -> Self {
        Self::ImplL(node_id, f_id)
    }

    fn impl_r(node_id: usize, f_id: usize) -> Self {
        Self::ImplR(node_id, f_id)
    }
}

pub struct FOSequent;

impl<'f> Calculus<'f> for FOSequent {
    type Params = SequentParams;

    type State = SequentState<FOSeqMove>;

    type Move = FOSeqMove;

    type Error = SequentErr;

    fn parse_formula(
        formula: &'f str,
        params: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        let (left, right) = sequent::parse_prop(formula)?;
        Ok(SequentState::new(
            vec![SequentNode::new(None, left, right, None)],
            params.unwrap_or_default().show_only_applicable_rules,
        ))
    }

    fn apply_move(state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        match k_move {
            FOSeqMove::Ax(n) => apply_ax(state, n),
            FOSeqMove::NotL(node, formula) => apply_not_l(state, node, formula),
            FOSeqMove::NotR(node, formula) => apply_not_r(state, node, formula),
            FOSeqMove::AndL(node, formula) => apply_and_l(state, node, formula),
            FOSeqMove::AndR(node, formula) => apply_and_r(state, node, formula),
            FOSeqMove::OrL(node, formula) => apply_or_l(state, node, formula),
            FOSeqMove::OrR(node, formula) => apply_or_r(state, node, formula),
            FOSeqMove::ImplL(node, formula) => apply_impl_l(state, node, formula),
            FOSeqMove::ImplR(node, formula) => apply_impl_r(state, node, formula),
            FOSeqMove::Undo => apply_undo(state),
            FOSeqMove::Prune(node) => apply_prune(state, node),
            FOSeqMove::AllL(node, formula, u) => apply_all_l(state, node, formula, u),
            FOSeqMove::AllR(node, formula, u) => apply_all_r(state, node, formula, u),
            FOSeqMove::ExL(node, formula, u) => apply_ex_l(state, node, formula, u),
            FOSeqMove::ExR(node, formula, u) => apply_ex_r(state, node, formula, u),
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

fn apply_all_l(
    mut state: SequentState<FOSeqMove>,
    node_id: usize,
    f_id: usize,
    mut u: Unifier,
) -> SequentResult<SequentState<FOSeqMove>> {
    check_left(&state, node_id, f_id)?;
    let node = &state.nodes[node_id];
    let formula = &node.left_formulas[f_id];
    if let LogicNode::All(var, c) = formula {
        // Yes, this handling is weird, but I am mirroring the behavior of the Kotlin implementation, which is also weird
        let replace_with = if let Some(t) = u.remove(var) {
            t
        } else {
            todo!()
        };
        let nu = Unifier::from_value(*var, replace_with);
        let new_f = c.instantiate(&nu);

        // Add newFormula to the left hand side of the sequence
        let mut new_l = node.left_formulas.clone();
        new_l.push(new_f);
        let new_r = node.right_formulas.clone();

        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                new_l,
                new_r,
                Some(FOSeqMove::AllL(node_id, f_id, u)),
            ),
        );

        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable(
            "allLeft",
            "universal quantifier",
        ))
    }
}

fn apply_all_r(
    mut state: SequentState<FOSeqMove>,
    node_id: usize,
    f_id: usize,
    mut u: Unifier,
) -> SequentResult<SequentState<FOSeqMove>> {
    check_right(&state, node_id, f_id)?;
    let node = &state.nodes[node_id];
    let formula = &node.right_formulas[f_id];
    if let LogicNode::All(var, child) = formula {
        // Yes, this handling is weird, but I am mirroring the behavior of the Kotlin implementation, which is also weird
        let replace_with = if let Some(t) = u.remove(var) {
            t
        } else {
            todo!()
        };
        // Check if swapVariable is a constant and not already in use in the current sequence
        let c = if let FOTerm::Const(c) = &replace_with {
            *c
        } else {
            return Err(SequentErr::ExpectedConst(replace_with));
        };

        if node
            .left_formulas
            .iter()
            .chain(&node.right_formulas)
            .flat_map(|n| collect_symbols(n))
            .collect::<HashSet<_>>()
            .contains(&c)
        {
            return Err(SequentErr::SymbolAlreadyUsed(c));
        }
        let nu = Unifier::from_value(*var, replace_with);
        let new_f = child.instantiate(&nu);

        // Add newFormula to the left hand side of the sequence
        let new_l = node.left_formulas.clone();
        let mut new_r = node.right_formulas.clone();
        new_r.remove(f_id);
        new_r.insert(f_id, new_f);

        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                new_l,
                new_r,
                Some(FOSeqMove::ExR(node_id, f_id, u)),
            ),
        );

        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable(
            "allRight",
            "universal quantifier",
        ))
    }
}

fn apply_ex_l(
    mut state: SequentState<FOSeqMove>,
    node_id: usize,
    f_id: usize,
    mut u: Unifier,
) -> SequentResult<SequentState<FOSeqMove>> {
    check_left(&state, node_id, f_id)?;
    let node = &state.nodes[node_id];
    let formula = &node.left_formulas[f_id];
    if let LogicNode::Ex(var, child) = formula {
        // Yes, this handling is weird, but I am mirroring the behavior of the Kotlin implementation, which is also weird
        let replace_with = if let Some(t) = u.remove(var) {
            t
        } else {
            todo!()
        };
        // Check if swapVariable is a constant and not already in use in the current sequence
        let c = if let FOTerm::Const(c) = &replace_with {
            *c
        } else {
            return Err(SequentErr::ExpectedConst(replace_with));
        };

        if node
            .left_formulas
            .iter()
            .chain(&node.right_formulas)
            .flat_map(|n| collect_symbols(n))
            .collect::<HashSet<_>>()
            .contains(&c)
        {
            return Err(SequentErr::SymbolAlreadyUsed(c));
        }
        let nu = Unifier::from_value(*var, replace_with);
        let new_f = child.instantiate(&nu);

        // Add newFormula to the left hand side of the sequence
        let mut new_l = node.left_formulas.clone();
        new_l.remove(f_id);
        new_l.insert(f_id, new_f);
        let new_r = node.right_formulas.clone();

        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                new_l,
                new_r,
                Some(FOSeqMove::ExR(node_id, f_id, u)),
            ),
        );

        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable(
            "exLeft",
            "existential quantifier",
        ))
    }
}

fn apply_ex_r(
    mut state: SequentState<FOSeqMove>,
    node_id: usize,
    f_id: usize,
    mut u: Unifier,
) -> SequentResult<SequentState<FOSeqMove>> {
    check_right(&state, node_id, f_id)?;
    let node = &state.nodes[node_id];
    let formula = &node.right_formulas[f_id];
    if let LogicNode::Ex(var, c) = formula {
        // Yes, this handling is weird, but I am mirroring the behavior of the Kotlin implementation, which is also weird
        let replace_with = if let Some(t) = u.remove(var) {
            t
        } else {
            todo!()
        };
        let nu = Unifier::from_value(*var, replace_with);
        let new_f = c.instantiate(&nu);

        // Add newFormula to the left hand side of the sequence
        let new_l = node.left_formulas.clone();
        let mut new_r = node.right_formulas.clone();
        new_r.push(new_f);

        state.add_node(
            node_id,
            SequentNode::new(
                Some(node_id),
                new_l,
                new_r,
                Some(FOSeqMove::ExR(node_id, f_id, u)),
            ),
        );

        Ok(state)
    } else {
        Err(SequentErr::RuleNotApplicable(
            "exRight",
            "existential quantifier",
        ))
    }
}

impl Serialize for FOSeqMove {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (ty, len, node_id, f_id, u) = match self {
            FOSeqMove::Ax(n) => ("Ax", 2, n, &0, None),
            FOSeqMove::NotL(n, f) => ("notLeft", 3, n, f, None),
            FOSeqMove::NotR(n, f) => ("notRight", 3, n, f, None),
            FOSeqMove::AndL(n, f) => ("andLeft", 3, n, f, None),
            FOSeqMove::AndR(n, f) => ("andRight", 3, n, f, None),
            FOSeqMove::OrL(n, f) => ("orLeft", 3, n, f, None),
            FOSeqMove::OrR(n, f) => ("orRight", 3, n, f, None),
            FOSeqMove::ImplL(n, f) => ("impLeft", 3, n, f, None),
            FOSeqMove::ImplR(n, f) => ("impRight", 3, n, f, None),
            FOSeqMove::Undo => ("undo", 1, &0, &0, None),
            FOSeqMove::Prune(n) => ("prune", 2, n, &0, None),
            FOSeqMove::AllL(n, f, u) => ("allLeft", 4, n, f, Some(u)),
            FOSeqMove::AllR(n, f, u) => ("allRight", 4, n, f, Some(u)),
            FOSeqMove::ExL(n, f, u) => ("exLeft", 4, n, f, Some(u)),
            FOSeqMove::ExR(n, f, u) => ("exRight", 4, n, f, Some(u)),
        };
        let mut state = serializer.serialize_struct("PropSeqMove", len)?;
        state.serialize_field("type", ty)?;
        if len > 1 {
            state.serialize_field("nodeID", node_id)?;
        }
        if len > 2 {
            state.serialize_field("listIndex", f_id)?;
        }
        if let Some(u) = u {
            state.serialize_field("varAssign", u)?;
        }
        state.end()
    }
}

impl<'de> Deserialize<'de> for FOSeqMove {
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
            #[serde(rename = "varAssign")]
            VarAssign,
        }

        struct MoveVisitor;

        impl<'de> Visitor<'de> for MoveVisitor {
            type Value = FOSeqMove;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("struct FOSeqMove")
            }

            fn visit_map<V>(self, mut map: V) -> Result<FOSeqMove, V::Error>
            where
                V: MapAccess<'de>,
            {
                let mut ty: Option<String> = None;
                let mut node_id: Option<usize> = None;
                let mut f_id: Option<usize> = None;
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
                        Field::FormulaId => {
                            if f_id.is_some() {
                                return Err(de::Error::duplicate_field("listIndex"));
                            }
                            f_id = Some(map.next_value()?);
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
                let u = if let Some(h) = var_assign {
                    match try_to_parse_unifier(h) {
                        Ok(u) => Some(u),
                        Err(e) => return Err(de::Error::custom(e.to_string())),
                    }
                } else {
                    None
                };
                Ok(match ty {
                    "Ax" => {
                        FOSeqMove::Ax(node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?)
                    }
                    "notLeft" => FOSeqMove::NotL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "notRight" => FOSeqMove::NotR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "andLeft" => FOSeqMove::AndL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "andRight" => FOSeqMove::AndR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "orLeft" => FOSeqMove::OrL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "orRight" => FOSeqMove::OrR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "implLeft" => FOSeqMove::ImplL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "implRight" => FOSeqMove::ImplR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                    ),
                    "allLeft" => FOSeqMove::AllL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                        u.ok_or_else(|| de::Error::missing_field("varAssign"))?,
                    ),
                    "allRight" => FOSeqMove::AllR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                        u.ok_or_else(|| de::Error::missing_field("varAssign"))?,
                    ),
                    "exLeft" => FOSeqMove::ExL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                        u.ok_or_else(|| de::Error::missing_field("varAssign"))?,
                    ),
                    "exRight" => FOSeqMove::ExR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                        u.ok_or_else(|| de::Error::missing_field("varAssign"))?,
                    ),
                    "undo" => FOSeqMove::Undo,
                    "prune" => {
                        FOSeqMove::Prune(node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?)
                    }
                    _ => todo!(),
                })
            }
        }

        const FIELDS: &[&str] = &["type", "nodeID", "listIndex", "varAssign"];
        deserializer.deserialize_struct("FOSeqMove", FIELDS, MoveVisitor)
    }
}
