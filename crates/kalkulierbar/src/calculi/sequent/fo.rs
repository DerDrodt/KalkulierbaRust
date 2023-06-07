use std::fmt;

use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{
    calculus::CloseMsg,
    logic::{
        fo::FOTerm,
        transform::signature::{SigAdherenceErr, Signature},
        unify::Substitution,
        LogicNode,
    },
    parse::{fo::parse_fo_term, sequent},
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
    AllL(usize, usize, FOTerm),
    AllR(usize, usize, Option<FOTerm>),
    ExL(usize, usize, Option<FOTerm>),
    ExR(usize, usize, FOTerm),
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
        let (left, right) = sequent::parse_fo(formula)?;
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
    replace_with: FOTerm,
) -> SequentResult<SequentState<FOSeqMove>> {
    check_left(&state, node_id, f_id)?;
    let node = &state.nodes[node_id];
    let formula = &node.left_formulas[f_id];
    if let LogicNode::All(var, c) = formula {
        check_adherence_to_sig(&replace_with, node)?;
        // TODO: signature check
        let nu = Substitution::from_value(*var, replace_with.clone());
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
                Some(FOSeqMove::AllL(node_id, f_id, replace_with)),
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
    replace_with: Option<FOTerm>,
) -> SequentResult<SequentState<FOSeqMove>> {
    check_right(&state, node_id, f_id)?;
    let node = &state.nodes[node_id];
    let formula = &node.right_formulas[f_id];
    if let LogicNode::All(var, child) = formula {
        // Check if swapVariable is a constant and not already in use in the current sequence
        let replace_with = replace_with.unwrap_or_else(|| get_fresh_constant(node, *var));
        let c = if let FOTerm::Const(c) = &replace_with {
            *c
        } else {
            return Err(SequentErr::ExpectedConst(replace_with));
        };

        if sig_of_sequent_node(node).has_const_or_fn(c) {
            return Err(SequentErr::SymbolAlreadyUsed(c));
        }
        let nu = Substitution::from_value(*var, replace_with.clone());
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
                Some(FOSeqMove::ExR(node_id, f_id, replace_with)),
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
    replace_with: Option<FOTerm>,
) -> SequentResult<SequentState<FOSeqMove>> {
    check_left(&state, node_id, f_id)?;
    let node = &state.nodes[node_id];
    let formula = &node.left_formulas[f_id];
    if let LogicNode::Ex(var, child) = formula {
        let replace_with = replace_with.unwrap_or_else(|| get_fresh_constant(node, *var));
        // Check if swapVariable is a constant and not already in use in the current sequence
        let c = if let FOTerm::Const(c) = &replace_with {
            *c
        } else {
            return Err(SequentErr::ExpectedConst(replace_with));
        };

        if sig_of_sequent_node(node).has_const_or_fn(c) {
            return Err(SequentErr::SymbolAlreadyUsed(c));
        }
        let nu = Substitution::from_value(*var, replace_with.clone());
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
                Some(FOSeqMove::ExR(node_id, f_id, replace_with)),
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
    replace_with: FOTerm,
) -> SequentResult<SequentState<FOSeqMove>> {
    check_right(&state, node_id, f_id)?;
    let node = &state.nodes[node_id];
    let formula = &node.right_formulas[f_id];
    if let LogicNode::Ex(var, c) = formula {
        check_adherence_to_sig(&replace_with, node)?;
        // Yes, this handling is weird, but I am mirroring the behavior of the Kotlin implementation, which is also weird
        let nu = Substitution::from_value(*var, replace_with.clone());
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
                Some(FOSeqMove::ExR(node_id, f_id, replace_with)),
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

fn sig_of_sequent_node(node: &SequentNode<FOSeqMove>) -> Signature {
    Signature::of_nodes(
        &node
            .left_formulas
            .iter()
            .chain(node.right_formulas.iter())
            .collect::<Vec<_>>(),
    )
}

fn check_adherence_to_sig(
    t: &FOTerm,
    node: &SequentNode<FOSeqMove>,
) -> Result<(), SigAdherenceErr> {
    if matches!(t, FOTerm::Const(_)) {
        return Ok(());
    }
    let sig = sig_of_sequent_node(node);
    sig.check(&t)?;
    Ok(())
}

fn get_fresh_constant(node: &SequentNode<FOSeqMove>, var_name: Symbol) -> FOTerm {
    let sig = sig_of_sequent_node(node);
    let base_name = var_name.to_string().to_lowercase();
    let mut idx = 0;
    while sig.has_const_or_fn(Symbol::intern(&format!("{base_name}_{idx}"))) {
        idx += 1;
    }

    let s = Symbol::intern(&format!("{base_name}_{idx}"));
    FOTerm::Const(s)
}

impl Serialize for FOSeqMove {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        let (ty, len, node_id, f_id, r_w) = match self {
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
            FOSeqMove::AllL(n, f, rw) => ("allLeft", 4, n, f, Some(rw)),
            FOSeqMove::AllR(n, f, Some(rw)) => ("allRight", 4, n, f, Some(rw)),
            FOSeqMove::AllR(n, f, None) => ("allRight", 4, n, f, None),
            FOSeqMove::ExL(n, f, Some(rw)) => ("exLeft", 4, n, f, Some(rw)),
            FOSeqMove::ExL(n, f, None) => ("exLeft", 4, n, f, None),
            FOSeqMove::ExR(n, f, rw) => ("exRight", 4, n, f, Some(rw)),
        };
        let mut state = serializer.serialize_struct("PropSeqMove", len)?;
        state.serialize_field("type", ty)?;
        if len > 1 {
            state.serialize_field("nodeID", node_id)?;
        }
        if len > 2 {
            state.serialize_field("listIndex", f_id)?;
        }
        if let Some(u) = r_w {
            state.serialize_field("instTerm", &u)?;
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
            #[serde(rename = "instTerm")]
            InstTerm,
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
                let mut inst_term: Option<String> = None;

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
                        Field::InstTerm => {
                            if inst_term.is_some() {
                                return Err(de::Error::duplicate_field("instTerm"));
                            }
                            inst_term = Some(map.next_value()?);
                        }
                    }
                }

                let ty = ty.ok_or_else(|| de::Error::missing_field("type"))?;
                let ty: &str = &ty;
                let inst_term = if let Some(t) = inst_term {
                    match parse_fo_term(&t) {
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
                        inst_term.ok_or_else(|| de::Error::missing_field("instTerm"))?,
                    ),
                    "allRight" => FOSeqMove::AllR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                        inst_term,
                    ),
                    "exLeft" => FOSeqMove::ExL(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                        inst_term,
                    ),
                    "exRight" => FOSeqMove::ExR(
                        node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?,
                        f_id.ok_or_else(|| de::Error::missing_field("listIndex"))?,
                        inst_term.ok_or_else(|| de::Error::missing_field("instTerm"))?,
                    ),
                    "undo" => FOSeqMove::Undo,
                    "prune" => {
                        FOSeqMove::Prune(node_id.ok_or_else(|| de::Error::missing_field("nodeID"))?)
                    }
                    _ => todo!(),
                })
            }
        }

        const FIELDS: &[&str] = &["type", "nodeID", "listIndex", "instTerm"];
        deserializer.deserialize_struct("FOSeqMove", FIELDS, MoveVisitor)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session;

    mod all_l {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        fn inst_term() -> FOTerm {
            FOTerm::Const("a".into())
        }

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("\\all X: R(X) |-", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::AllL(0, 0, inst_term())).unwrap();

                assert_eq!(2, s.nodes.len());
                assert!(s.nodes[0].parent.is_none());
                assert_eq!(vec![1], s.nodes[0].children);
                assert_eq!(0, s.nodes[1].parent.unwrap());
                assert!(s.nodes[1].right_formulas.is_empty());
                assert_eq!(2, s.nodes[1].left_formulas.len());

                let f1 = parse_fo_formula("\\all X: R(X)").unwrap();
                let f2 = parse_fo_formula("R(a)").unwrap();

                assert!(s.nodes[1].left_formulas[0].syn_eq(&f1));
                assert!(s.nodes[1].left_formulas[1].syn_eq(&f2));
            })
        }

        // See https://github.com/KalkulierbaR/kalkulierbar/issues/104
        #[test]
        fn complex() {
            session(|| {
                let s = FOSequent::parse_formula("|- \\all X: P(X) -> P(f(a))", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::ImplR(0, 0)).unwrap();
                let s = FOSequent::apply_move(
                    s,
                    FOSeqMove::AllL(
                        1,
                        0,
                        FOTerm::Function("f".into(), vec![FOTerm::Const("a".into())]),
                    ),
                )
                .unwrap();

                assert_eq!(3, s.nodes.len());
                assert_eq!(1, s.nodes[1].children.len());
                assert_eq!(2, s.nodes[1].children[0]);
                assert_eq!(1, s.nodes[2].parent.unwrap());

                assert_eq!(2, s.nodes[2].left_formulas.len());
                assert!(
                    s.nodes[2].left_formulas[0].syn_eq(&parse_fo_formula(r"\all X: P(X)").unwrap())
                );
                assert!(s.nodes[2].left_formulas[1].syn_eq(&parse_fo_formula("P(f(a))").unwrap()));

                assert_eq!(1, s.nodes[2].right_formulas.len());
                assert!(s.nodes[2].right_formulas[0].syn_eq(&parse_fo_formula("P(f(a))").unwrap()));
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("\\ex X: R(X) |-", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::AllL(0, 0, inst_term())).is_err());
            })
        }
    }

    mod all_r {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        fn inst_term() -> Option<FOTerm> {
            Some(FOTerm::Const("a".into()))
        }

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("\\all X: R(X)", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::AllR(0, 0, inst_term())).unwrap();

                assert_eq!(2, s.nodes.len());
                assert!(s.nodes[0].parent.is_none());
                assert_eq!(vec![1], s.nodes[0].children);
                assert_eq!(0, s.nodes[1].parent.unwrap());
                assert!(s.nodes[1].left_formulas.is_empty());
                assert_eq!(1, s.nodes[1].right_formulas.len());

                let f1 = parse_fo_formula("R(a)").unwrap();

                assert!(s.nodes[1].right_formulas[0].syn_eq(&f1));
            })
        }

        #[test]
        fn wrong_inst() {
            session(|| {
                let s = FOSequent::parse_formula("\\all X: R(X), P(a)", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::AllR(0, 0, inst_term())).is_err());
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("\\ex X: R(X)", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::AllR(0, 0, inst_term())).is_err());
            })
        }
    }

    mod and_l {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("(P(a) & P(b)) |-", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::AndL(0, 0)).unwrap();

                assert_eq!(2, s.nodes.len());
                assert!(s.nodes[0].parent.is_none());
                assert_eq!(vec![1], s.nodes[0].children);
                assert_eq!(0, s.nodes[1].parent.unwrap());
                assert!(s.nodes[1].right_formulas.is_empty());
                assert_eq!(2, s.nodes[1].left_formulas.len());

                let f1 = parse_fo_formula("P(a)").unwrap();
                let f2 = parse_fo_formula("P(b)").unwrap();

                assert!(s.nodes[1].left_formulas[0].syn_eq(&f1));
                assert!(s.nodes[1].left_formulas[1].syn_eq(&f2));
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = FOSequent::parse_formula("(P(a) & P(b)) |-", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::AndL(0, 0)).unwrap();

                assert_eq!(1, s.nodes[0].children.len());
                assert_eq!(0, s.nodes[1].parent.unwrap());
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("(P(a) & P(b))", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::AndL(0, 0)).is_err());
            })
        }
    }

    mod and_r {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("(P(a) & P(b)) & (P(b) |P(c))", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::AndR(0, 0)).unwrap();

                assert_eq!(3, s.nodes.len());

                let f1 = parse_fo_formula("P(a) & P(b)").unwrap();
                let f2 = parse_fo_formula("P(b) | P(c)").unwrap();

                assert!(s.nodes[1].right_formulas[0].syn_eq(&f1));
                assert!(s.nodes[2].right_formulas[0].syn_eq(&f2));
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = FOSequent::parse_formula("(P(a) & P(b)) & (P(b) |P(c))", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::AndR(0, 0)).unwrap();

                assert!(s.nodes[1].parent.is_some());
                assert_eq!(2, s.nodes[0].children.len());
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("(P(a) | P(b))", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::AndR(0, 0)).is_err());
            })
        }
    }

    mod ax {
        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) | !P(a)", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::OrR(0, 0)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(1, 1)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::Ax(2)).unwrap();

                assert!(s.nodes.iter().all(|n| n.is_closed));
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) | !P(a)", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::OrR(0, 0)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(1, 1)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::Ax(2)).unwrap();

                assert!(s.nodes[3].parent.is_some());
                assert_eq!(1, s.nodes[2].children.len());
            })
        }

        #[test]
        fn fail() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) | !P(a)", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::Ax(0)).is_err());
            })
        }
    }

    mod ex_l {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        fn inst_term() -> Option<FOTerm> {
            Some(FOTerm::Const("a".into()))
        }

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("\\ex X: R(X) |-", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::ExL(0, 0, inst_term())).unwrap();

                assert_eq!(2, s.nodes.len());
                assert!(s.nodes[0].parent.is_none());
                assert_eq!(vec![1], s.nodes[0].children);
                assert_eq!(0, s.nodes[1].parent.unwrap());
                assert!(s.nodes[1].right_formulas.is_empty());
                assert_eq!(1, s.nodes[1].left_formulas.len());

                let f1 = parse_fo_formula("R(a)").unwrap();

                assert!(s.nodes[1].left_formulas[0].syn_eq(&f1));
            })
        }

        #[test]
        fn wrong_inst() {
            session(|| {
                let s = FOSequent::parse_formula("\\ex X: R(X), P(a)", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::ExL(0, 0, inst_term())).is_err());
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("\\all X: R(X) |-", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::ExL(0, 0, inst_term())).is_err());
            })
        }
    }

    mod ex_r {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        fn inst_term() -> FOTerm {
            FOTerm::Const("a".into())
        }

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("\\ex X: R(X)", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::ExR(0, 0, inst_term())).unwrap();

                assert_eq!(2, s.nodes.len());
                assert!(s.nodes[0].parent.is_none());
                assert_eq!(vec![1], s.nodes[0].children);
                assert_eq!(0, s.nodes[1].parent.unwrap());
                assert!(s.nodes[1].left_formulas.is_empty());
                assert_eq!(2, s.nodes[1].right_formulas.len());

                let f1 = parse_fo_formula("\\ex X: R(X)").unwrap();
                let f2 = parse_fo_formula("R(a)").unwrap();

                assert!(s.nodes[1].right_formulas[0].syn_eq(&f1));
                assert!(s.nodes[1].right_formulas[1].syn_eq(&f2));
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("\\all X: R(X)", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::ExR(0, 0, inst_term())).is_err());
            })
        }
    }

    mod not_l {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("!(!P(a))", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(0, 0)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotL(1, 0)).unwrap();

                let f1 = parse_fo_formula("P(a)").unwrap();

                assert!(s.nodes[2].right_formulas[0].syn_eq(&f1));
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = FOSequent::parse_formula("!(!P(a))", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(0, 0)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotL(1, 0)).unwrap();

                assert_eq!(1, s.nodes[0].children.len());
                assert_eq!(0, s.nodes[1].parent.unwrap());
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) & !P(a)", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::NotL(0, 0)).is_err());
            })
        }
    }

    mod not_r {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("!P(a)", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(0, 0)).unwrap();

                let f1 = parse_fo_formula("P(a)").unwrap();

                assert!(s.nodes[1].left_formulas[0].syn_eq(&f1));
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = FOSequent::parse_formula("!P(a)", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(0, 0)).unwrap();

                assert_eq!(1, s.nodes[0].children.len());
                assert_eq!(0, s.nodes[1].parent.unwrap());
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) & !P(a)", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::NotR(0, 0)).is_err());
            })
        }
    }

    mod or_l {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("!((P(a) & P(b)) | (P(b) |P(c)))", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(0, 0)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::OrL(1, 0)).unwrap();

                let f1 = parse_fo_formula("P(a) & P(b)").unwrap();
                let f2 = parse_fo_formula("P(b) | P(c)").unwrap();

                assert!(s.nodes[2].left_formulas[0].syn_eq(&f1));
                assert!(s.nodes[3].left_formulas[0].syn_eq(&f2));
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = FOSequent::parse_formula("!((P(a) & P(b)) | (P(b) |P(c)))", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(0, 0)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::OrL(1, 0)).unwrap();

                assert_eq!(2, s.nodes[1].children.len());
                assert_eq!(0, s.nodes[1].parent.unwrap());
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("!((P(a) & P(b)) & (P(b) |P(c)))", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(0, 0)).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::OrL(1, 0)).is_err());
            })
        }
    }

    mod or_r {
        use crate::{parse::fo::parse_fo_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) | P(b)", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::OrR(0, 0)).unwrap();

                let f1 = parse_fo_formula("P(a)").unwrap();
                let f2 = parse_fo_formula("P(b)").unwrap();

                assert!(s.nodes[1].right_formulas[0].syn_eq(&f1));
                assert!(s.nodes[1].right_formulas[1].syn_eq(&f2));
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) | P(b)", None).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::OrR(0, 0)).unwrap();

                assert_eq!(1, s.nodes[0].children.len());
                assert_eq!(0, s.nodes[1].parent.unwrap());
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) & P(b)", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::OrR(0, 0)).is_err());
            })
        }
    }

    mod undo {
        use crate::tamper_protect::ProtectedState;

        use super::*;

        #[test]
        fn nothing_to_undo() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) | P(b)", None).unwrap();
                assert!(FOSequent::apply_move(s, FOSeqMove::Undo).is_err());
            })
        }

        #[test]
        fn one_child() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) | P(b)", None).unwrap();
                let i = s.compute_seal_info();
                let s = FOSequent::apply_move(s, FOSeqMove::OrR(0, 0)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::Undo).unwrap();

                assert_eq!(i, s.compute_seal_info());
            })
        }

        #[test]
        fn two_children() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) & P(b)", None).unwrap();
                let i = s.compute_seal_info();
                let s = FOSequent::apply_move(s, FOSeqMove::AndR(0, 0)).unwrap();
                let s = FOSequent::apply_move(s, FOSeqMove::Undo).unwrap();

                assert_eq!(i, s.compute_seal_info());
            })
        }

        #[test]
        fn complex() {
            session(|| {
                let s = FOSequent::parse_formula("P(a) | !P(a)", None).unwrap();
                let i0 = s.compute_seal_info();
                let s = FOSequent::apply_move(s, FOSeqMove::OrR(0, 0)).unwrap();
                let i1 = s.compute_seal_info();
                let s = FOSequent::apply_move(s, FOSeqMove::NotR(1, 1)).unwrap();
                let i2 = s.compute_seal_info();
                let s = FOSequent::apply_move(s, FOSeqMove::Ax(2)).unwrap();

                let s = FOSequent::apply_move(s, FOSeqMove::Undo).unwrap();
                assert_eq!(i2, s.compute_seal_info());
                let s = FOSequent::apply_move(s, FOSeqMove::Undo).unwrap();
                assert_eq!(i1, s.compute_seal_info());
                let s = FOSequent::apply_move(s, FOSeqMove::Undo).unwrap();
                assert_eq!(i0, s.compute_seal_info());
            })
        }
    }
}
