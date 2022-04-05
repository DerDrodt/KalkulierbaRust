use std::fmt;

use serde::{
    de::{self, MapAccess, Visitor},
    ser::SerializeStruct,
    Deserialize, Serialize,
};

use crate::{calculus::CloseMsg, parse::sequent, Calculus};

use super::{
    apply_and_l, apply_and_r, apply_ax, apply_impl_l, apply_impl_r, apply_not_l, apply_not_r,
    apply_or_l, apply_or_r, apply_prune, apply_undo, CommonSequentMove, SequentErr, SequentNode,
    SequentParams, SequentState,
};

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

impl CommonSequentMove for PropSeqMove {
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

pub struct PropSequent;

impl<'f> Calculus<'f> for PropSequent {
    type Params = SequentParams;

    type State = SequentState<PropSeqMove>;

    type Move = PropSeqMove;

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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session;

    mod and_l {
        use crate::{parse::parse_prop_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = PropSequent::parse_formula("!(a & b)", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::AndL(1, 0)).unwrap();

                let f1 = parse_prop_formula("a ").unwrap();
                let f2 = parse_prop_formula("b ").unwrap();
                let n = &s.nodes[s.nodes.len() - 1];

                assert!(n.left_formulas[0].syn_eq(&f1));
                assert!(n.left_formulas[1].syn_eq(&f2));

                assert!(n.left_formulas[0].is_var());
                assert!(n.left_formulas[1].is_var())
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = PropSequent::parse_formula("!(a & b)", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).unwrap();
                assert!(s.nodes[0].parent.is_none());
                let s = PropSequent::apply_move(s, PropSeqMove::AndL(1, 0)).unwrap();
                assert_eq!(1, s.nodes[0].children.len());
                assert_eq!(0, s.nodes[1].parent.unwrap())
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = PropSequent::parse_formula("a & b", None).unwrap();
                assert!(PropSequent::apply_move(s, PropSeqMove::AndL(0, 0)).is_err());
            })
        }
    }

    mod and_r {
        use crate::{parse::parse_prop_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = PropSequent::parse_formula("(a & b) & (b |c)", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::AndR(0, 0)).unwrap();

                let f1 = parse_prop_formula("a & b").unwrap();
                let f2 = parse_prop_formula("b | c").unwrap();
                let n1 = &s.nodes[s.nodes.len() - 2];
                let n2 = &s.nodes[s.nodes.len() - 1];

                assert!(n1.right_formulas[0].syn_eq(&f1));
                assert!(n2.right_formulas[0].syn_eq(&f2));

                assert_eq!(3, s.nodes.len())
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = PropSequent::parse_formula("(a & b) & (b |c)", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::AndR(0, 0)).unwrap();
                assert!(s.nodes[0].parent.is_none());
                assert_eq!(2, s.nodes[0].children.len());
                assert_eq!(0, s.nodes[1].parent.unwrap())
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = PropSequent::parse_formula("(a & b) | (b |c)", None).unwrap();
                assert!(PropSequent::apply_move(s, PropSeqMove::AndR(0, 0)).is_err());
            })
        }
    }

    mod ax {

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = PropSequent::parse_formula("a | !a", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::OrR(0, 0)).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::NotR(1, 1)).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::Ax(2)).unwrap();

                assert!(s.nodes.iter().all(|n| n.is_closed))
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = PropSequent::parse_formula("a | !a", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::OrR(0, 0)).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::NotR(1, 1)).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::Ax(2)).unwrap();
                assert!(s.nodes[0].parent.is_none());
                assert_eq!(1, s.nodes[1].children.len());
                assert_eq!(1, s.nodes[2].parent.unwrap())
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = PropSequent::parse_formula("a | !a", None).unwrap();
                assert!(PropSequent::apply_move(s, PropSeqMove::Ax(0)).is_err());
            })
        }
    }

    mod not_l {
        use crate::{parse::parse_prop_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = PropSequent::parse_formula("!(!a)", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::NotL(1, 0)).unwrap();

                let f1 = parse_prop_formula("a").unwrap();
                let n = &s.nodes[2];

                assert!(n.right_formulas[0].syn_eq(&f1));
                assert!(n.right_formulas[0].is_var())
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = PropSequent::parse_formula("!(!a)", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::NotL(1, 0)).unwrap();

                assert!(s.nodes[0].parent.is_none());
                assert_eq!(1, s.nodes[1].children.len());
                assert_eq!(1, s.nodes[2].parent.unwrap())
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = PropSequent::parse_formula("a & !a", None).unwrap();
                assert!(PropSequent::apply_move(s, PropSeqMove::NotL(0, 0)).is_err());
            })
        }
    }

    mod not_r {
        use crate::{parse::parse_prop_formula, SynEq};

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = PropSequent::parse_formula("!a", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).unwrap();

                let f1 = parse_prop_formula("a").unwrap();
                let n = &s.nodes[1];

                assert!(n.left_formulas[0].syn_eq(&f1));
                assert!(n.left_formulas[0].is_var())
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = PropSequent::parse_formula("!a", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).unwrap();

                assert!(s.nodes[0].parent.is_none());
                assert_eq!(1, s.nodes[0].children.len());
                assert_eq!(0, s.nodes[1].parent.unwrap())
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = PropSequent::parse_formula("a & !a", None).unwrap();
                assert!(PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).is_err());
            })
        }
    }

    mod or_l {
        use crate::parse::parse_prop_formula;

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = PropSequent::parse_formula("!((a & b) | (b |c))", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::OrL(1, 0)).unwrap();

                let f1 = parse_prop_formula("a & b").unwrap();
                let f2 = parse_prop_formula("b | c").unwrap();
                let n1 = &s.nodes[2];
                let n2 = &s.nodes[3];

                assert_eq!(f1, n1.left_formulas[0]);
                assert_eq!(f2, n2.left_formulas[0]);
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = PropSequent::parse_formula("!((a & b) | (b |c))", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::OrL(1, 0)).unwrap();

                assert!(s.nodes[0].parent.is_none());
                assert_eq!(2, s.nodes[1].children.len());
                assert_eq!(1, s.nodes[2].parent.unwrap())
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = PropSequent::parse_formula("!((a & b) & (b |c))", None).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::NotR(0, 0)).unwrap();
                assert!(PropSequent::apply_move(s, PropSeqMove::OrL(1, 0)).is_err());
            })
        }
    }

    mod or_r {
        use crate::parse::parse_prop_formula;

        use super::*;

        #[test]
        fn basic() {
            session(|| {
                let s = PropSequent::parse_formula("a | b", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::OrR(0, 0)).unwrap();

                let f1 = parse_prop_formula("a").unwrap();
                let f2 = parse_prop_formula("b").unwrap();
                let n = &s.nodes[1];

                assert_eq!(f1, n.right_formulas[0]);
                assert_eq!(f2, n.right_formulas[1]);
            })
        }

        #[test]
        fn parent() {
            session(|| {
                let s = PropSequent::parse_formula("a | b", None).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::OrR(0, 0)).unwrap();

                assert!(s.nodes[0].parent.is_none());
                assert_eq!(1, s.nodes[0].children.len());
                assert_eq!(0, s.nodes[1].parent.unwrap())
            })
        }

        #[test]
        fn wrong_node() {
            session(|| {
                let s = PropSequent::parse_formula("a & b", None).unwrap();
                assert!(PropSequent::apply_move(s, PropSeqMove::OrR(0, 0)).is_err());
            })
        }
    }

    mod undo {
        use crate::tamper_protect::ProtectedState;

        use super::*;

        #[test]
        fn nothing_to_undo() {
            session(|| {
                let s = PropSequent::parse_formula("a | b", None).unwrap();

                assert!(PropSequent::apply_move(s, PropSeqMove::Undo).is_err())
            })
        }

        #[test]
        fn one_child() {
            session(|| {
                let s = PropSequent::parse_formula("a | b", None).unwrap();

                let h = s.compute_seal_info();

                let s = PropSequent::apply_move(s, PropSeqMove::OrR(0, 0)).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::Undo).unwrap();

                assert_eq!(h, s.compute_seal_info())
            })
        }

        #[test]
        fn two_children() {
            session(|| {
                let s = PropSequent::parse_formula("a & b", None).unwrap();
                let h = s.compute_seal_info();
                let s = PropSequent::apply_move(s, PropSeqMove::AndR(0, 0)).unwrap();
                let s = PropSequent::apply_move(s, PropSeqMove::Undo).unwrap();

                assert_eq!(h, s.compute_seal_info())
            })
        }

        #[test]
        fn complex() {
            session(|| {
                let s = PropSequent::parse_formula("a | !a", None).unwrap();
                let h0 = s.compute_seal_info();
                let s = PropSequent::apply_move(s, PropSeqMove::OrR(0, 0)).unwrap();
                let h1 = s.compute_seal_info();
                let s = PropSequent::apply_move(s, PropSeqMove::NotR(1, 1)).unwrap();
                let h2 = s.compute_seal_info();
                let s = PropSequent::apply_move(s, PropSeqMove::Ax(2)).unwrap();

                let s = PropSequent::apply_move(s, PropSeqMove::Undo).unwrap();
                assert_eq!(h2, s.compute_seal_info());
                let s = PropSequent::apply_move(s, PropSeqMove::Undo).unwrap();
                assert_eq!(h1, s.compute_seal_info());
                let s = PropSequent::apply_move(s, PropSeqMove::Undo).unwrap();
                assert_eq!(h0, s.compute_seal_info());
            })
        }
    }
}
