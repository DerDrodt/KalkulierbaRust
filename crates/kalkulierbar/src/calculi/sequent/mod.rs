use std::fmt;

use serde::{Deserialize, Serialize};

use crate::logic::LogicNode;

pub mod fo;
pub mod prop;

#[derive(Debug, Serialize, Deserialize, Default)]
#[serde(rename_all = "camelCase")]
#[serde(default)]
pub struct SequentParams {
    pub show_only_applicable_rules: bool,
}

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
