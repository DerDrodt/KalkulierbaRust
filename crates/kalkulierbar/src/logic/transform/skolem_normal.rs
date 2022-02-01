use std::fmt;

use crate::logic::{transform, LogicNode};

use super::unique_vars::unique_vars;

#[derive(Debug, Clone, Copy)]
pub enum SkolemNormalFormErr {
    NNFErr(&'static str),
}

impl fmt::Display for SkolemNormalFormErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SkolemNormalFormErr::NNFErr(s) => write!(f, "{}", s),
        }
    }
}

pub fn skolem_normal_form(formula: LogicNode) -> Result<LogicNode, SkolemNormalFormErr> {
    let nnf = match transform::negation_normal_form(formula) {
        Ok(n) => n,
        Err(e) => return Err(SkolemNormalFormErr::NNFErr(e)),
    };
    let uniq = unique_vars(&nnf);

    Ok(uniq)
}
