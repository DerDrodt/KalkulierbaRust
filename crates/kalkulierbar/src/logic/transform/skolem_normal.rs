use crate::logic::{transform, LogicNode};

pub enum SkolemNormalFormErr {
    NNFErr(&'static str),
}

pub fn skolem_normal_form(formula: LogicNode) -> Result<LogicNode, SkolemNormalFormErr> {
    let nnf = match transform::negation_normal_form(formula) {
        Ok(n) => n,
        Err(e) => return Err(SkolemNormalFormErr::NNFErr(e)),
    };

    Ok(nnf)
}
