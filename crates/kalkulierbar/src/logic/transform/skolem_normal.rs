use std::fmt;

use crate::logic::{transform, LogicNode};

use super::{
    prenex_normal::{prenex_normal, PrenixNormalFormErr},
    skolem::{skolemize, SkolemizationErr},
    unique_vars::unique_vars,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SkolemNormalFormErr {
    NNFErr(&'static str),
    SkolemErr(SkolemizationErr),
    PrenexErr(PrenixNormalFormErr),
}

impl From<&'static str> for SkolemNormalFormErr {
    fn from(s: &'static str) -> Self {
        SkolemNormalFormErr::NNFErr(s)
    }
}

impl From<SkolemizationErr> for SkolemNormalFormErr {
    fn from(e: SkolemizationErr) -> Self {
        SkolemNormalFormErr::SkolemErr(e)
    }
}

impl From<PrenixNormalFormErr> for SkolemNormalFormErr {
    fn from(e: PrenixNormalFormErr) -> Self {
        SkolemNormalFormErr::PrenexErr(e)
    }
}

impl fmt::Display for SkolemNormalFormErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SkolemNormalFormErr::NNFErr(s) => write!(f, "{}", s),
            SkolemNormalFormErr::SkolemErr(e) => write!(f, "{}", e),
            SkolemNormalFormErr::PrenexErr(e) => write!(f, "{}", e),
        }
    }
}

pub fn skolem_normal_form(formula: LogicNode) -> Result<LogicNode, SkolemNormalFormErr> {
    let nnf = transform::negation_normal_form(formula)?;
    let uniq = unique_vars(nnf);
    let skol = skolemize(uniq)?;
    let pre = prenex_normal(skol)?;
    Ok(pre)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse::fo::parse_fo_formula, session};

    #[test]
    fn valid() {
        session(|| {
            let formulas = [
                ("R(a) -> R(b) | R(a) & !R(b)" , "(¬R(a) ∨ (R(b) ∨ (R(a) ∧ ¬R(b))))"),
        ("!(R(a) | R(b))" , "(¬R(a) ∧ ¬R(b))"),
        ("!(R(a) & R(b))" , "(¬R(a) ∨ ¬R(b))"),
        ("!(!R(a) <-> !R(a))" , "((¬R(a) ∧ R(a)) ∨ (R(a) ∧ ¬R(a)))"),
        ("!\\ex A : !(S(A) & !\\all B : (R(B) -> !R(A)))" , "(∀A: (S(A) ∧ (R(sk1(A)) ∧ R(A))))"),
        ("!\\all A : (P(A) <-> \\ex C : (R(A) <-> !R(C)))" ,
            "(∀C: ((P(sk1) ∧ ((R(sk1) ∧ R(C)) ∨ (¬R(sk1) ∧ ¬R(C)))) ∨ (¬P(sk1) ∧ ((¬R(sk1) ∨ ¬R(sk2)) ∧ (R(sk1) ∨ R(sk2))))))"),
        ("!\\ex A : R(A) -> !\\all B : !(R(B) | !R(B))", "(R(sk1) ∨ (R(sk2) ∨ ¬R(sk2)))")
            ];

            for (f, e) in formulas {
                let parsed = parse_fo_formula(f).unwrap();
                let nnf = skolem_normal_form(parsed).unwrap();
                assert_eq!(e, nnf.to_string());
            }
        })
    }
}
