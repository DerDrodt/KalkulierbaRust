use std::fmt;

use serde::{Deserialize, Serialize};

pub mod fo;
pub mod prop;
mod util;

pub use fo::FOResolution as FO;
pub use prop::PropResolution as Prop;

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "UPPERCASE")]
pub enum VisualHelp {
    None,
    Highlight,
    Rearrange,
}

impl Default for VisualHelp {
    fn default() -> Self {
        Self::None
    }
}

impl fmt::Display for VisualHelp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VisualHelp::None => write!(f, "NONE"),
            VisualHelp::Highlight => write!(f, "HIGHLIGHT"),
            VisualHelp::Rearrange => write!(f, "REARRANGE"),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::{session, Calculus};

    // based on issue #67 in internal gitlab, now inaccessible
    #[test]
    fn issue67() {
        session(|| {
            let s = Prop::parse_formula("a,!b,c,!d,!e; b; d; e", None).unwrap();

            let s = Prop::apply_move(
                s,
                prop::PropResMove::Hyper(0, HashMap::from([(1, (1, 0)), (3, (2, 0)), (4, (3, 0))])),
            )
            .unwrap();
            assert_eq!(
                "{a, !b, c, !d, !e}, {b}, {d}, {e}, {a, c}",
                s.clause_set.to_string()
            );

            let s =
                FO::parse_formula("/all X: ((!R(c) | R(f) | !R(X)) & R(c) & R(X))", None).unwrap();

            let s = FO::apply_move(
                s,
                fo::FOResMove::Hyper(0, HashMap::from([(0, (1, 0)), (2, (2, 0))])),
            )
            .unwrap();

            assert_eq!(
                "{!R(c), R(f), !R(X_1)}, {R(c)}, {R(X_3)}, {R(f)}",
                s.clause_set.to_string()
            )
        })
    }
}
