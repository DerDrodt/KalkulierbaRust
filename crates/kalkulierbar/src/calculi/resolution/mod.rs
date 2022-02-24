use std::fmt;

use serde::{Deserialize, Serialize};

pub mod fo;
pub mod prop;
mod util;

#[derive(Deserialize, Serialize)]
#[serde(rename_all = "UPPERCASE")]
pub enum VisualHelp {
    None,
    Hightlight,
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
            VisualHelp::Hightlight => write!(f, "HIGHLIGHT"),
            VisualHelp::Rearrange => write!(f, "REARRANGE"),
        }
    }
}
