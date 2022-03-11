use std::convert::TryFrom;
use std::fmt;

use serde::{Deserialize, Serialize};

pub mod dpll;
pub mod resolution;
pub mod sequent;
pub mod tableaux;

#[derive(Debug, Deserialize, Clone, Copy, PartialEq, Eq)]
#[serde(try_from = "&str")]
pub enum CalculusKind {
    PropTableaux,
    FOTableaux,
    PropResolution,
    FOResolution,
    DPLL,
    NCTableaux,
    PropSequent,
    FOSequent,
}

impl CalculusKind {
    pub fn to_str(&self) -> &'static str {
        match self {
            CalculusKind::PropTableaux => "prop-tableaux",
            CalculusKind::FOTableaux => "fo-tableaux",
            CalculusKind::PropResolution => "prop-resolution",
            CalculusKind::FOResolution => "fo-resolution",
            CalculusKind::DPLL => "dpll",
            CalculusKind::NCTableaux => "nc-tableaux",
            CalculusKind::PropSequent => "prop-sequent",
            CalculusKind::FOSequent => "fo-sequent",
        }
    }
}

impl fmt::Display for CalculusKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_str())
    }
}

impl<'a> TryFrom<&'a str> for CalculusKind {
    type Error = &'static str;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        match s {
            "prop-tableaux" => Ok(CalculusKind::PropTableaux),
            "fo-tableaux" => Ok(CalculusKind::FOTableaux),
            "prop-resolution" => Ok(CalculusKind::PropResolution),
            "fo-resolution" => Ok(CalculusKind::FOResolution),
            "dpll" => Ok(CalculusKind::DPLL),
            "nc-tableaux" => Ok(CalculusKind::NCTableaux),
            "prop-sequent" => Ok(CalculusKind::PropSequent),
            "fo-sequent" => Ok(CalculusKind::FOSequent),
            _ => Err("Unknown calculus"),
        }
    }
}

impl Serialize for CalculusKind {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(self.to_str())
    }
}
