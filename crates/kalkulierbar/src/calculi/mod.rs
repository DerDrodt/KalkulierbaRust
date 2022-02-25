use std::convert::TryFrom;
use std::fmt;

pub mod dpll;
pub mod resolution;
pub mod tableaux;

pub enum CalculusKind {
    PropTableaux,
    FOTableaux,
    PropResolution,
    FOResolution,
    DPLL,
}

impl fmt::Display for CalculusKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                CalculusKind::PropTableaux => "prop-tableaux",
                CalculusKind::FOTableaux => "fo-tableaux",
                CalculusKind::PropResolution => "prop-resolution",
                CalculusKind::FOResolution => "fo-resolution",
                CalculusKind::DPLL => "dpll",
            }
        )
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
            _ => Err("Unknown calculus"),
        }
    }
}
