use std::convert::TryFrom;
use std::fmt;

pub mod tableaux;

pub enum CalculusKind {
    PropTableaux,
}

impl fmt::Display for CalculusKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                CalculusKind::PropTableaux => "prop-tableaux",
            }
        )
    }
}

impl<'a> TryFrom<&'a str> for CalculusKind {
    type Error = &'static str;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        match s {
            "prop-tableaux" => Ok(CalculusKind::PropTableaux),
            _ => Err("Unknown calculus"),
        }
    }
}
