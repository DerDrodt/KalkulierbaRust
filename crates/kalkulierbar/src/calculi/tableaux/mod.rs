use serde::{Deserialize, Serialize};

use crate::clause::Atom;
use std::fmt;

pub mod fo;
pub mod nc;
pub mod prop;

pub use prop::PropTableaux as Prop;

pub type TableauxResult<T> = Result<T, TableauxErr>;

#[derive(Debug, Eq, PartialEq)]
pub enum TableauxErr {
    InvalidNodeId(usize),
    ExpectedLeaf(usize),
    AlreadyClosed(usize),
    ExpectedClosed(usize),
    LemmaRoot,
    LemmaLeaf(usize),
    ExpectedSiblings(usize, usize),
}

#[derive(Debug, Eq, PartialEq, Copy, Clone, Serialize, Deserialize)]
pub enum TableauxType {
    #[serde(rename = "UNCONNECTED")]
    Unconnected,
    #[serde(rename = "WEAKLYCONNECTED")]
    WeaklyConnected,
    #[serde(rename = "STRONGLYCONNECTED")]
    StronglyConnected,
}

impl TableauxType {
    pub fn is_unconnected(&self) -> bool {
        matches!(self, TableauxType::Unconnected)
    }

    pub fn is_weakly_connected(&self) -> bool {
        matches!(self, TableauxType::WeaklyConnected)
    }

    pub fn is_strongly_connected(&self) -> bool {
        matches!(self, TableauxType::StronglyConnected)
    }
}

impl fmt::Display for TableauxType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            TableauxType::Unconnected => "Unconnected",
            TableauxType::WeaklyConnected => "WeaklyConnected",
            TableauxType::StronglyConnected => "StronglyConnected",
        };
        write!(f, "{}", s)
    }
}

pub trait TableauxNode<L: fmt::Display + Clone>: Into<Atom<L>> + fmt::Display {
    fn parent(&self) -> Option<usize>;

    fn spelling(&self) -> String;

    fn literal_stem(&self) -> String;

    fn negated(&self) -> bool;

    fn is_closed(&self) -> bool;

    fn close_ref(&self) -> Option<usize>;

    fn children(&self) -> &Vec<usize>;

    fn lemma_source(&self) -> Option<usize>;

    fn is_leaf(&self) -> bool;

    fn mark_closed(&mut self);

    fn to_atom(&self) -> Atom<L>;
}
