use serde::{Deserialize, Serialize};

use crate::calculus::CloseMsg;
use crate::clause::{Atom, Clause};
use std::fmt;

pub mod fo;
pub mod prop;

pub use prop::PropTableaux as Prop;

pub type TableauxResult<T> = Result<T, TableauxErr>;

#[derive(Debug, Eq, PartialEq)]
pub enum TableauxErr {
    InvalidNodeId(usize),
    ExpectedLeaf(usize),
    AlreadyClosed(usize),
    ExpectedClosed(usize),
    LemmaRoot(usize),
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

pub trait TableauxState<L>
where
    L: fmt::Display + Clone,
{
    type Node: TableauxNode<L> + Into<Atom<L>>;

    fn root(&self) -> &Self::Node {
        self.node(0).unwrap()
    }

    fn regular(&self) -> bool;

    fn nodes(&self) -> &Vec<Self::Node>;

    fn node(&self, id: usize) -> TableauxResult<&Self::Node>;

    fn node_mut(&mut self, id: usize) -> TableauxResult<&mut Self::Node>;

    fn node_is_parent_of(&self, parent_id: usize, child: usize) -> TableauxResult<bool> {
        let child = self.node(child)?;
        if let Some(parent) = child.parent() {
            if parent == parent_id {
                Ok(true)
            } else {
                self.node_is_parent_of(parent_id, parent)
            }
        } else {
            Ok(false)
        }
    }

    fn mark_node_closed(&mut self, leaf: usize) {
        let mut id = leaf;
        while self.is_leaf(id) || self.all_children_closed(id) {
            let node = &mut self.node_mut(id).unwrap();
            node.mark_closed();
            if node.parent().is_none() {
                break;
            }
            id = node.parent().unwrap();
        }
    }

    fn is_leaf(&self, id: usize) -> bool {
        match self.node(id) {
            Ok(n) => n.is_leaf(),
            Err(_) => false,
        }
    }

    fn all_children_closed(&self, id: usize) -> bool {
        match self.node(id) {
            Ok(n) => n.children().iter().all(|e| self.nodes()[*e].is_closed()),
            Err(_) => false,
        }
    }

    fn get_close_msg(&self) -> CloseMsg {
        let msg = if self.root().is_closed() {
            "The proof tree is not closed".to_string()
        } else {
            "The proof is closed and valid in a $connectedness ${regularity}tableaux $withWithoutBT backtracking".to_string()
        };

        CloseMsg {
            closed: self.root().is_closed(),
            msg,
        }
    }

    fn get_lemma(&self, leaf_id: usize, lemma_id: usize) -> TableauxResult<Atom<L>> {
        let leaf = self.node(leaf_id)?;
        let lemma = self.node(lemma_id)?;

        if !leaf.is_leaf() {
            return Err(TableauxErr::ExpectedLeaf(leaf_id));
        }

        if leaf.is_closed() {
            return Err(TableauxErr::AlreadyClosed(leaf_id));
        }

        if !lemma.is_closed() {
            return Err(TableauxErr::ExpectedClosed(lemma_id));
        }

        if lemma.parent().is_none() {
            return Err(TableauxErr::LemmaRoot(lemma_id));
        }

        if lemma.is_leaf() {
            return Err(TableauxErr::LemmaLeaf(lemma_id));
        }

        let common_parent = lemma.parent().unwrap();

        if !self.node_is_parent_of(common_parent, leaf_id)? {
            return Err(TableauxErr::ExpectedSiblings(leaf_id, lemma_id));
        }

        let atom: Atom<L> = lemma.to_atom();

        if self.regular() {}

        Ok(atom)
    }

    fn node_is_closable(&self, id: usize) -> bool;

    fn node_is_directly_closable(&self, id: usize) -> bool;

    fn clause_expand_preprocessing(&self, clause: &Clause<L>) -> Vec<Atom<L>>;
}

pub trait TableauxNode<L: fmt::Display + Clone>: Into<Atom<L>> {
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
