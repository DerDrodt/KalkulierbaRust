use crate::calculus::CloseMsg;
use crate::clause::{Atom, Clause};
use std::fmt;

mod prop;

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

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum TableauxType {
    Unconnected,
    WeaklyConnected,
    StronglyConnected,
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

pub trait TableauxState {
    type AtomType: fmt::Display + Clone;
    type Node: TableauxNode<Self::AtomType> + Into<Atom<Self::AtomType>>;

    fn root(&self) -> &Self::Node;

    fn regular(&self) -> bool;

    fn nodes(&self) -> &Vec<Self::Node>;

    fn node(&self, id: usize) -> TableauxResult<&Self::Node>;

    fn node_mut(&self, id: usize) -> TableauxResult<&mut Self::Node>;

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

    fn mark_node_closed<'a>(&'a mut self, leaf: &mut Self::Node) {
        let mut node = leaf;

        while node.is_leaf()
            || node
                .children()
                .iter()
                .fold(true, |acc, e| acc && self.nodes()[*e].is_closed())
        {
            node.mark_closed();
            if node.parent().is_none() {
                break;
            }
            if let Ok(n) = self.node_mut(node.parent().unwrap()) {
                node = n;
            } else {
                break;
            }
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

    fn get_lemma(&self, leaf_id: usize, lemma_id: usize) -> TableauxResult<Atom<Self::AtomType>> {
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

        let atom: Atom<Self::AtomType> = (*lemma).into();

        if self.regular() {}

        Ok(atom)
    }

    fn node_is_closable(&self, id: usize) -> bool;

    fn node_is_directly_closable(&self, id: usize) -> bool;

    fn clause_expand_preprocessing<'c>(
        &self,
        clause: &'c Clause<Self::AtomType>,
    ) -> &'c Vec<Atom<String>>;
}

pub trait TableauxNode<L: fmt::Display + Clone>: Into<Atom<L>> + Copy {
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
}
