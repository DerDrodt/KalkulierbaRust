use std::{collections::HashMap, fmt};

use serde::{Deserialize, Serialize};

use crate::{
    clause::Atom, clause::ClauseSet, logic::fo::FOTerm, logic::fo::Relation, logic::unify,
};

use super::{TableauxErr, TableauxNode, TableauxState, TableauxType};

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum FOTabMove {}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct FOTabState<'f, L>
where
    L: fmt::Display + Clone,
{
    clause_set: ClauseSet<Relation<L>>,
    formula: &'f str,
    ty: TableauxType,
    regular: bool,
    backtracking: bool,
    manual_var_assign: bool,
    nodes: Vec<FOTabNode<L>>,
    moves: Vec<FOTabMove>,
    used_backtracking: bool,
    expansion_counter: u32,
}

impl<'f, L> FOTabState<'f, L>
where
    L: fmt::Display + Clone + Copy + Eq,
{
    fn node_ancestry_contains_unifiable(&self, id: usize, atom: Atom<Relation<L>>) -> bool {
        let mut node = match self.node(id) {
            Ok(n) => n,
            _ => {
                return false;
            }
        };

        while node.parent.is_some() {
            node = &self.nodes[node.parent.unwrap()];

            if node.negated != atom.negated()
                && node.relation.spelling == atom.lit().spelling
                && unify::unify(&node.relation, atom.lit()).is_ok()
            {
                return true;
            }
        }

        false
    }

    fn apply_var_instantiation(&mut self, var_assign: HashMap<&'f str, FOTerm<L>>) {}
}

impl<'f, L> TableauxState<Relation<L>> for FOTabState<'f, L>
where
    L: fmt::Display + Clone + Copy + Eq,
{
    type Node = FOTabNode<L>;

    fn regular(&self) -> bool {
        self.regular
    }

    fn nodes(&self) -> &Vec<Self::Node> {
        &self.nodes
    }

    fn node(&self, id: usize) -> super::TableauxResult<&Self::Node> {
        if let Some(node) = self.nodes.get(id) {
            Ok(node)
        } else {
            Err(TableauxErr::InvalidNodeId(id))
        }
    }

    fn node_mut(&mut self, id: usize) -> super::TableauxResult<&mut Self::Node> {
        if let Some(node) = self.nodes.get_mut(id) {
            Ok(node)
        } else {
            Err(TableauxErr::InvalidNodeId(id))
        }
    }

    fn node_is_closable(&self, id: usize) -> bool {
        match self.node(id) {
            Ok(n) => n.is_leaf() && self.node_ancestry_contains_unifiable(id, n.into()),
            _ => false,
        }
    }

    fn node_is_directly_closable(&self, id: usize) -> bool {
        let node = match self.node(id) {
            Ok(n) => n,
            _ => return false,
        };

        if node.parent.is_none()
            || !node.is_leaf()
            || node.negated == self.nodes[node.parent.unwrap()].negated
        {
            return false;
        }

        let parent = &self.nodes[node.parent.unwrap()];

        match unify::unify(&node.relation, &parent.relation) {
            Ok(_) => true,
            _ => false,
        }
    }

    fn clause_expand_preprocessing<'c>(
        &self,
        clause: &'c crate::clause::Clause<Relation<L>>,
    ) -> Vec<crate::clause::Atom<Relation<L>>> {
        let suffix_appender = ();
        let mut atom_list = Vec::new();

        for atom in clause.atoms() {
            let new_args = atom.lit().args.iter().map(|a| a.clone()).collect();
            let rel = Relation::new(atom.lit().spelling, new_args);
            atom_list.push(Atom::new(rel, atom.negated()));
        }

        atom_list
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct FOTabNode<L>
where
    L: Clone + fmt::Display,
{
    parent: Option<usize>,
    pub relation: Relation<L>,
    negated: bool,
    lemma_source: Option<usize>,
    is_closed: bool,
    close_ref: Option<usize>,
    children: Vec<usize>,
}

impl<'de: 'f, 'f, L> Deserialize<'de> for FOTabNode<L>
where
    L: Clone + fmt::Display,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        todo!()
    }
}

impl<'f, L> FOTabNode<L>
where
    L: Clone + fmt::Display,
{
    pub fn new(
        parent: Option<usize>,
        relation: Relation<L>,
        negated: bool,
        lemma_source: Option<usize>,
    ) -> Self {
        Self {
            parent,
            relation,
            negated,
            lemma_source,
            is_closed: false,
            close_ref: None,
            children: Vec::new(),
        }
    }
}

impl<'f, L> From<FOTabNode<L>> for Atom<Relation<L>>
where
    L: Clone + fmt::Display,
{
    fn from(n: FOTabNode<L>) -> Self {
        Atom::new(n.relation, n.negated)
    }
}

impl<'f, L> From<&FOTabNode<L>> for Atom<Relation<L>>
where
    L: Clone + fmt::Display,
{
    fn from(n: &FOTabNode<L>) -> Self {
        Atom::new(n.relation.clone(), n.negated)
    }
}

impl<'f, L> TableauxNode<Relation<L>> for FOTabNode<L>
where
    L: Clone + fmt::Display,
{
    fn parent(&self) -> Option<usize> {
        self.parent
    }

    fn spelling(&self) -> String {
        if self.negated {
            format!("!{}", self.relation)
        } else {
            self.relation.to_string()
        }
    }

    fn literal_stem(&self) -> String {
        format!("{}{}", self.relation.spelling, self.relation.args.len())
    }

    fn negated(&self) -> bool {
        self.negated
    }

    fn is_closed(&self) -> bool {
        self.is_closed
    }

    fn close_ref(&self) -> Option<usize> {
        self.close_ref
    }

    fn children(&self) -> &Vec<usize> {
        &self.children
    }

    fn lemma_source(&self) -> Option<usize> {
        self.lemma_source
    }

    fn is_leaf(&self) -> bool {
        self.children.len() == 0
    }

    fn mark_closed(&mut self) {
        self.is_closed = true;
    }

    fn to_atom(&self) -> Atom<Relation<L>> {
        self.into()
    }
}
