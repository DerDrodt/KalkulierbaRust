use std::collections::HashMap;

use serde::{Deserialize, Serialize};

use crate::{
    clause::Atom, clause::ClauseSet, logic::fo::FOTerm, logic::fo::Relation,
    logic::transform::term_manipulator::VariableInstantiator,
    logic::transform::term_manipulator::VariableSuffixAppend,
    logic::transform::visitor::FOTermVisitor, logic::unify, Calculus, KStr,
};

use super::{TableauxErr, TableauxNode, TableauxState, TableauxType};

pub enum FOTabErr {}

pub type FOTabResult<T> = Result<T, FOTabErr>;

pub struct FOTabParams {
    ty: TableauxType,
    regular: bool,
    backtracking: bool,
    manual_var_assign: bool,
}

impl Default for FOTabParams {
    fn default() -> Self {
        Self {
            ty: TableauxType::Unconnected,
            regular: false,
            backtracking: false,
            manual_var_assign: false,
        }
    }
}

pub struct FOTableaux;

impl<'f> Calculus<'f> for FOTableaux {
    type Params = FOTabParams;

    type State = FOTabState<'f>;

    type Move = FOTabMove;

    type Error = FOTabErr;

    fn parse_formula(
        formula: &'f str,
        params: Option<Self::Params>,
    ) -> Result<Self::State, Self::Error> {
        todo!()
    }

    fn apply_move(state: Self::State, k_move: Self::Move) -> Result<Self::State, Self::Error> {
        let mut state = state;
        state.status_msg.take();
        match k_move {
            FOTabMove::AutoClose(leaf, node) => apply_auto_close(state, leaf, node),
            FOTabMove::CloseAssign(leaf, node, var_assign) => {
                apply_close_assign(state, leaf, node, var_assign)
            }
            FOTabMove::Expand(leaf, clause) => apply_expand(state, leaf, clause),
            FOTabMove::Lemma(leaf, lemma) => apply_lemma(state, leaf, lemma),
            FOTabMove::Undo => apply_undo(state),
        }
    }

    fn check_close(state: Self::State) -> crate::calculus::CloseMsg {
        state.get_close_msg()
    }
}

pub fn apply_auto_close(
    mut state: FOTabState,
    leaf: usize,
    node: usize,
) -> FOTabResult<FOTabState> {
    todo!()
}

pub fn apply_close_assign(
    mut state: FOTabState,
    leaf: usize,
    node: usize,
    var_assign: HashMap<KStr, FOTerm>,
) -> FOTabResult<FOTabState> {
    todo!()
}

pub fn apply_expand(mut state: FOTabState, leaf: usize, clause: usize) -> FOTabResult<FOTabState> {
    todo!()
}

pub fn apply_lemma(mut state: FOTabState, leaf: usize, lemma: usize) -> FOTabResult<FOTabState> {
    todo!()
}

pub fn apply_undo(mut state: FOTabState) -> FOTabResult<FOTabState> {
    todo!()
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub enum FOTabMove {
    AutoClose(usize, usize),
    CloseAssign(usize, usize, HashMap<KStr, FOTerm>),
    Expand(usize, usize),
    Lemma(usize, usize),
    Undo,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct FOTabState<'f> {
    clause_set: ClauseSet<Relation<'f>>,
    formula: &'f str,
    ty: TableauxType,
    regular: bool,
    backtracking: bool,
    manual_var_assign: bool,
    nodes: Vec<FOTabNode<'f>>,
    moves: Vec<FOTabMove>,
    used_backtracking: bool,
    expansion_counter: u32,
    status_msg: Option<String>,
}

impl<'f> FOTabState<'f> {
    fn node_ancestry_contains_unifiable(&self, id: usize, atom: Atom<Relation<'f>>) -> bool {
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

    fn apply_var_instantiation(&mut self, var_assign: HashMap<KStr, FOTerm>) {
        let mut instantiator = VariableInstantiator(var_assign);

        self.nodes = self
            .nodes
            .iter()
            .map(|n| {
                let mut relation = n.relation.clone();
                relation.args = relation
                    .args
                    .iter()
                    .map(|a| instantiator.visit(a))
                    .collect();
                FOTabNode::new(n.parent, relation, n.negated, n.lemma_source)
            })
            .collect()
    }
}

impl<'f> TableauxState<Relation<'f>> for FOTabState<'f> {
    type Node = FOTabNode<'f>;

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
        clause: &'c crate::clause::Clause<Relation<'f>>,
    ) -> Vec<crate::clause::Atom<Relation<'f>>> {
        let mut suffix_appender = VariableSuffixAppend(format!("_{}", self.expansion_counter + 1));
        let mut atom_list = Vec::new();

        for atom in clause.atoms() {
            let new_args = atom
                .lit()
                .args
                .iter()
                .map(|a| suffix_appender.visit(&a.clone()))
                .collect();
            let rel = Relation::new(atom.lit().spelling, new_args);
            atom_list.push(Atom::new(rel, atom.negated()));
        }

        atom_list
    }
}

#[derive(Debug, Clone, Serialize)]
pub struct FOTabNode<'f> {
    parent: Option<usize>,
    pub relation: Relation<'f>,
    negated: bool,
    lemma_source: Option<usize>,
    is_closed: bool,
    close_ref: Option<usize>,
    children: Vec<usize>,
}

impl<'de: 'f, 'f> Deserialize<'de> for FOTabNode<'f> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        todo!()
    }
}

impl<'f> FOTabNode<'f> {
    pub fn new(
        parent: Option<usize>,
        relation: Relation<'f>,
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

impl<'f> From<FOTabNode<'f>> for Atom<Relation<'f>> {
    fn from(n: FOTabNode<'f>) -> Self {
        Atom::new(n.relation, n.negated)
    }
}

impl<'f> From<&FOTabNode<'f>> for Atom<Relation<'f>> {
    fn from(n: &FOTabNode<'f>) -> Self {
        Atom::new(n.relation.clone(), n.negated)
    }
}

impl<'f> TableauxNode<Relation<'f>> for FOTabNode<'f> {
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

    fn to_atom(&self) -> Atom<Relation<'f>> {
        self.into()
    }
}
