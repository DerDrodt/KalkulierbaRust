use core::fmt;
use std::{
    collections::HashSet,
    ops::{Add, AddAssign},
};

use crate::{
    clause::ClauseSet,
    logic::{
        fo::{FOTerm, Relation},
        LogicNode,
    },
    Symbol,
};

use super::visitor::{FOTermVisitor, MutFOTermVisitor, MutLogicNodeVisitor};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct CompoundSig {
    name: Symbol,
    arity: usize,
}

impl CompoundSig {
    pub fn new(name: Symbol, arity: usize) -> Self {
        Self { name, arity }
    }
}

impl fmt::Display for CompoundSig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}({})", self.name, self.arity)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    consts: HashSet<Symbol>,
    fns: HashSet<CompoundSig>,
    rels: HashSet<CompoundSig>,
    bound_vars: HashSet<Symbol>,
}

impl Signature {
    pub fn empty() -> Self {
        Self {
            consts: HashSet::new(),
            fns: HashSet::new(),
            rels: HashSet::new(),
            bound_vars: HashSet::new(),
        }
    }

    pub fn of_node(node: &LogicNode) -> Self {
        let mut se = SigExtractor::new();
        se.visit(node);
        Self {
            consts: se.consts,
            fns: se.fns,
            rels: se.rels,
            bound_vars: se.bound_vars,
        }
    }

    pub fn of_nodes(nodes: &[&LogicNode]) -> Self {
        let mut s = Self::empty();
        for n in nodes.into_iter() {
            s += Self::of_node(n);
        }
        s
    }

    pub fn of_rel(r: &Relation) -> Self {
        let mut consts = HashSet::new();
        let mut fns = HashSet::new();
        let rels = HashSet::from([CompoundSig::new(r.spelling, r.args.len())]);
        let mut bound_vars = HashSet::new();
        let mut tse = TermSigExtractor::new(&mut consts, &mut fns, &mut bound_vars);

        for a in &r.args {
            tse.visit(a);
        }

        Self {
            consts,
            fns,
            rels,
            bound_vars,
        }
    }

    pub fn of_clause_set(cs: &ClauseSet<Relation>) -> Self {
        let mut s = Self::empty();
        for a in cs.clauses().iter().flat_map(|c| c.atoms()) {
            s += Self::of_rel(a.lit());
        }
        s
    }

    pub fn get_const_and_fn_names(&self) -> HashSet<Symbol> {
        self.consts
            .iter()
            .copied()
            .chain(self.fns.iter().map(|f| f.name))
            .collect()
    }

    pub fn get_fn_arity(&self, name: Symbol) -> Option<usize> {
        self.fns.iter().find(|f| f.name == name).map(|f| f.arity)
    }

    pub fn has_const(&self, name: Symbol) -> bool {
        self.consts.contains(&name)
    }

    pub fn has_fn(&self, name: Symbol) -> bool {
        self.fns.iter().any(|f| f.name == name)
    }

    pub fn has_const_or_fn(&self, name: Symbol) -> bool {
        self.has_const(name) || self.has_fn(name)
    }

    pub fn check(&self, t: &FOTerm) -> Result<(), SigAdherenceErr> {
        let sac = SigAdherenceChecker::new(self, true);
        sac.visit(t)
    }
}

impl Add<&Signature> for &Signature {
    type Output = Signature;

    fn add(self, rhs: &Signature) -> Self::Output {
        Signature {
            consts: self.consts.union(&rhs.consts).copied().collect(),
            fns: self.fns.union(&rhs.fns).copied().collect(),
            rels: self.rels.union(&rhs.rels).copied().collect(),
            bound_vars: self.consts.union(&rhs.bound_vars).copied().collect(),
        }
    }
}

impl AddAssign for Signature {
    fn add_assign(&mut self, rhs: Self) {
        for c in rhs.consts.into_iter() {
            self.consts.insert(c);
        }
        for f in rhs.fns.into_iter() {
            self.fns.insert(f);
        }
        for r in rhs.rels.into_iter() {
            self.rels.insert(r);
        }
        for b in rhs.bound_vars.into_iter() {
            self.bound_vars.insert(b);
        }
    }
}

impl fmt::Display for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = self
            .consts
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        let fns = self
            .fns
            .iter()
            .map(|f| f.name.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let r = self
            .rels
            .iter()
            .map(|f| f.name.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let b = self
            .bound_vars
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", ");
        write!(
            f,
            "Σ(constants={}, functions={}, relations={}, bound={})",
            c, fns, r, b
        )
    }
}

struct SigExtractor {
    consts: HashSet<Symbol>,
    fns: HashSet<CompoundSig>,
    rels: HashSet<CompoundSig>,
    bound_vars: HashSet<Symbol>,
}

impl SigExtractor {
    fn new() -> Self {
        Self {
            consts: HashSet::new(),
            fns: HashSet::new(),
            rels: HashSet::new(),
            bound_vars: HashSet::new(),
        }
    }
}

impl MutLogicNodeVisitor for SigExtractor {
    type Ret = ();

    fn visit_var(&mut self, _: Symbol) -> Self::Ret {}

    fn visit_not(&mut self, child: &crate::logic::LogicNode) -> Self::Ret {
        self.visit(child)
    }

    fn visit_and(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        self.visit(left);
        self.visit(right)
    }

    fn visit_or(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        self.visit(left);
        self.visit(right)
    }

    fn visit_impl(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        self.visit(left);
        self.visit(right)
    }

    fn visit_equiv(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        self.visit(left);
        self.visit(right)
    }

    fn visit_rel(&mut self, spelling: Symbol, args: &[crate::logic::fo::FOTerm]) -> Self::Ret {
        self.rels.insert(CompoundSig::new(spelling, args.len()));
        let mut tse = TermSigExtractor::new(&mut self.consts, &mut self.fns, &mut self.bound_vars);
        for a in args {
            tse.visit(a);
        }
    }

    fn visit_all(&mut self, var: Symbol, child: &crate::logic::LogicNode) -> Self::Ret {
        self.bound_vars.insert(var);
        self.visit(child)
    }

    fn visit_ex(&mut self, var: Symbol, child: &crate::logic::LogicNode) -> Self::Ret {
        self.bound_vars.insert(var);
        self.visit(child)
    }
}

struct TermSigExtractor<'a> {
    consts: &'a mut HashSet<Symbol>,
    fns: &'a mut HashSet<CompoundSig>,
    bound_vars: &'a mut HashSet<Symbol>,
}

impl<'a> TermSigExtractor<'a> {
    fn new(
        consts: &'a mut HashSet<Symbol>,
        fns: &'a mut HashSet<CompoundSig>,
        bound_vars: &'a mut HashSet<Symbol>,
    ) -> Self {
        Self {
            consts,
            fns,
            bound_vars,
        }
    }
}

impl<'a> MutFOTermVisitor for TermSigExtractor<'a> {
    type Ret = ();

    fn visit_quantified_var(&mut self, s: Symbol) -> Self::Ret {
        self.bound_vars.insert(s);
    }

    fn visit_const(&mut self, s: Symbol) -> Self::Ret {
        self.consts.insert(s);
    }

    fn visit_fn(&mut self, name: Symbol, args: &[crate::logic::fo::FOTerm]) -> Self::Ret {
        self.fns.insert(CompoundSig::new(name, args.len()));
        for a in args {
            self.visit(a);
        }
    }
}

struct SigAdherenceChecker<'a> {
    sig: &'a Signature,
    allow_new_consts: bool,
}

impl<'a> SigAdherenceChecker<'a> {
    fn new(sig: &'a Signature, allow_new_consts: bool) -> Self {
        Self {
            sig,
            allow_new_consts,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SigAdherenceErr {
    UnknownConst(Symbol),
    UnknownFn(Symbol),
    ConstAndFn(Symbol),
    IncorrectArity(Symbol, usize, usize),
}

impl fmt::Display for SigAdherenceErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SigAdherenceErr::UnknownConst(name) => write!(f, "Unknown constant '{name}'"),
            SigAdherenceErr::UnknownFn(name) => write!(f, "Unknown function '{name}'"),
            SigAdherenceErr::ConstAndFn(name) => {
                write!(f, "'{name}' is both a constant and a function")
            }
            SigAdherenceErr::IncorrectArity(name, expected, actual) => write!(
                f,
                "Function '{name}' should have arity {expected} but has {actual}"
            ),
        }
    }
}

impl<'a> FOTermVisitor for SigAdherenceChecker<'a> {
    type Ret = Result<(), SigAdherenceErr>;

    fn visit_quantified_var(&self, _: Symbol) -> Self::Ret {
        Ok(())
    }

    fn visit_const(&self, s: Symbol) -> Self::Ret {
        if !self.allow_new_consts && !self.sig.has_const(s) {
            Err(SigAdherenceErr::UnknownConst(s))
        } else if self.sig.has_fn(s) {
            Err(SigAdherenceErr::ConstAndFn(s))
        } else {
            Ok(())
        }
    }

    fn visit_fn(&self, name: Symbol, args: &[crate::logic::fo::FOTerm]) -> Self::Ret {
        let expected = match self.sig.get_fn_arity(name) {
            Some(n) => n,
            _ => return Err(SigAdherenceErr::UnknownFn(name)),
        };
        let arity = args.len();

        if expected != arity {
            return Err(SigAdherenceErr::IncorrectArity(name, expected, arity));
        }

        for a in args {
            self.visit(a)?;
        }
        Ok(())
    }
}
