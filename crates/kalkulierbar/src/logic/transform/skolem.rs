use std::{
    collections::{HashMap, HashSet},
    fmt,
};

use crate::{
    logic::{fo::FOTerm, LogicNode},
    Symbol,
};

use super::{
    collectors::collect_symbols,
    visitor::{MutFOTermVisitor, MutLogicNodeVisitor},
};

pub fn skolemize(n: &LogicNode) -> Result<LogicNode, SkolemizationErr> {
    let used_symbols = collect_symbols(n);
    Skolemization::new(used_symbols).visit(n)
}

#[derive(Debug, Clone, Copy)]
pub struct SkolemizationErr;

impl fmt::Display for SkolemizationErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Double-bound universally quantified variable encountered during Skolemization"
        )
    }
}

pub struct Skolemization {
    counter: u32,
    quantified_vars: Vec<Symbol>,
    replacement_map: HashMap<Symbol, FOTerm>,
    used_names: HashSet<Symbol>,
}

impl Skolemization {
    pub fn new(used_names: HashSet<Symbol>) -> Self {
        Self {
            counter: 0,
            quantified_vars: Vec::new(),
            replacement_map: HashMap::new(),
            used_names,
        }
    }

    fn get_skolem_term(&mut self) -> FOTerm {
        self.counter += 1;
        let mut name = Symbol::intern(&format!("sk{}", self.counter));

        while self.used_names.contains(&name) {
            self.counter += 1;
            name = Symbol::intern(&format!("sk{}", self.counter));
        }

        if self.quantified_vars.is_empty() {
            FOTerm::Const(name)
        } else {
            let mut args = Vec::new();

            for v in &self.quantified_vars {
                args.push(FOTerm::QuantifiedVar(*v))
            }

            FOTerm::Function(name, args)
        }
    }
}

impl MutLogicNodeVisitor for Skolemization {
    type Ret = Result<LogicNode, SkolemizationErr>;

    fn visit_var(&mut self, _: Symbol) -> Self::Ret {
        panic!("Unknown LogicNode encountered during Skolemization")
    }

    fn visit_not(&mut self, child: &crate::logic::LogicNode) -> Self::Ret {
        Ok(LogicNode::Not(Box::new(self.visit(child)?)))
    }

    fn visit_and(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::And(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_or(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Or(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_impl(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Impl(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_equiv(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Equiv(
            Box::new(self.visit(left)?),
            Box::new(self.visit(right)?),
        ))
    }

    fn visit_rel(&mut self, spelling: Symbol, args: &Vec<FOTerm>) -> Self::Ret {
        let mut replacer = SkolemTermReplacer::new(&self.replacement_map);
        Ok(LogicNode::Rel(
            spelling,
            args.iter().map(|a| replacer.visit(a)).collect(),
        ))
    }

    fn visit_all(&mut self, var: Symbol, child: &crate::logic::LogicNode) -> Self::Ret {
        if self.quantified_vars.contains(&var) {
            return Err(SkolemizationErr);
        }
        self.quantified_vars.push(var);
        let child = self.visit(child)?;
        let popped = self.quantified_vars.pop().unwrap();
        assert!(popped == var);

        Ok(LogicNode::All(var, Box::new(child)))
    }

    fn visit_ex(&mut self, var: Symbol, child: &crate::logic::LogicNode) -> Self::Ret {
        let term = self.get_skolem_term();

        let old = self.replacement_map.insert(var, term);

        let ret = self.visit(child);

        if let Some(v) = old {
            self.replacement_map.insert(var, v);
        } else {
            self.replacement_map.remove(&var);
        }

        ret
    }
}

struct SkolemTermReplacer<'a> {
    replacement_map: &'a HashMap<Symbol, FOTerm>,
}

impl<'a> SkolemTermReplacer<'a> {
    fn new(replacement_map: &'a HashMap<Symbol, FOTerm>) -> Self {
        Self { replacement_map }
    }
}

impl<'a> MutFOTermVisitor for SkolemTermReplacer<'a> {
    type Ret = FOTerm;

    fn visit_quantified_var(&mut self, s: Symbol) -> Self::Ret {
        if self.replacement_map.contains_key(&s) {
            let skolem_term = self.replacement_map.get(&s).unwrap().clone();

            skolem_term
        } else {
            FOTerm::QuantifiedVar(s)
        }
    }

    fn visit_const(&mut self, s: Symbol) -> Self::Ret {
        FOTerm::Const(s)
    }

    fn visit_fn(&mut self, name: Symbol, args: &Vec<FOTerm>) -> Self::Ret {
        FOTerm::Function(name, args.iter().map(|a| self.visit(a)).collect())
    }
}
