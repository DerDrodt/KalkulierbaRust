use std::collections::{HashMap, HashSet};

use crate::{
    logic::{fo::FOTerm, LogicNode},
    Symbol,
};

use super::{
    term_manipulator::QuantifierLinker,
    visitor::{MutFOTermVisitor, MutLogicNodeVisitor},
};

pub struct SkolemizationErr;

pub struct Skolemization {
    counter: u32,
    quantified_vars: HashMap<Symbol, Vec<Symbol>>,
    replacement_map: HashMap<Symbol, FOTerm>,
    used_names: HashSet<Symbol>,
}

impl Skolemization {
    pub fn new(used_names: HashSet<Symbol>) -> Self {
        Self {
            counter: 0,
            quantified_vars: HashMap::new(),
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

        if self.quantified_vars.len() == 0 {
            FOTerm::Const(name)
        } else {
            let mut args = Vec::new();

            for (v, _) in &self.quantified_vars {
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
        Ok(LogicNode::Not(Box::new(child.clone())))
    }

    fn visit_and(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::And(
            Box::new(left.clone()),
            Box::new(right.clone()),
        ))
    }

    fn visit_or(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Or(
            Box::new(left.clone()),
            Box::new(right.clone()),
        ))
    }

    fn visit_impl(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Impl(
            Box::new(left.clone()),
            Box::new(right.clone()),
        ))
    }

    fn visit_equiv(
        &mut self,
        left: &crate::logic::LogicNode,
        right: &crate::logic::LogicNode,
    ) -> Self::Ret {
        Ok(LogicNode::Equiv(
            Box::new(left.clone()),
            Box::new(right.clone()),
        ))
    }

    fn visit_rel(&mut self, spelling: Symbol, args: &Vec<FOTerm>) -> Self::Ret {
        let mut replacer =
            SkolemTermReplacer::new(&self.replacement_map, &mut self.quantified_vars);
        Ok(LogicNode::Rel(
            spelling,
            args.iter().map(|a| replacer.visit(a)).collect(),
        ))
    }

    fn visit_all(
        &mut self,
        var: Symbol,
        child: &crate::logic::LogicNode,
        bound_vars: &Vec<Symbol>,
    ) -> Self::Ret {
        if self.quantified_vars.contains_key(&var) {
            return Err(SkolemizationErr);
        }
        self.quantified_vars.insert(var, bound_vars.clone());
        let child = self.visit(child)?;
        let bound_vars = self.quantified_vars.remove(&var).unwrap();

        Ok(LogicNode::All(var, Box::new(child), bound_vars))
    }

    fn visit_ex(
        &mut self,
        _: Symbol,
        child: &crate::logic::LogicNode,
        bound_vars: &Vec<Symbol>,
    ) -> Self::Ret {
        let term = self.get_skolem_term();
        for var in bound_vars {
            self.replacement_map.insert(*var, term.clone());
        }
        self.visit(child)
    }
}

struct SkolemTermReplacer<'a> {
    replacement_map: &'a HashMap<Symbol, FOTerm>,
    binding_quants: &'a mut HashMap<Symbol, Vec<Symbol>>,
}

impl<'a> SkolemTermReplacer<'a> {
    fn new(
        replacement_map: &'a HashMap<Symbol, FOTerm>,
        binding_quants: &'a mut HashMap<Symbol, Vec<Symbol>>,
    ) -> Self {
        Self {
            replacement_map,
            binding_quants,
        }
    }
}

impl<'a> MutFOTermVisitor for SkolemTermReplacer<'a> {
    type Ret = FOTerm;

    fn visit_quantified_var(&mut self, s: Symbol) -> Self::Ret {
        if self.replacement_map.contains_key(&s) {
            let mut linker = QuantifierLinker::new(&mut self.binding_quants);

            let skolem_term = self.replacement_map.get(&s).unwrap().clone();

            linker.visit(&skolem_term).unwrap();

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
