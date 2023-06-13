use std::collections::HashSet;

use crate::{logic::LogicNode, Symbol};

use super::visitor::{MutFOTermVisitor, MutLogicNodeVisitor};

pub fn collect_free_vars(n: &LogicNode) -> HashSet<Symbol> {
    let mut col = FreeVarCollector::new();
    col.visit(n);
    col.free
}

struct FreeVarCollector {
    bound: HashSet<Symbol>,
    free: HashSet<Symbol>,
}

impl FreeVarCollector {
    fn new() -> Self {
        Self {
            bound: HashSet::new(),
            free: HashSet::new(),
        }
    }
}

impl MutLogicNodeVisitor for FreeVarCollector {
    type Ret = ();

    fn visit_var(&mut self, _: Symbol) -> Self::Ret {
        panic!()
    }

    fn visit_not(&mut self, child: &LogicNode) -> Self::Ret {
        self.visit(child)
    }

    fn visit_and(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        self.visit(left);
        self.visit(right)
    }

    fn visit_or(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        self.visit(left);
        self.visit(right)
    }

    fn visit_impl(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        self.visit(left);
        self.visit(right)
    }

    fn visit_equiv(&mut self, left: &LogicNode, right: &LogicNode) -> Self::Ret {
        self.visit(left);
        self.visit(right)
    }

    fn visit_rel(&mut self, _: Symbol, args: &[crate::logic::fo::FOTerm]) -> Self::Ret {
        let mut col = FreeVarTermCollector::new(&self.bound);
        for a in args {
            col.visit(a);
        }
        self.free = self.free.union(&col.free).copied().collect();
    }

    fn visit_all(&mut self, var: Symbol, child: &LogicNode) -> Self::Ret {
        let already_inserted = !self.bound.insert(var);
        self.visit(child);
        if !already_inserted {
            self.bound.remove(&var);
        }
    }

    fn visit_ex(&mut self, var: Symbol, child: &LogicNode) -> Self::Ret {
        let already_inserted = !self.bound.insert(var);
        self.visit(child);
        if !already_inserted {
            self.bound.remove(&var);
        }
    }

    fn visit_box(&mut self, _: &LogicNode) -> Self::Ret {
        panic!("Cannot create CNF of Modal formula")
    }

    fn visit_diamond(&mut self, _: &LogicNode) -> Self::Ret {
        panic!("Cannot create CNF of Modal formula")
    }
}

struct FreeVarTermCollector<'a> {
    bound: &'a HashSet<Symbol>,
    free: HashSet<Symbol>,
}

impl<'a> FreeVarTermCollector<'a> {
    pub fn new(bound: &'a HashSet<Symbol>) -> Self {
        Self {
            bound,
            free: HashSet::new(),
        }
    }
}

impl<'a> MutFOTermVisitor for FreeVarTermCollector<'a> {
    type Ret = ();

    fn visit_quantified_var(&mut self, s: Symbol) -> Self::Ret {
        if !self.bound.contains(&s) {
            self.free.insert(s);
        }
    }

    fn visit_const(&mut self, _: Symbol) -> Self::Ret {}

    fn visit_fn(&mut self, _: Symbol, args: &[crate::logic::fo::FOTerm]) -> Self::Ret {
        for a in args {
            self.visit(a);
        }
    }
}
