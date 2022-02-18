use std::collections::HashSet;

use crate::{logic::LogicNode, Symbol};

use super::visitor::{MutFOTermVisitor, MutLogicNodeVisitor};

pub fn collect_symbols(n: &LogicNode) -> HashSet<Symbol> {
    let mut c = SymbolCollector::new();
    c.visit(n);
    c.0
}

pub struct SymbolCollector(HashSet<Symbol>);

impl SymbolCollector {
    pub fn new() -> Self {
        Self(HashSet::new())
    }
}

impl Default for SymbolCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl MutLogicNodeVisitor for SymbolCollector {
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
        self.0.insert(spelling);
        for a in args {
            TermSymbolCollector(&mut self.0).visit(a);
        }
    }

    fn visit_all(&mut self, var: Symbol, child: &crate::logic::LogicNode) -> Self::Ret {
        self.0.insert(var);
        self.visit(child);
    }

    fn visit_ex(&mut self, var: Symbol, child: &crate::logic::LogicNode) -> Self::Ret {
        self.0.insert(var);
        self.visit(child);
    }
}

struct TermSymbolCollector<'a>(&'a mut HashSet<Symbol>);

impl<'a> MutFOTermVisitor for TermSymbolCollector<'a> {
    type Ret = ();

    fn visit_quantified_var(&mut self, s: Symbol) -> Self::Ret {
        self.0.insert(s);
    }

    fn visit_const(&mut self, s: Symbol) -> Self::Ret {
        self.0.insert(s);
    }

    fn visit_fn(&mut self, name: Symbol, args: &[crate::logic::fo::FOTerm]) -> Self::Ret {
        self.0.insert(name);
        for a in args {
            self.visit(a);
        }
    }
}
