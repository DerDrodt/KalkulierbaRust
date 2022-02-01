use super::visitor::FOTermVisitor;

use crate::{
    logic::{fo::FOTerm, unify::Unifier},
    symbol::Symbol,
};

pub struct VariableInstantiator<'a>(pub &'a Unifier);

impl<'a> FOTermVisitor for VariableInstantiator<'a> {
    type Ret = FOTerm;

    fn visit_quantified_var(&self, s: Symbol) -> Self::Ret {
        if self.0.contains(s) {
            self.0.get(s).clone()
        } else {
            FOTerm::QuantifiedVar(s)
        }
    }

    fn visit_const(&self, s: Symbol) -> Self::Ret {
        FOTerm::Const(s)
    }

    fn visit_fn(&self, name: Symbol, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        let args = args.iter().map(|a| self.visit(a)).collect();

        FOTerm::Function(name, args)
    }
}

impl FOTerm {
    pub fn instantiate(&self, unifier: &Unifier) -> FOTerm {
        let instantiatior = VariableInstantiator(unifier);
        instantiatior.visit(self)
    }
}

pub struct VariableSuffixAppend(pub Symbol);

impl FOTermVisitor for VariableSuffixAppend {
    type Ret = FOTerm;

    fn visit_quantified_var(&self, s: Symbol) -> Self::Ret {
        FOTerm::QuantifiedVar(Symbol::intern(&format!("{}{}", s, self.0)))
    }

    fn visit_const(&self, s: Symbol) -> Self::Ret {
        FOTerm::Const(s)
    }

    fn visit_fn(&self, name: Symbol, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        let args = args.iter().map(|a| self.visit(a)).collect();

        FOTerm::Function(name, args)
    }
}

pub struct TermContainsVariableChecker(pub Symbol);

impl FOTermVisitor for TermContainsVariableChecker {
    type Ret = bool;

    fn visit_quantified_var(&self, s: Symbol) -> Self::Ret {
        s == self.0
    }

    fn visit_const(&self, _: Symbol) -> Self::Ret {
        false
    }

    fn visit_fn(&self, _: Symbol, args: &Vec<FOTerm>) -> Self::Ret {
        args.iter().fold(false, |acc, t| acc || self.visit(t))
    }
}
