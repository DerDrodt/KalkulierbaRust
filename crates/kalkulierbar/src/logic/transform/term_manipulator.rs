use std::collections::HashMap;

use super::visitor::{FOTermVisitor, MutFOTermVisitor};

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

pub struct QuantifierLinker<'h> {
    quantifiers: &'h mut HashMap<Symbol, Vec<Symbol>>,
}

impl<'a, 'h> QuantifierLinker<'h> {
    pub fn new(quantifiers: &'h mut HashMap<Symbol, Vec<Symbol>>) -> Self {
        Self { quantifiers }
    }
}

impl<'a, 'h> MutFOTermVisitor for QuantifierLinker<'h> {
    type Ret = Result<(), Symbol>;

    fn visit_quantified_var(&mut self, s: Symbol) -> Self::Ret {
        let quant = self.quantifiers.get_mut(&s);

        match quant {
            Some(quant) => {
                quant.push(s);
                Ok(())
            }
            None => Err(s),
        }
    }

    fn visit_const(&mut self, _: Symbol) -> Self::Ret {
        Ok(())
    }

    fn visit_fn(&mut self, _: Symbol, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        for arg in args {
            self.visit(arg)?;
        }
        Ok(())
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
