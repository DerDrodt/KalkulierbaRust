use std::collections::HashMap;

use super::visitor::FOTermVisitor;

use crate::{logic::fo::FOTerm, KStr};

pub struct VariableInstantiator(pub HashMap<KStr, FOTerm>);

impl FOTermVisitor for VariableInstantiator {
    type Ret = FOTerm;

    fn visit_quantified_var(&mut self, s: &KStr) -> Self::Ret {
        if self.0.contains_key(s) {
            self.0.get(s).unwrap().clone()
        } else {
            FOTerm::QuantifiedVar(s.clone())
        }
    }

    fn visit_const(&mut self, s: &KStr) -> Self::Ret {
        FOTerm::Const(s.clone())
    }

    fn visit_fn(&mut self, name: &KStr, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        let args = args.iter().map(|a| self.visit(a)).collect();

        FOTerm::Function(name.clone(), args)
    }
}

pub struct VariableSuffixAppend(pub String);

impl FOTermVisitor for VariableSuffixAppend {
    type Ret = FOTerm;

    fn visit_quantified_var(&mut self, s: &KStr) -> Self::Ret {
        FOTerm::QuantifiedVar(format!("{}{}", s, self.0).into())
    }

    fn visit_const(&mut self, s: &KStr) -> Self::Ret {
        FOTerm::Const(s.clone())
    }

    fn visit_fn(&mut self, name: &KStr, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        let args = args.iter().map(|a| self.visit(a)).collect();

        FOTerm::Function(name.clone(), args)
    }
}

pub struct QuantifierLinker<'h> {
    quantifiers: &'h mut HashMap<KStr, Vec<KStr>>,
}

impl<'a, 'h> QuantifierLinker<'h> {
    pub fn new(quantifiers: &'h mut HashMap<KStr, Vec<KStr>>) -> Self {
        Self { quantifiers }
    }
}

impl<'a, 'h> FOTermVisitor for QuantifierLinker<'h> {
    type Ret = Result<(), KStr>;

    fn visit_quantified_var(&mut self, s: &KStr) -> Self::Ret {
        let quant = self.quantifiers.get_mut(s);

        match quant {
            Some(quant) => {
                quant.push(s.clone());
                Ok(())
            }
            None => Err(s.clone()),
        }
    }

    fn visit_const(&mut self, _: &KStr) -> Self::Ret {
        Ok(())
    }

    fn visit_fn(&mut self, _: &KStr, args: &Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        for arg in args {
            self.visit(arg)?;
        }
        Ok(())
    }
}
