use std::collections::HashMap;

use super::visitor::FOTermVisitor;

use crate::KStr;

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
