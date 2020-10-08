use std::collections::HashMap;

use super::visitor::FOTermVisitor;

pub struct QuantifierLinker<'a, 'h> {
    quantifiers: &'h mut HashMap<&'a str, Vec<&'a str>>,
}

impl<'a, 'h> QuantifierLinker<'a, 'h> {
    pub fn new(quantifiers: &'h mut HashMap<&'a str, Vec<&'a str>>) -> Self {
        Self { quantifiers }
    }
}

impl<'a, 'h> FOTermVisitor<'a> for QuantifierLinker<'a, 'h> {
    type Ret = Result<(), &'a str>;

    fn visit_quantified_var(&mut self, s: &'a str) -> Self::Ret {
        let quant = self.quantifiers.get_mut(s);

        match quant {
            Some(quant) => {
                quant.push(s);
                Ok(())
            }
            None => Err(s),
        }
    }

    fn visit_const(&mut self, _: &'a str) -> Self::Ret {
        Ok(())
    }

    fn visit_fn(&mut self, _: &'a str, args: &Vec<crate::logic::fo::FOTerm<'a>>) -> Self::Ret {
        for arg in args {
            self.visit(arg)?;
        }
        Ok(())
    }
}
