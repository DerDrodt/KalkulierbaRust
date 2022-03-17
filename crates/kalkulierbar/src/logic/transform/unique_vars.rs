use std::collections::{HashMap, HashSet};

use crate::{
    logic::{fo::FOTerm, LogicNode},
    Symbol,
};

use super::transformer::{FOTermTransformer, MutLogicNodeTransformer};

pub fn unique_vars(n: LogicNode) -> LogicNode {
    UniqueVars::new().visit(n)
}

#[derive(Default)]
struct UniqueVars {
    variable_disamb_counter: HashMap<Symbol, u32>,
    seen_vars: HashSet<Symbol>,
    replacements: HashMap<Symbol, Symbol>,
}

impl UniqueVars {
    pub fn new() -> Self {
        Default::default()
    }

    fn handle_var_binding(&mut self, name: Symbol) -> Symbol {
        let mut new_name = name;

        // Why is this loop necessary?
        // Good question! We can't assume that the generated name with the current version number
        // does not already exist in the formula (e.g. \all X: \all X: P(X) & \ex Xv1: P(Xv1))
        while self.seen_vars.contains(&new_name) {
            let v = self
                .variable_disamb_counter
                .insert(
                    name,
                    *self.variable_disamb_counter.get(&name).unwrap_or(&0) + 1,
                )
                .unwrap_or(0)
                + 1;
            new_name = Symbol::intern(&format!("{}v{}", name, v))
        }

        self.seen_vars.insert(new_name);

        new_name
    }
}

impl MutLogicNodeTransformer for UniqueVars {
    type Ret = LogicNode;

    fn visit_var(&mut self, _: Symbol) -> Self::Ret {
        panic!("Called unique variable transformer on propositional formula")
    }

    fn visit_not(&mut self, child: crate::logic::LogicNode) -> Self::Ret {
        LogicNode::Not(self.visit(child).into())
    }

    fn visit_and(
        &mut self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        LogicNode::And(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_or(
        &mut self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        LogicNode::Or(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_impl(
        &mut self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        LogicNode::Impl(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_equiv(
        &mut self,
        left: crate::logic::LogicNode,
        right: crate::logic::LogicNode,
    ) -> Self::Ret {
        LogicNode::Equiv(self.visit(left).into(), self.visit(right).into())
    }

    fn visit_rel(&mut self, spelling: Symbol, args: Vec<crate::logic::fo::FOTerm>) -> Self::Ret {
        let renamer = VariableRenamer::new_strict(&self.replacements);
        LogicNode::Rel(
            spelling,
            args.into_iter().map(|a| renamer.visit(a)).collect(),
        )
    }

    fn visit_all(&mut self, var: Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        let disamb = self.handle_var_binding(var);

        let old = self.replacements.insert(var, disamb);
        let child = self.visit(child);
        if let Some(v) = old {
            self.replacements.insert(var, v);
        } else {
            self.replacements.remove(&var);
        }

        LogicNode::All(disamb, Box::new(child))
    }

    fn visit_ex(&mut self, var: Symbol, child: crate::logic::LogicNode) -> Self::Ret {
        let disamb = self.handle_var_binding(var);

        let old = self.replacements.insert(var, disamb);
        let child = self.visit(child);
        if let Some(v) = old {
            self.replacements.insert(var, v);
        } else {
            self.replacements.remove(&var);
        }

        LogicNode::Ex(disamb, Box::new(child))
    }
}

pub(crate) struct VariableRenamer<'a> {
    strict: bool,
    replacement_map: &'a HashMap<Symbol, Symbol>,
}

impl<'a> VariableRenamer<'a> {
    pub fn new_strict(map: &'a HashMap<Symbol, Symbol>) -> Self {
        Self {
            strict: true,
            replacement_map: map,
        }
    }

    pub fn new(map: &'a HashMap<Symbol, Symbol>) -> Self {
        Self {
            strict: false,
            replacement_map: map,
        }
    }
}

impl<'a> FOTermTransformer for VariableRenamer<'a> {
    fn visit_quantified_var(&self, s: Symbol) -> FOTerm {
        FOTerm::QuantifiedVar(match self.replacement_map.get(&s) {
            Some(s) => *s,
            None => {
                if self.strict {
                    panic!(
                        "Encountered QuantifiedVariable with no disambiguation replacement: {}",
                        s
                    )
                } else {
                    s
                }
            }
        })
    }

    fn visit_const(&self, s: Symbol) -> FOTerm {
        FOTerm::Const(s)
    }

    fn visit_fn(&self, name: Symbol, args: Vec<crate::logic::fo::FOTerm>) -> FOTerm {
        FOTerm::Function(name, args.into_iter().map(|a| self.visit(a)).collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{parse::fo::parse_fo_formula, session};

    #[test]
    fn valid() {
        session(|| {
            let formulas = [
                (
                    "\\all X: (R(X) & \\all X: S(X))",
                    "(∀X: (R(X) ∧ (∀Xv1: S(Xv1))))",
                ),
                (
                    "\\all X: R(X) & \\all X: S(X)",
                    "((∀X: R(X)) ∧ (∀Xv1: S(Xv1)))",
                ),
            ];

            for (f, e) in formulas {
                let parsed = parse_fo_formula(f).unwrap();
                let nnf = unique_vars(parsed);
                assert_eq!(e, nnf.to_string());
            }
        })
    }
}
