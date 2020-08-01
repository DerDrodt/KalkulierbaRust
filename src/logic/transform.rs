use super::LogicNode;
use crate::clause::{Atom, Clause, ClauseSet};

#[derive(Debug)]
pub struct FormulaConversionErr;

pub fn naive_cnf(node: &LogicNode) -> Result<ClauseSet<String>, FormulaConversionErr> {
    match node {
        LogicNode::Not(c) => match c.as_ref() {
            LogicNode::Not(i) => naive_cnf(i),
            LogicNode::Or(left, right) => {
                // TODO: optimize
                let left = left.clone();
                let right = right.clone();
                let and = LogicNode::And(
                    Box::new(LogicNode::Not(left)),
                    Box::new(LogicNode::Not(right)),
                );
                naive_cnf(&and)
            }
            LogicNode::And(left, right) => {
                // TODO: optimize
                let left = left.clone();
                let right = right.clone();
                let or = LogicNode::Or(
                    Box::new(LogicNode::Not(left)),
                    Box::new(LogicNode::Not(right)),
                );
                naive_cnf(&or)
            }
            LogicNode::Impl(left, right) => {
                // TODO: optimize
                let left = left.clone();
                let right = right.clone();
                let node = LogicNode::And(left, Box::new(LogicNode::Not(right)));
                naive_cnf(&node)
            }
            LogicNode::Equiv(left, right) => {
                // TODO: optimize
                let left = left.clone();
                let right = right.clone();
                let left_impl = Box::new(LogicNode::Impl(left.clone(), right.clone()));
                let right_impl = Box::new(LogicNode::Impl(right, left));
                let node = LogicNode::Not(Box::new(LogicNode::And(left_impl, right_impl)));
                naive_cnf(&node)
            }
            LogicNode::Var(spelling) => {
                let atom = Atom::new(spelling.clone(), true);
                let clause = Clause::new(vec![atom]);
                Ok(ClauseSet::new(vec![clause]))
            }
        },
        LogicNode::And(left, right) => {
            let mut c = naive_cnf(left)?;
            c.unite(&naive_cnf(right)?);
            Ok(c)
        }
        LogicNode::Or(left, right) => {
            let left: Vec<Clause<String>> = naive_cnf(left)?.into();
            let right: Vec<Clause<String>> = naive_cnf(right)?.into();

            if left.len() * right.len() > crate::CNF_BLOWUP_LIMIT as usize {
                Err(FormulaConversionErr)
            } else {
                let mut clauses = vec![];
                for lc in left.into_iter() {
                    for rc in right.clone().into_iter() {
                        let mut atoms: Vec<Atom<String>> = lc.clone().into();
                        atoms.append(&mut rc.into());
                        let clause = Clause::new(atoms);
                        clauses.push(clause);
                    }
                }

                Ok(ClauseSet::new(clauses))
            }
        }
        LogicNode::Impl(..) => naive_cnf(&node.clone().to_basic_ops()),
        LogicNode::Equiv(..) => naive_cnf(&node.clone().to_basic_ops()),
        LogicNode::Var(spelling) => Ok(ClauseSet::new(vec![Clause::new(vec![Atom::new(
            spelling.clone(),
            false,
        )])])),
    }
}

struct TseytinCNF {
    index: u32,
    cs: ClauseSet<String>,
}

impl TseytinCNF {
    pub fn new() -> Self {
        TseytinCNF {
            index: 0,
            cs: ClauseSet::new(vec![]),
        }
    }

    pub fn get_name(&self, node: &LogicNode) -> String {
        match node {
            LogicNode::Not(_) => format!("not{}", self.index),
            LogicNode::And(..) => format!("and{}", self.index),
            LogicNode::Or(..) => format!("or{}", self.index),
            LogicNode::Impl(..) => format!("impl{}", self.index),
            LogicNode::Equiv(..) => format!("equiv{}", self.index),
            LogicNode::Var(spelling) => format!("var{}", spelling),
        }
    }

    pub fn visit(&mut self, node: &LogicNode) {
        match node {
            LogicNode::Var(_) => self.index += 1,
            LogicNode::Not(c) => {
                let self_var = self.get_name(node);
                self.index += 1;
                let child_var = self.get_name(c);
                self.visit(c);

                let clause_a = Clause::new(vec![
                    Atom::new(child_var.clone(), true),
                    Atom::new(self_var.clone(), true),
                ]);
                let clause_b = Clause::new(vec![
                    Atom::new(child_var, false),
                    Atom::new(self_var, false),
                ]);
                self.cs.add(clause_a);
                self.cs.add(clause_b);
            }
            LogicNode::And(left, right) => {
                let self_var = self.get_name(node);
                self.index += 1;
                let left_var = self.get_name(left);
                self.visit(left);
                let right_var = self.get_name(right);
                self.visit(right);

                let clause_a = Clause::new(vec![
                    Atom::new(left_var.clone(), false),
                    Atom::new(self_var.clone(), true),
                ]);
                let clause_b = Clause::new(vec![
                    Atom::new(right_var.clone(), false),
                    Atom::new(self_var.clone(), true),
                ]);
                let clause_c = Clause::new(vec![
                    Atom::new(left_var.clone(), true),
                    Atom::new(right_var.clone(), true),
                    Atom::new(self_var.clone(), false),
                ]);
                self.cs.add(clause_a);
                self.cs.add(clause_b);
                self.cs.add(clause_c);
            }
            LogicNode::Or(left, right) => {
                let self_var = self.get_name(node);
                self.index += 1;
                let left_var = self.get_name(left);
                self.visit(left);
                let right_var = self.get_name(right);
                self.visit(right);

                let clause_a = Clause::new(vec![
                    Atom::new(left_var.clone(), true),
                    Atom::new(self_var.clone(), false),
                ]);
                let clause_b = Clause::new(vec![
                    Atom::new(right_var.clone(), true),
                    Atom::new(self_var.clone(), false),
                ]);
                let clause_c = Clause::new(vec![
                    Atom::new(left_var.clone(), false),
                    Atom::new(right_var.clone(), false),
                    Atom::new(self_var.clone(), true),
                ]);
                self.cs.add(clause_a);
                self.cs.add(clause_b);
                self.cs.add(clause_c);
            }
            LogicNode::Impl(left, right) => {
                let self_var = self.get_name(node);
                self.index += 1;
                let left_var = self.get_name(left);
                self.visit(left);
                let right_var = self.get_name(right);
                self.visit(right);

                let clause_a = Clause::new(vec![
                    Atom::new(left_var.clone(), false),
                    Atom::new(self_var.clone(), false),
                ]);
                let clause_b = Clause::new(vec![
                    Atom::new(right_var.clone(), true),
                    Atom::new(self_var.clone(), false),
                ]);
                let clause_c = Clause::new(vec![
                    Atom::new(left_var.clone(), true),
                    Atom::new(right_var.clone(), false),
                    Atom::new(self_var.clone(), true),
                ]);
                self.cs.add(clause_a);
                self.cs.add(clause_b);
                self.cs.add(clause_c);
            }
            LogicNode::Equiv(left, right) => {
                let self_var = self.get_name(node);
                self.index += 1;
                let left_var = self.get_name(left);
                self.visit(left);
                let right_var = self.get_name(right);
                self.visit(right);

                let clause_a = Clause::new(vec![
                    Atom::new(left_var.clone(), false),
                    Atom::new(right_var.clone(), true),
                    Atom::new(self_var.clone(), true),
                ]);
                let clause_b = Clause::new(vec![
                    Atom::new(left_var.clone(), true),
                    Atom::new(right_var.clone(), false),
                    Atom::new(self_var.clone(), true),
                ]);
                let clause_c = Clause::new(vec![
                    Atom::new(left_var.clone(), true),
                    Atom::new(right_var.clone(), true),
                    Atom::new(self_var.clone(), false),
                ]);
                let clause_d = Clause::new(vec![
                    Atom::new(left_var.clone(), false),
                    Atom::new(right_var.clone(), false),
                    Atom::new(self_var.clone(), false),
                ]);
                self.cs.add(clause_a);
                self.cs.add(clause_b);
                self.cs.add(clause_c);
                self.cs.add(clause_d);
            }
        }
    }
}

pub fn tseytin_cnf(node: &LogicNode) -> Result<ClauseSet<String>, FormulaConversionErr> {
    let mut t = TseytinCNF::new();
    let mut res = ClauseSet::new(vec![]);
    let root = Clause::new(vec![Atom::new(t.get_name(node), false)]);
    res.add(root);

    t.visit(node);

    res.unite(&t.cs);
    Ok(res)
}

#[cfg(test)]
mod tests {
    use super::naive_cnf as naive;
    use super::tseytin_cnf as tseytin;
    use crate::parse::clause_set::PropParser;

    macro_rules! test_map {
        ($func:ident, $( $f:expr, $e:expr );*) => {{
            $(
                let parsed = PropParser::parse($f).unwrap();
                assert_eq!($e, $func(&parsed).unwrap().to_string(), "Parsed: {}", parsed.to_string());
            )*
        }};
    }

    #[test]
    fn naive_cnf() {
        test_map!(
            naive,
            "a -> b", "{!a, b}";
            "!(a | b)", "{!a}, {!b}";
            "!(a & b)", "{!a, !b}";
            "!(!a)", "{a}";
            "!(a | b) -> !(!a & b)", "{a, b, a, !b}";
            "a | !b -> !a <-> b & !a | b", "{!a, !a, a, !b}, {!a, !a, a}, {!a, !a, !b, a}, {!a, !a, !b}, {b, !a, a, !b}, {b, !a, a}, {b, !a, !b, a}, {b, !a, !b}, {b, b, a, !b}, {b, b, a}, {b, b, !b, a}, {b, b, !b}, {!a, b, a, !b}, {!a, b, a}, {!a, b, !b, a}, {!a, b, !b}"
        );
    }
    #[test]
    fn tysetin_cnf() {
        test_map!(
            tseytin,
            "a -> b", "{impl0}, {vara, impl0}, {!varb, impl0}, {!vara, varb, !impl0}";
            "!(a | b)", "{not0}, {!vara, or1}, {!varb, or1}, {vara, varb, !or1}, {!or1, !not0}, {or1, not0}";
            "!(a & b)", "{not0}, {vara, !and1}, {varb, !and1}, {!vara, !varb, and1}, {!and1, !not0}, {and1, not0}";
            "!(!a)", "{not0}, {!vara, !not1}, {vara, not1}, {!not1, !not0}, {not1, not0}";
            "a", "{vara}";
            "!(a | b) -> !(!a & b)", "{impl0}, {!vara, or2}, {!varb, or2}, {vara, varb, !or2}, {!or2, !not1}, {or2, not1}, {!vara, !not7}, {vara, not7}, {not7, !and6}, {varb, !and6}, {!not7, !varb, and6}, {!and6, !not5}, {and6, not5}, {not1, impl0}, {!not5, impl0}, {!not1, not5, !impl0}";
            "a | !b -> !a <-> b & !a | b", "{equiv0}, {!varb, !not4}, {varb, not4}, {!vara, or2}, {!not4, or2}, {vara, not4, !or2}, {!vara, !not6}, {vara, not6}, {or2, impl1}, {!not6, impl1}, {!or2, not6, !impl1}, {!vara, !not11}, {vara, not11}, {varb, !and9}, {not11, !and9}, {!varb, !not11, and9}, {!and9, or8}, {!varb, or8}, {and9, varb, !or8}, {impl1, !or8, !equiv0}, {!impl1, or8, !equiv0}, {!impl1, !or8, equiv0}, {impl1, or8, equiv0}"
        );
    }
}
