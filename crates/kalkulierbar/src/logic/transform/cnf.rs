use std::fmt;

use serde::{
    de::{Error, Unexpected, Visitor},
    Deserialize, Serialize,
};

use super::super::LogicNode;
use crate::clause::{Atom, Clause, ClauseSet};

#[derive(Debug)]
pub struct FormulaConversionErr;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lit<'l> {
    Str(&'l str),
    Indexed(&'l str, u32),
    Appended(&'l str, &'l str),
}

impl<'l> fmt::Display for Lit<'l> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Lit::Str(s) => write!(f, "{}", s),
            Lit::Indexed(s, i) => write!(f, "{}{}", s, i),
            Lit::Appended(s1, s2) => write!(f, "{}{}", s1, s2),
        }
    }
}

impl<'l> From<&'l str> for Lit<'l> {
    fn from(s: &'l str) -> Self {
        Lit::Str(s)
    }
}

impl<'l> From<(&'l str, u32)> for Lit<'l> {
    fn from((s, i): (&'l str, u32)) -> Self {
        Lit::Indexed(s, i)
    }
}

impl<'l> From<(&'l str, &'l str)> for Lit<'l> {
    fn from((s, i): (&'l str, &'l str)) -> Self {
        Lit::Appended(s, i)
    }
}

impl<'l> Serialize for Lit<'l> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl<'de: 'l, 'l> Deserialize<'de> for Lit<'l> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        struct LitVisitor;

        impl<'l> Visitor<'l> for LitVisitor {
            type Value = Lit<'l>;

            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a Lit")
            }

            fn visit_borrowed_str<E>(self, v: &'l str) -> Result<Self::Value, E>
            where
                E: Error,
            {
                Ok(v.into())
            }

            fn visit_borrowed_bytes<E>(self, v: &'l [u8]) -> Result<Self::Value, E>
            where
                E: Error,
            {
                use std::str;
                let s = str::from_utf8(v)
                    .map_err(|_| Error::invalid_value(Unexpected::Bytes(v), &self))?;
                Ok(Lit::Str(s))
            }
        }

        deserializer.deserialize_str(LitVisitor)
    }
}

pub fn naive_cnf<'n, 'f, L>(node: &'n LogicNode<'f>) -> Result<ClauseSet<L>, FormulaConversionErr>
where
    L: Copy + fmt::Display + From<&'f str> + PartialEq + Eq,
{
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
                let atom = Atom::new((*spelling).into(), true);
                let clause = Clause::new(vec![atom]);
                Ok(ClauseSet::new(vec![clause]))
            }
            LogicNode::Rel(_, _) => todo!(),
            LogicNode::All(_, _, _) => todo!(),
            LogicNode::Ex(_, _, _) => todo!(),
        },
        LogicNode::And(left, right) => {
            let mut c = naive_cnf(left)?;
            c.unite(&naive_cnf(right)?);
            Ok(c)
        }
        LogicNode::Or(left, right) => {
            let left: Vec<Clause<L>> = naive_cnf(left)?.into();
            let right: Vec<Clause<L>> = naive_cnf(right)?.into();

            if left.len() * right.len() > crate::CNF_BLOWUP_LIMIT as usize {
                Err(FormulaConversionErr)
            } else {
                let mut clauses = vec![];
                for lc in left.into_iter() {
                    for rc in right.clone().into_iter() {
                        let mut atoms: Vec<Atom<L>> = lc.clone().into();
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
            (*spelling).into(),
            false,
        )])])),
        LogicNode::Rel(_, _) => todo!(),
        LogicNode::All(_, _, _) => todo!(),
        LogicNode::Ex(_, _, _) => todo!(),
    }
}

struct TseytinCNF<L>
where
    L: fmt::Display + Copy,
{
    index: u32,
    cs: ClauseSet<L>,
}

impl<'f, L> TseytinCNF<L>
where
    L: fmt::Display + Copy + From<(&'f str, &'f str)> + From<(&'f str, u32)>,
{
    pub fn new() -> Self {
        TseytinCNF {
            index: 0,
            cs: ClauseSet::new(vec![]),
        }
    }

    pub fn get_name<'n>(&mut self, node: &'n LogicNode<'f>) -> L {
        let name = match node {
            LogicNode::Not(_) => "not",
            LogicNode::And(..) => "and",
            LogicNode::Or(..) => "or",
            LogicNode::Impl(..) => "impl",
            LogicNode::Equiv(..) => "equiv",
            LogicNode::Var(spelling) => return ("var", *spelling).into(),
            LogicNode::Rel(_, _) => todo!(),
            LogicNode::All(_, _, _) => todo!(),
            LogicNode::Ex(_, _, _) => todo!(),
        };

        (name, self.index).into()
    }

    pub fn visit<'n>(&mut self, node: &'n LogicNode<'f>) {
        match node {
            LogicNode::Var(_) => self.index += 1,
            LogicNode::Not(c) => {
                let self_var = self.get_name(node);
                self.index += 1;
                let child_var = self.get_name(c);
                self.visit(c);

                let clause_a: Clause<L> =
                    Clause::new(vec![Atom::new(child_var, true), Atom::new(self_var, true)]);

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
            LogicNode::Rel(_, _) => todo!(),
            LogicNode::All(_, _, _) => todo!(),
            LogicNode::Ex(_, _, _) => todo!(),
        }
    }
}

pub fn tseytin_cnf<'n, 'f, L>(node: &'n LogicNode<'f>) -> Result<ClauseSet<L>, FormulaConversionErr>
where
    L: Copy + fmt::Display + From<(&'f str, &'f str)> + From<(&'f str, u32)>,
{
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
    use super::{ClauseSet, Lit};
    use crate::parse;

    macro_rules! test_map {
        ($func:ident, $( $f:expr, $e:expr );*) => {{
            $(
                let parsed = parse::parse_prop_formula($f).unwrap();
                let res: ClauseSet<Lit> = $func(&parsed).unwrap();
                assert_eq!($e, res.to_string(), "Parsed: {}", parsed.to_string());
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
