use std::fmt;

use serde::{
    de::{Error, Unexpected, Visitor},
    Deserialize, Serialize,
};

use super::super::LogicNode;
use super::naive_cnf::{FormulaConversionErr, NaiveCNF};
use super::tseytin_cnf::TseytinCNF;
use super::visitor::LogicNodeVisitor;
use crate::clause::{Atom, Clause, ClauseSet};
use crate::symbol::Symbol;

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

impl LogicNode {
    pub fn naive_cnf(&self) -> Result<ClauseSet<Symbol>, FormulaConversionErr> {
        NaiveCNF::new().visit(self)
    }

    pub fn tseytin_cnf(&self) -> Result<ClauseSet<Symbol>, FormulaConversionErr> {
        let mut t = TseytinCNF::new();
        let mut res = ClauseSet::new(vec![]);
        let root = Clause::new(vec![Atom::new(t.node_name(self), false)]);
        res.add(root);

        t.visit(self);

        res.unite(&t.clause_set);
        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use super::ClauseSet;
    use crate::{parse, session, symbol::Symbol};

    macro_rules! test_map {
        ($func:ident, $( $f:expr, $e:expr );*) => {{
            $(
                session(|| {
                    let parsed = parse::parse_prop_formula($f).unwrap();
                    let res: ClauseSet<Symbol> = parsed.$func().unwrap();
                    assert_eq!($e, res.to_string(), "Parsed: {}", parsed.to_string());
                });
            )*
        }};
    }

    #[test]
    fn naive_cnf() {
        test_map!(
            naive_cnf,
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
            tseytin_cnf,
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
