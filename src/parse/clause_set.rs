use lazy_static::lazy_static;
use regex::Regex;
use serde::{Deserialize, Serialize};

use super::{ParseErr, ParseResult, Token, TokenKind};
use crate::clause::{Atom, Clause, ClauseSet};
use crate::logic::{transform, transform::FormulaConversionErr, LogicNode};
use crate::parse;

#[derive(Deserialize, Serialize)]
pub enum CNFStrategy {
    Naive,
    Tseytin,
    Optimal,
}

pub fn parse_flexible(formula: &str, strategy: CNFStrategy) -> ParseResult<ClauseSet<String>> {
    let likely_formula = formula.contains(|c| match c {
        '&' | '|' | '\\' | '>' | '<' | '=' | '-' => true,
        _ => false,
    });
    /* let likely_clause_set = formula.contains(|c| match c {
        ';' | ',' => true,
        _ => false,
    }); */

    // TODO: Dimacs

    let clause_parse = match parse_clause_set(formula) {
        Ok(res) => {
            return Ok(res);
        }
        Err(e) => e,
    };

    let formula_parse = match PropParser::parse(formula) {
        Ok(res) => {
            return Ok(to_cnf(res, strategy).unwrap());
        }
        Err(e) => e,
    };

    Err(if likely_formula {
        formula_parse
    } else {
        clause_parse
    })
}

pub fn parse_clause_set(formula: &str) -> ParseResult<ClauseSet<String>> {
    let pf = formula.replace("\n", ";");

    lazy_static! {
        static ref WHITESPACE: Regex = Regex::new(r"\s").unwrap();
        static ref TRAILING_SEMI: Regex = Regex::new(r";$").unwrap();
        static ref RE: Regex =
            Regex::new(r"^!?[a-zA-Z0-9]+(,!?[a-zA-Z0-9]+)*(;!?[a-zA-Z0-9]+(,!?[a-zA-Z0-9]+)*)*$")
                .unwrap();
    }

    let pf = WHITESPACE.replace_all(&pf, "");
    let pf = TRAILING_SEMI.replace(&pf, "");

    if !RE.is_match(&pf) {
        return Err(ParseErr::InvalidFormat);
    }

    let mut parsed = vec![];

    for clause in pf.split(";") {
        let mut parsed_clause = vec![];

        for member in clause.split(',') {
            let negated = member.starts_with('!');
            let lit = if negated { &member[1..] } else { member };

            parsed_clause.push(Atom::new(lit.to_string(), negated))
        }

        parsed.push(Clause::new(parsed_clause));
    }

    Ok(ClauseSet::new(parsed))
}

pub fn parse_prop_formula(formula: &str) -> ParseResult<LogicNode> {
    PropParser::parse(formula)
}

pub struct PropParser {
    tokens: Vec<Token>,
}

impl PropParser {
    pub fn parse(formula: &str) -> ParseResult<LogicNode> {
        let mut parser = PropParser {
            tokens: parse::tokenize(formula)?,
        };
        parser.tokens.reverse();
        let node = parser.parse_equiv()?;
        if !parser.tokens.is_empty() {
            Err(ParseErr::Expected(
                "end of input".to_string(),
                parser.got_msg(),
            ))
        } else {
            Ok(*node)
        }
    }

    fn parse_equiv(&mut self) -> ParseResult<Box<LogicNode>> {
        let mut stub = self.parse_impl()?;

        while self.next_is(TokenKind::Equiv) {
            self.bump()?;
            let right = self.parse_impl()?;
            stub = Box::new(LogicNode::Equiv(stub, right));
        }

        Ok(stub)
    }

    fn parse_impl(&mut self) -> ParseResult<Box<LogicNode>> {
        let mut stub = self.parse_or()?;

        while self.next_is(TokenKind::Impl) {
            self.bump()?;
            let right = self.parse_or()?;
            stub = Box::new(LogicNode::Impl(stub, right));
        }

        Ok(stub)
    }

    fn parse_or(&mut self) -> ParseResult<Box<LogicNode>> {
        let mut stub = self.parse_and()?;

        while self.next_is(TokenKind::Or) {
            self.bump()?;
            let right = self.parse_and()?;
            stub = Box::new(LogicNode::Or(stub, right));
        }

        Ok(stub)
    }

    fn parse_and(&mut self) -> ParseResult<Box<LogicNode>> {
        let mut stub = self.parse_not()?;

        while self.next_is(TokenKind::And) {
            self.bump()?;
            let right = self.parse_not()?;
            stub = Box::new(LogicNode::And(stub, right));
        }

        Ok(stub)
    }

    fn parse_not(&mut self) -> ParseResult<Box<LogicNode>> {
        if self.next_is(TokenKind::Not) {
            self.bump()?;
            Ok(Box::new(LogicNode::Not(self.parse_paren()?)))
        } else {
            self.parse_paren()
        }
    }

    fn parse_paren(&mut self) -> ParseResult<Box<LogicNode>> {
        if self.next_is(TokenKind::LParen) {
            self.bump()?;
            let exp = self.parse_equiv()?;
            self.eat(TokenKind::RParen)?;
            Ok(exp)
        } else {
            self.parse_var()
        }
    }

    fn parse_var(&mut self) -> ParseResult<Box<LogicNode>> {
        if !self.next_is_id() {
            return Err(ParseErr::Expected("identifier".to_string(), self.got_msg()));
        }

        let exp = Box::new(LogicNode::Var(self.cur_token()?.spelling.clone()));
        self.bump()?;
        Ok(exp)
    }

    fn next_is(&self, expected: TokenKind) -> bool {
        return self.tokens.len() > 0 && self.cur_token().unwrap().kind == expected;
    }

    fn next_is_id(&self) -> bool {
        self.next_is(TokenKind::CapIdent) || self.next_is(TokenKind::LowIdent)
    }

    fn bump(&mut self) -> ParseResult<()> {
        match self.tokens.pop() {
            Some(_) => Ok(()),
            None => Err(ParseErr::Expected(
                "token".to_string(),
                "end of input".to_string(),
            )),
        }
    }

    fn eat(&mut self, expected: TokenKind) -> ParseResult<()> {
        if self.tokens.is_empty() || !self.next_is(expected.clone()) {
            Err(ParseErr::Expected(expected.to_string(), self.got_msg()))
        } else {
            self.bump()
        }
    }

    fn got_msg(&self) -> String {
        if self.tokens.is_empty() {
            "end of input".to_string()
        } else {
            let t = self.cur_token().unwrap();
            format!("{} at position {}", t, t.src_pos)
        }
    }

    fn cur_token(&self) -> ParseResult<&Token> {
        self.tokens.last().ok_or(ParseErr::Expected(
            "token".to_string(),
            "end of input".to_string(),
        ))
    }
}

fn to_cnf(
    node: LogicNode,
    strategy: CNFStrategy,
) -> Result<ClauseSet<String>, FormulaConversionErr> {
    match strategy {
        CNFStrategy::Naive => transform::naive_cnf(&node),
        CNFStrategy::Tseytin => transform::tseytin_cnf(&node),
        CNFStrategy::Optimal => {
            if let Ok(res) = transform::naive_cnf(&node) {
                Ok(res)
            } else {
                transform::tseytin_cnf(&node)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{parse_clause_set, parse_prop_formula};

    macro_rules! test_map {
        ($func:ident, $( $f:expr, $e:expr );*) => {{
            $(
                let cs = $func($f).expect($f);
                assert_eq!($e, cs.to_string());
            )*
        }};
    }

    macro_rules! test_list_invalid {
        ($func:ident, $( $f:expr ),*) => {{
            $(
                let res = $func($f);
                assert!(res.is_err(), "f: {}\nCS: {:?}", $f, res);
            )*
        }};
    }

    #[test]
    fn clause_set_valid() {
        test_map!(
            parse_clause_set,
            "a", "{a}";
            "!a", "{!a}";
            "a;b", "{a}, {b}";
            "a,b", "{a, b}";
            "a, b ;    c", "{a, b}, {c}";
            "a\nb", "{a}, {b}";
            "a\nb\n", "{a}, {b}";
            "a; ", "{a}";
            "fUnkYvAR;!McVariable,thefirst", "{fUnkYvAR}, {!McVariable, thefirst}"
        );
    }

    #[test]
    fn clause_set_invalid() {
        test_list_invalid!(
            parse_clause_set,
            "",
            ",a",
            ";a",
            "a,b,;c",
            "a,b,",
            "a;;b,c;d",
            "!!a",
            "a,!!b;c",
            "a,!",
            "a\n;",
            "a\n\n",
            "a;;"
        );
    }

    #[test]
    fn prop_valid() {
        test_map!(
            parse_prop_formula,
            "a", "a";
            "!a", "¬a";
            "a -> b", "(a -> b)";
            "a-> b", "(a -> b)";
            "a    ->b", "(a -> b)";
            "a->b", "(a -> b)";
            "a<->(b -> (!(c)))", "(a <=> (b -> ¬c))";
            "(b & a <-> (a) | !b)", "((b ∧ a) <=> (a ∨ ¬b))"
        );
    }

    #[test]
    fn prop_invalid() {
        test_list_invalid!(
            parse_prop_formula,
            "",
            "-->a",
            "<--",
            "--><=>",
            "!->",
            "a!",
            "a-->",
            "b<=>",
            "<->a",
            "<->",
            "(a&b v2",
            "(a|b"
        );
    }
}
