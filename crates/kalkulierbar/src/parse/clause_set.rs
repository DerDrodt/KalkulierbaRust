use std::{fmt, iter::Peekable};

use serde::{Deserialize, Serialize};

use super::{ParseErr, ParseResult};
use crate::clause::{Atom, Clause, ClauseSet};
use crate::logic::fo::{FOTerm, Relation};
use crate::symbol::Symbol;

#[derive(Deserialize, Serialize)]
pub enum CNFStrategy {
    #[serde(rename = "NAIVE")]
    Naive,
    #[serde(rename = "TSEYTIN")]
    Tseytin,
    #[serde(rename = "OPTIMAL")]
    Optimal,
}

impl Default for CNFStrategy {
    fn default() -> Self {
        Self::Optimal
    }
}

pub fn parse_prop_clause_set(formula: &str) -> ParseResult<ClauseSet<Symbol>> {
    PropClauseSetParser::parse(formula)
}

pub fn parse_fo_clause_set(formula: &str) -> ParseResult<ClauseSet<Relation>> {
    FOClauseSetParser::parse(formula)
}

#[derive(Debug, PartialEq, Eq)]
struct Token<'t> {
    pub kind: TokenKind,
    pub spelling: &'t str,
    pub src_pos: usize,
}

impl<'t> fmt::Display for Token<'t> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.spelling)
    }
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
enum TokenKind {
    Comma,
    Semi,
    Not,
    LParen,
    RParen,
    CapIdent,
    LowIdent,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Comma => write!(f, ","),
            TokenKind::Semi => write!(f, ";"),
            TokenKind::Not => write!(f, "!"),
            TokenKind::CapIdent => write!(f, "capitalized identifier"),
            TokenKind::LowIdent => write!(f, "lower identifier"),
            TokenKind::LParen => write!(f, "("),
            TokenKind::RParen => write!(f, ")"),
        }
    }
}

struct ClauseSetTokenizer<'f> {
    formula: &'f str,
    pos: usize,
    extended: bool,
}

impl<'f> ClauseSetTokenizer<'f> {
    pub fn new(formula: &'f str) -> Self {
        Self {
            formula,
            pos: 0,
            extended: false,
        }
    }

    fn next_token(&mut self) -> Option<ParseResult<Token<'f>>> {
        if self.formula.is_empty() {
            return None;
        }

        let (kind, spelling, size) = match self.formula.chars().next().unwrap() {
            ';' | '\n' => (TokenKind::Semi, ";", 1),
            ',' => (TokenKind::Comma, ",", 1),
            '!' => (TokenKind::Not, "!", 1),
            '(' => (TokenKind::LParen, "(", 1),
            ')' => (TokenKind::RParen, ")", 1),
            c if c.is_whitespace() => {
                self.pos += 1;
                self.formula = &self.formula[1..];
                return self.next_token();
            }
            _ => {
                let mut i = 0;
                for c in self.formula.chars() {
                    match c {
                        'a'..='z' | 'A'..='Z' | '0'..='9' => i += 1,
                        '-' | '_' if i > 0 && self.extended => i += 1,
                        _ => break,
                    }
                }
                let spelling = &self.formula[0..i];

                if spelling.is_empty() {
                    return None;
                }

                let first = spelling.chars().next().unwrap();
                let tt = match first {
                    'A'..='Z' => TokenKind::CapIdent,
                    _ => TokenKind::LowIdent,
                };

                (tt, spelling, i)
            }
        };

        let t = Token {
            kind,
            spelling,
            src_pos: self.pos,
        };
        self.pos += size;
        self.formula = &self.formula[size..];
        Some(Ok(t))
    }
}

impl<'f> Iterator for ClauseSetTokenizer<'f> {
    type Item = ParseResult<Token<'f>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.formula.is_empty() {
            None
        } else {
            self.next_token()
        }
    }
}

impl<'f> From<&'f str> for ClauseSetTokenizer<'f> {
    fn from(f: &'f str) -> Self {
        ClauseSetTokenizer::new(f)
    }
}

pub struct PropClauseSetParser<'f> {
    tokens: Peekable<ClauseSetTokenizer<'f>>,
}

impl<'f> PropClauseSetParser<'f> {
    pub fn parse(formula: &'f str) -> ParseResult<ClauseSet<Symbol>> {
        let tokens: ClauseSetTokenizer = formula.into();
        let p = tokens.peekable();
        let mut parser = PropClauseSetParser { tokens: p };
        parser.parse_cs()
    }

    fn parse_cs(&mut self) -> ParseResult<ClauseSet<Symbol>> {
        let mut cs = vec![self.parse_c()?];

        while self.semi() && self.tokens.peek().is_some() {
            cs.push(self.parse_c()?);
        }

        Ok(ClauseSet::new(cs))
    }

    fn parse_c(&mut self) -> ParseResult<Clause<Symbol>> {
        let mut c = vec![self.parse_atom()?];

        while self.comma() {
            c.push(self.parse_atom()?)
        }

        Ok(Clause::new(c))
    }

    fn parse_atom(&mut self) -> ParseResult<Atom<Symbol>> {
        let negated = self.em();
        Ok(Atom::new(self.parse_spelling()?, negated))
    }

    fn parse_spelling(&mut self) -> ParseResult<Symbol> {
        match self.tokens.next() {
            Some(Err(e)) => Err(e),
            Some(Ok(Token {
                spelling,
                kind: TokenKind::LowIdent,
                ..
            }))
            | Some(Ok(Token {
                spelling,
                kind: TokenKind::CapIdent,
                ..
            })) => Ok(Symbol::intern(spelling)),
            Some(Ok(t)) => Err(ParseErr::Expected("identifier".to_string(), t.to_string())),
            None => Err(ParseErr::Expected(
                "identifier".to_string(),
                "end of input".to_string(),
            )),
        }
    }

    fn eat_if_kind(&mut self, expected: TokenKind) -> bool {
        match self.tokens.peek() {
            Some(Ok(Token { kind, .. })) => {
                if *kind == expected {
                    self.tokens.next();
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn semi(&mut self) -> bool {
        self.eat_if_kind(TokenKind::Semi)
    }

    fn comma(&mut self) -> bool {
        self.eat_if_kind(TokenKind::Comma)
    }

    fn em(&mut self) -> bool {
        self.eat_if_kind(TokenKind::Not)
    }
}

pub struct FOClauseSetParser<'f> {
    tokens: Peekable<ClauseSetTokenizer<'f>>,
}

impl<'f> FOClauseSetParser<'f> {
    pub fn parse(formula: &'f str) -> ParseResult<ClauseSet<Relation>> {
        let tokens: ClauseSetTokenizer = formula.into();
        let p = tokens.peekable();
        let mut parser = FOClauseSetParser { tokens: p };
        parser.parse_cs()
    }

    fn parse_cs(&mut self) -> ParseResult<ClauseSet<Relation>> {
        let mut cs = vec![self.parse_c()?];

        while self.semi() && self.tokens.peek().is_some() {
            cs.push(self.parse_c()?);
        }

        Ok(ClauseSet::new(cs))
    }

    fn parse_c(&mut self) -> ParseResult<Clause<Relation>> {
        let mut c = vec![self.parse_lit()?];

        while self.comma() {
            c.push(self.parse_lit()?)
        }

        Ok(Clause::new(c))
    }

    fn parse_lit(&mut self) -> ParseResult<Atom<Relation>> {
        let negated = self.em();
        Ok(Atom::new(self.parse_rel()?, negated))
    }

    fn parse_rel(&mut self) -> ParseResult<Relation> {
        if !self.next_is(TokenKind::CapIdent) {
            return Err(ParseErr::Expected(
                "relation identifier".to_string(),
                self.got_msg(),
            ));
        }

        let rel_id = Symbol::intern(self.cur_token()?.spelling);
        self.bump()?;
        self.eat(TokenKind::LParen)?;

        let mut args = Vec::new();
        if !self.next_is(TokenKind::RParen) {
            args.push(self.parse_term()?);
            while self.next_is(TokenKind::Comma) {
                self.bump()?;
                args.push(self.parse_term()?);
            }
        }

        self.eat(TokenKind::RParen)?;
        Ok(Relation::new(rel_id, args))
    }

    fn parse_term(&mut self) -> ParseResult<FOTerm> {
        if !self.next_is_id() {
            return Err(ParseErr::Expected("identifier".to_string(), self.got_msg()));
        }

        if self.next_is(TokenKind::CapIdent) {
            self.parse_quant_var()
        } else {
            let ident = Symbol::intern(self.cur_token()?.spelling);
            self.bump()?;
            if self.next_is(TokenKind::LParen) {
                self.parse_fn(ident)
            } else {
                Ok(FOTerm::Const(ident))
            }
        }
    }

    fn parse_quant_var(&mut self) -> ParseResult<FOTerm> {
        let spelling = Symbol::intern(self.cur_token()?.spelling);

        self.eat(TokenKind::CapIdent)?;

        Ok(FOTerm::QuantifiedVar(spelling))
    }

    fn parse_fn(&mut self, ident: Symbol) -> ParseResult<FOTerm> {
        self.eat(TokenKind::LParen)?;

        let mut args = vec![self.parse_term()?];
        while self.next_is(TokenKind::Comma) {
            self.bump()?;
            args.push(self.parse_term()?);
        }

        self.eat(TokenKind::RParen)?;
        Ok(FOTerm::Function(ident, args))
    }

    fn eat_if_kind(&mut self, expected: TokenKind) -> bool {
        match self.tokens.peek() {
            Some(Ok(Token { kind, .. })) => {
                if *kind == expected {
                    self.tokens.next();
                    true
                } else {
                    false
                }
            }
            _ => false,
        }
    }

    fn semi(&mut self) -> bool {
        self.eat_if_kind(TokenKind::Semi)
    }

    fn comma(&mut self) -> bool {
        self.eat_if_kind(TokenKind::Comma)
    }

    fn em(&mut self) -> bool {
        self.eat_if_kind(TokenKind::Not)
    }

    fn next_is(&mut self, expected: TokenKind) -> bool {
        match self.tokens.peek() {
            Some(Ok(Token { kind, .. })) => *kind == expected,
            _ => false,
        }
    }

    fn next_is_id(&mut self) -> bool {
        self.next_is(TokenKind::CapIdent) || self.next_is(TokenKind::LowIdent)
    }

    fn bump(&mut self) -> ParseResult<()> {
        match self.tokens.next() {
            Some(_) => Ok(()),
            None => Err(ParseErr::Expected(
                "token".to_string(),
                "end of input".to_string(),
            )),
        }
    }

    fn eat(&mut self, expected: TokenKind) -> ParseResult<()> {
        if self.next_is(expected) {
            self.bump()
        } else {
            Err(ParseErr::Expected(expected.to_string(), self.got_msg()))
        }
    }

    fn got_msg(&mut self) -> String {
        match self.tokens.peek() {
            Some(Ok(t)) => format!("{} at position {}", t, t.src_pos),
            _ => "end of input".to_string(),
        }
    }

    fn cur_token(&mut self) -> ParseResult<&Token<'f>> {
        match self.tokens.peek() {
            Some(Ok(t)) => Ok(t),
            Some(Err(e)) => Err(e.clone()),
            _ => Err(ParseErr::Expected(
                "token".to_string(),
                "end of input".to_string(),
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session;

    macro_rules! test_map {
        ($func:ident, $( $f:expr, $e:expr );*) => {{
            $(
                session(|| {
                    let cs = $func($f).expect($f);
                    assert_eq!($e, cs.to_string());
                });
            )*
        }};
    }

    macro_rules! test_list_invalid {
        ($func:ident, $( $f:expr ),*) => {{
            $(
                session(|| {
                    let res = $func($f);
                    assert!(res.is_err(), "f: {}\nCS: {:?}", $f, res);
                });
            )*
        }};
    }

    #[test]
    fn valid() {
        test_map!(
            parse_prop_clause_set,
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
    fn invalid() {
        test_list_invalid!(
            parse_prop_clause_set,
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
}
