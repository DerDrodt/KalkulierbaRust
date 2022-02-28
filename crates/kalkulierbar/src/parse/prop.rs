use std::iter::Peekable;

use crate::{
    logic::LogicNode,
    parse::{ParseErr, ParseResult, Token, TokenKind},
    symbol::Symbol,
};

use super::Tokenizer;

pub fn parse_prop_formula(formula: &str) -> ParseResult<LogicNode> {
    PropParser::parse(formula)
}

pub struct PropParser<'t> {
    tokens: Peekable<Tokenizer<'t>>,
}

impl<'f> PropParser<'f> {
    pub fn parse(formula: &'f str) -> ParseResult<LogicNode> {
        let mut parser = PropParser {
            tokens: Tokenizer::new(formula, false).peekable(),
        };
        if parser.tokens.peek().is_none() {
            return Err(ParseErr::EmptyFormula);
        }
        let node = parser.parse_equiv()?;
        match parser.tokens.next() {
            Some(_) => Err(ParseErr::Expected(
                "end of input".to_string(),
                parser.got_msg(),
            )),
            None => Ok(*node),
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

        let exp = Box::new(LogicNode::Var(Symbol::intern(self.cur_token()?.spelling)));
        self.bump()?;
        Ok(exp)
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
