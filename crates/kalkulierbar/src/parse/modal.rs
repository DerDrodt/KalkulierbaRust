use std::iter::Peekable;

use crate::{logic::LogicNode, Symbol};

use super::{ParseErr, ParseResult, Token, TokenKind, Tokenizer};

pub fn parse_modal_formula(formula: &str) -> ParseResult<(bool, LogicNode)> {
    ModalParser::parse(formula)
}

pub struct ModalParser<'t> {
    tokens: Peekable<Tokenizer<'t>>,
}

impl<'f> ModalParser<'f> {
    pub fn parse(formula: &'f str) -> ParseResult<(bool, LogicNode)> {
        let mut parser = Self {
            tokens: Tokenizer::new(formula, false, true).peekable(),
        };
        if parser.tokens.peek().is_none() {
            return Err(ParseErr::EmptyFormula);
        }
        let (assumption, node) = parser.parse_sign()?;
        match parser.tokens.next() {
            Some(_) => Err(ParseErr::Expected(
                "end of input".to_string(),
                parser.got_msg(),
            )),
            None => Ok((assumption, *node)),
        }
    }

    fn parse_sign(&mut self) -> ParseResult<(bool, Box<LogicNode>)> {
        let assumption = if self.next_is(TokenKind::SignT) {
            self.bump()?;
            self.eat(TokenKind::Colon)?;
            true
        } else if self.next_is(TokenKind::SignF) {
            self.bump()?;
            self.eat(TokenKind::Colon)?;
            false
        } else {
            false
        };

        Ok((assumption, self.parse_equiv()?))
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
            self.parse_box()
        }
    }

    fn parse_box(&mut self) -> ParseResult<Box<LogicNode>> {
        if self.next_is(TokenKind::Box) {
            self.bump()?;
            Ok(Box::new(LogicNode::Box(self.parse_box()?)))
        } else {
            self.parse_diamond()
        }
    }

    fn parse_diamond(&mut self) -> ParseResult<Box<LogicNode>> {
        if self.next_is(TokenKind::Diamond) {
            self.bump()?;
            Ok(Box::new(LogicNode::Diamond(self.parse_box()?)))
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
