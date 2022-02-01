use std::iter::Peekable;

use crate::{
    logic::{fo::FOTerm, LogicNode},
    symbol::Symbol,
};

use super::{ParseErr, ParseResult, Token, TokenKind, Tokenizer};

pub fn parse_fo_formula<'f>(formula: &'f str) -> ParseResult<LogicNode> {
    FOParser::parse(formula)
}

pub fn parse_fo_term<'f>(term: &'f str) -> ParseResult<FOTerm> {
    let mut parser = FOParser::new_term_parser(term);
    let res = parser.parse_term()?;
    match parser.tokens.next() {
        Some(_) => Err(ParseErr::Expected(
            "end of input".to_string(),
            parser.got_msg(),
        )),
        None => Ok(res),
    }
}

struct FOParser<'t> {
    tokens: Peekable<Tokenizer<'t>>,
    quantifier_scope: Vec<Vec<Symbol>>,
    bind_quant_vars: bool,
}

impl<'t> FOParser<'t> {
    fn new(formula: &'t str) -> Self {
        Self {
            tokens: Tokenizer::new(formula, false).peekable(),
            quantifier_scope: Vec::new(),
            bind_quant_vars: true,
        }
    }

    fn new_term_parser(term: &'t str) -> Self {
        Self {
            tokens: Tokenizer::new(term, true).peekable(),
            quantifier_scope: Vec::new(),
            bind_quant_vars: false,
        }
    }

    pub fn parse(formula: &'t str) -> ParseResult<LogicNode> {
        let mut parser = FOParser::new(formula);

        let node = parser.parse_equiv()?;
        match parser.tokens.next() {
            Some(_) => Err(ParseErr::Expected(
                "end of input".to_string(),
                parser.got_msg(),
            )),
            None => Ok(*node),
        }
    }

    pub fn parse_equiv(&mut self) -> ParseResult<Box<LogicNode>> {
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
            Ok(Box::new(LogicNode::Not(self.parse_not()?)))
        } else {
            self.parse_quantifier()
        }
    }

    fn parse_quantifier(&mut self) -> ParseResult<Box<LogicNode>> {
        if !self.next_is(TokenKind::All) && !self.next_is(TokenKind::Ex) {
            return self.parse_paren();
        }

        let kind = self.cur_token()?.kind;
        self.bump()?;

        if !self.next_is(TokenKind::CapIdent) {
            return Err(ParseErr::Expected("quantifier".to_string(), self.got_msg()));
        }

        let name = Symbol::intern(self.cur_token()?.spelling);
        self.bump()?;
        self.eat(TokenKind::Colon)?;

        self.quantifier_scope.push(Vec::new());

        let sub = self.parse_not()?;

        let last_scope = self
            .quantifier_scope
            .remove(self.quantifier_scope.len() - 1);

        let mut bound_before: Vec<Symbol> = last_scope
            .iter()
            .filter_map(|it| if *it != name { Some(*it) } else { None })
            .collect();

        if self.quantifier_scope.is_empty() && !bound_before.is_empty() {
            return Err(ParseErr::UnboundVars(
                bound_before.iter().map(|k| k.to_string()).collect(),
            ));
        }

        if !bound_before.is_empty() {
            self.quantifier_scope
                .last_mut()
                .unwrap()
                .append(&mut bound_before);
        }

        Ok(Box::new(match kind {
            TokenKind::All => LogicNode::All(name, sub),
            TokenKind::Ex => LogicNode::Ex(name, sub),
            _ => panic!(),
        }))
    }

    fn parse_paren(&mut self) -> ParseResult<Box<LogicNode>> {
        if self.next_is(TokenKind::LParen) {
            self.bump()?;
            let exp = self.parse_equiv()?;
            self.eat(TokenKind::RParen)?;
            Ok(exp)
        } else {
            self.parse_atomic()
        }
    }

    fn parse_atomic(&mut self) -> ParseResult<Box<LogicNode>> {
        if !self.next_is(TokenKind::CapIdent) {
            return Err(ParseErr::Expected(
                "relation identifier".to_string(),
                self.got_msg(),
            ));
        }

        let rel_id = Symbol::intern(self.cur_token()?.spelling);
        self.bump()?;
        self.eat(TokenKind::LParen)?;

        let mut args = vec![self.parse_term()?];
        while self.next_is(TokenKind::Comma) {
            self.bump()?;
            args.push(self.parse_term()?);
        }

        self.eat(TokenKind::RParen)?;
        Ok(Box::new(LogicNode::Rel(rel_id, args)))
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

        if self.quantifier_scope.is_empty() && self.bind_quant_vars {
            return Err(ParseErr::UnboundVar(self.got_msg()));
        }

        if self.bind_quant_vars {
            self.quantifier_scope.last_mut().unwrap().push(spelling);
        }

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

    fn cur_token(&mut self) -> ParseResult<&Token<'t>> {
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
