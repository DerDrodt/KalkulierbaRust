use std::{
    collections::{HashMap, HashSet},
    iter::Peekable,
};

use crate::{
    logic::{fo::FOTerm, LogicNode},
    symbol::Symbol,
};

use super::{ParseErr, ParseResult, Token, TokenKind, Tokenizer};

pub fn parse_fo_formula(formula: &str) -> ParseResult<LogicNode> {
    FOParser::parse(formula)
}

pub fn parse_fo_term(term: &str) -> ParseResult<FOTerm> {
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
    quantifier_scope: Vec<Symbol>,
    bind_quant_vars: bool,
    arities: HashMap<Symbol, usize>,
    consts: HashSet<Symbol>,
    fns: HashSet<Symbol>,
    rels: HashSet<Symbol>,
    bound_vars: HashSet<Symbol>,
}

impl<'t> FOParser<'t> {
    fn new(formula: &'t str) -> Self {
        Self {
            tokens: Tokenizer::new(formula, false).peekable(),
            quantifier_scope: Vec::new(),
            bind_quant_vars: true,
            arities: HashMap::new(),
            consts: HashSet::new(),
            fns: HashSet::new(),
            rels: HashSet::new(),
            bound_vars: HashSet::new(),
        }
    }

    fn new_term_parser(term: &'t str) -> Self {
        Self {
            tokens: Tokenizer::new(term, true).peekable(),
            quantifier_scope: Vec::new(),
            bind_quant_vars: false,
            arities: HashMap::new(),
            consts: HashSet::new(),
            fns: HashSet::new(),
            rels: HashSet::new(),
            bound_vars: HashSet::new(),
        }
    }

    pub fn parse(formula: &'t str) -> ParseResult<LogicNode> {
        let mut parser = FOParser::new(formula);
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

        let mut names = Vec::new();
        let name = Symbol::intern(self.cur_token()?.spelling);
        names.push(name);
        self.quantifier_scope.push(name);
        self.bump()?;
        while !self.next_is(TokenKind::Colon) {
            self.eat(TokenKind::Comma)?;
            if !self.next_is(TokenKind::CapIdent) {
                return Err(ParseErr::Expected("quantifier".to_string(), self.got_msg()));
            }
            let name = Symbol::intern(self.cur_token()?.spelling);
            if self.rels.contains(&name) {
                return Err(ParseErr::BoundAndRel(name));
            }
            self.bound_vars.insert(name);
            names.push(name);
            self.quantifier_scope.push(name);
            self.bump()?;
        }
        self.bump()?;

        let quant = match kind {
            TokenKind::All => LogicNode::All,
            TokenKind::Ex => LogicNode::Ex,
            _ => panic!(),
        };

        let mut sub = self.parse_not()?;

        for n in names.iter().rev() {
            self.quantifier_scope.pop();
            sub = Box::new(quant(*n, sub));
        }

        Ok(sub)
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

        let mut args = Vec::new();
        if !self.next_is(TokenKind::RParen) {
            args.push(self.parse_term()?);
            while self.next_is(TokenKind::Comma) {
                self.bump()?;
                args.push(self.parse_term()?);
            }
        }

        self.eat(TokenKind::RParen)?;

        match self.arities.get(&rel_id) {
            Some(&expected) => {
                let arity = args.len();
                if arity != expected {
                    return Err(ParseErr::IncorrectRelArity(rel_id, expected, arity));
                }
            }
            None => {
                self.arities.insert(rel_id, args.len());
            }
        }
        if self.bound_vars.contains(&rel_id) {
            return Err(ParseErr::BoundAndRel(rel_id));
        }

        self.rels.insert(rel_id);

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
                if self.fns.contains(&ident) {
                    return Err(ParseErr::ConstAndFn(ident));
                }
                Ok(FOTerm::Const(ident))
            }
        }
    }

    fn parse_quant_var(&mut self) -> ParseResult<FOTerm> {
        let spelling = Symbol::intern(self.cur_token()?.spelling);

        if self.bind_quant_vars && !self.quantifier_scope.contains(&spelling) {
            return Err(ParseErr::UnboundVar(self.got_msg()));
        }

        self.eat(TokenKind::CapIdent)?;

        if self.rels.contains(&spelling) {
            return Err(ParseErr::BoundAndRel(spelling));
        }

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

        match self.arities.get(&ident) {
            Some(&expected) => {
                let arity = args.len();
                if arity != expected {
                    return Err(ParseErr::IncorrectFnArity(ident, expected, arity));
                }
            }
            None => {
                self.arities.insert(ident, args.len());
            }
        }

        if self.consts.contains(&ident) {
            return Err(ParseErr::ConstAndFn(ident));
        }
        self.fns.insert(ident);

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
            parse_fo_formula,
            "P(c)", "P(c)";
            "\\all X: P(X)", "(∀X: P(X))";
            "\\all X:P(X)", "(∀X: P(X))";
            "\\all X:           P(X)", "(∀X: P(X))";
            "\\all X: \\all Y: \\all Z: R(m(X, m(Y, Z)), m(m(X,Y), Z))", "(∀X: (∀Y: (∀Z: R(m(X, m(Y, Z)), m(m(X, Y), Z)))))";
            "\\ex Xyz: P(Xyz)", "(∃Xyz: P(Xyz))";
            "!\\ex X: (P(X) <-> !P(X))", "¬(∃X: (P(X) <=> ¬P(X)))";
            "!(\\ex X: (P(X) <-> !P(X)))", "¬(∃X: (P(X) <=> ¬P(X)))";
            "\\ex Xyz: P(Xyz) & \\all X: P(X)", "((∃Xyz: P(Xyz)) ∧ (∀X: P(X)))";
            "!/ex X: (P(X) <-> !P(X))", "¬(∃X: (P(X) <=> ¬P(X)))";
            "!(/ex X: (P(X) <-> !P(X)))", "¬(∃X: (P(X) <=> ¬P(X)))";
            "/ex Xyz: P(Xyz) & /all X: P(X)", "((∃Xyz: P(Xyz)) ∧ (∀X: P(X)))";
            "\\ex X, Y: (P(X, Y) -> P(Y, X))", "(∃X: (∃Y: (P(X, Y) → P(Y, X))))";
            "\\all X, Y, Z: (P(X, Y) & P(Y, Z) -> P(X, Z))", "(∀X: (∀Y: (∀Z: ((P(X, Y) ∧ P(Y, Z)) → P(X, Z)))))"
        );
    }

    #[test]
    fn invalid() {
        test_list_invalid!(
            parse_fo_formula,
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
            "(a|b",
            "X",
            "R(X)",
            "\\all X: P(\\all: X: P(X))",
            "\\all X: P(Y)",
            "\\all x: P(X)",
            "\\all X P(X)",
            "\\ex X, x: P(X)",
            "\\ex X, f(X): P(X)",
            "\\ex X, P(X): P(X)",
            "\\ex X, P(x): P(X)",
            "\\ex X, Y, x: P(X)"
        );
    }
}
