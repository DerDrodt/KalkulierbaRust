use crate::{
    logic::LogicNode,
    parse::{self, ParseErr, ParseResult, Token, TokenKind},
};

pub fn parse_prop_formula<'f>(formula: &'f str) -> ParseResult<LogicNode<'f>> {
    PropParser::parse(formula)
}

pub struct PropParser<'t> {
    tokens: Vec<Token<'t>>,
}

impl<'f> PropParser<'f> {
    pub fn parse(formula: &'f str) -> ParseResult<LogicNode<'f>> {
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

    fn parse_equiv(&mut self) -> ParseResult<Box<LogicNode<'f>>> {
        let mut stub = self.parse_impl()?;

        while self.next_is(TokenKind::Equiv) {
            self.bump()?;
            let right = self.parse_impl()?;
            stub = Box::new(LogicNode::Equiv(stub, right));
        }

        Ok(stub)
    }

    fn parse_impl(&mut self) -> ParseResult<Box<LogicNode<'f>>> {
        let mut stub = self.parse_or()?;

        while self.next_is(TokenKind::Impl) {
            self.bump()?;
            let right = self.parse_or()?;
            stub = Box::new(LogicNode::Impl(stub, right));
        }

        Ok(stub)
    }

    fn parse_or(&mut self) -> ParseResult<Box<LogicNode<'f>>> {
        let mut stub = self.parse_and()?;

        while self.next_is(TokenKind::Or) {
            self.bump()?;
            let right = self.parse_and()?;
            stub = Box::new(LogicNode::Or(stub, right));
        }

        Ok(stub)
    }

    fn parse_and(&mut self) -> ParseResult<Box<LogicNode<'f>>> {
        let mut stub = self.parse_not()?;

        while self.next_is(TokenKind::And) {
            self.bump()?;
            let right = self.parse_not()?;
            stub = Box::new(LogicNode::And(stub, right));
        }

        Ok(stub)
    }

    fn parse_not(&mut self) -> ParseResult<Box<LogicNode<'f>>> {
        if self.next_is(TokenKind::Not) {
            self.bump()?;
            Ok(Box::new(LogicNode::Not(self.parse_paren()?)))
        } else {
            self.parse_paren()
        }
    }

    fn parse_paren(&mut self) -> ParseResult<Box<LogicNode<'f>>> {
        if self.next_is(TokenKind::LParen) {
            self.bump()?;
            let exp = self.parse_equiv()?;
            self.eat(TokenKind::RParen)?;
            Ok(exp)
        } else {
            self.parse_var()
        }
    }

    fn parse_var(&mut self) -> ParseResult<Box<LogicNode<'f>>> {
        if !self.next_is_id() {
            return Err(ParseErr::Expected("identifier".to_string(), self.got_msg()));
        }

        let exp = Box::new(LogicNode::Var(self.cur_token()?.spelling));
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

    fn cur_token(&self) -> ParseResult<&Token<'f>> {
        self.tokens.last().ok_or(ParseErr::Expected(
            "token".to_string(),
            "end of input".to_string(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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
