use std::fmt;

pub use clause_set::{parse_clause_set, CNFStrategy};
pub use prop::parse_prop_formula;

use crate::{
    clause::ClauseSet, logic::transform::FormulaConversionErr, logic::LogicNode, symbol::Symbol,
};

pub mod clause_set;
pub mod fo;
pub mod prop;

pub type ParseResult<T> = Result<T, ParseErr>;

pub fn parse_flexible(formula: &str, strategy: CNFStrategy) -> ParseResult<ClauseSet<Symbol>> {
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

    let formula_parse = match parse_prop_formula(formula) {
        Ok(res) => {
            return Ok(to_cnf(&res, strategy).unwrap());
        }
        Err(e) => e,
    };

    Err(if likely_formula {
        formula_parse
    } else {
        clause_parse
    })
}

fn to_cnf(
    node: &LogicNode,
    strategy: CNFStrategy,
) -> Result<ClauseSet<Symbol>, FormulaConversionErr> {
    match strategy {
        CNFStrategy::Naive => node.naive_cnf(),
        CNFStrategy::Tseytin => node.tseytin_cnf(),
        CNFStrategy::Optimal => {
            if let Ok(res) = node.naive_cnf() {
                Ok(res)
            } else {
                node.tseytin_cnf()
            }
        }
    }
}

#[derive(Debug, Eq, PartialEq, Clone)]
pub enum ParseErr {
    Expected(String, String),
    InvalidFormat,
    UnboundVar(String),
    UnboundVars(Vec<String>),
    EmptyToken,
}

impl fmt::Display for ParseErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErr::Expected(expected, got) => write!(f, "Expected {} but got {}", expected, got),
            ParseErr::InvalidFormat => write!(f, "Please use alphanumeric variables only, separate atoms with ',' and clauses with ';'."),
            ParseErr::EmptyToken => write!(f, "Encountered an empty token"),
            ParseErr::UnboundVars(v) => {
                let mut vs = String::new();

                for (i, var) in v.iter().enumerate() {
                    if i > 0 {
                        vs.push_str(", ");
                    }
                    vs.push_str(var);
                }

                write!(f, "Unbound variables found: {}", vs)
            }
            ParseErr::UnboundVar(v) => write!(f, "Unbound var {}",v)
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Token<'t> {
    pub kind: TokenKind,
    pub spelling: &'t str,
    pub src_pos: usize,
}

impl<'t> fmt::Display for Token<'t> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.spelling)
    }
}
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum TokenKind {
    And,
    Or,
    Not,
    Impl,
    Equiv,
    LParen,
    RParen,
    Comma,
    Colon,
    CapIdent,
    LowIdent,
    All,
    Ex,
    Unknown,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            TokenKind::And => "&",
            TokenKind::Or => "|",
            TokenKind::Not => "!",
            TokenKind::Impl => "->",
            TokenKind::Equiv => "<->",
            TokenKind::LParen => "(",
            TokenKind::RParen => ")",
            TokenKind::Comma => ",",
            TokenKind::Colon => ":",
            TokenKind::CapIdent => "capitalized identifier",
            TokenKind::LowIdent => "lower identifier",
            TokenKind::All => "\\all",
            TokenKind::Ex => "\\ex",
            TokenKind::Unknown => "unknown",
        };

        write!(f, "{}", s)
    }
}

struct Tokenizer<'f> {
    formula: &'f str,
    pos: usize,
    extended: bool,
}

impl<'f> Tokenizer<'f> {
    fn new(formula: &'f str, extended: bool) -> Self {
        Self {
            formula,
            pos: 0,
            extended,
        }
    }

    fn next_token(&mut self) -> Option<ParseResult<Token<'f>>> {
        if self.formula.is_empty() {
            return None;
        }

        let (kind, spelling, size) = match self.formula.chars().next().unwrap() {
            '&' => (TokenKind::And, "&", 1),
            '|' => (TokenKind::Or, "|", 1),
            '!' => (TokenKind::Not, "!", 1),
            '(' => (TokenKind::LParen, "(", 1),
            ')' => (TokenKind::RParen, ")", 1),
            ',' => (TokenKind::Comma, ",", 1),
            ':' => (TokenKind::Colon, ":", 1),
            '-' => {
                if self.formula.starts_with("->") {
                    (TokenKind::Impl, "->", 2)
                } else {
                    return Some(Err(ParseErr::Expected("->".to_string(), "-".to_string())));
                }
            }
            '<' => {
                let spelling = if self.formula.starts_with("<=>") {
                    "<=>"
                } else if self.formula.starts_with("<->") {
                    "<->"
                } else {
                    return Some(Err(ParseErr::Expected("<=>".to_string(), "<".to_string())));
                };

                (TokenKind::Equiv, spelling, 3)
            }
            '\\' => {
                if self.formula.starts_with("\\ex") {
                    (TokenKind::Ex, "\\ex", 3)
                } else if self.formula.starts_with("\\all") {
                    (TokenKind::All, "\\all", 4)
                } else {
                    return Some(Err(ParseErr::Expected(
                        "Quantifier".to_string(),
                        "\\".to_string(),
                    )));
                }
            }
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

impl<'f> Iterator for Tokenizer<'f> {
    type Item = ParseResult<Token<'f>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.formula.is_empty() {
            None
        } else {
            self.next_token()
        }
    }
}
