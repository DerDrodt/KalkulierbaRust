use std::fmt;

pub use clause_set::{parse_clause_set, CNFStrategy};
pub use prop::parse_prop_formula;
use transform::Lit;

use crate::{
    clause::ClauseSet,
    logic::transform::{self, FormulaConversionErr},
    logic::LogicNode,
};

pub mod clause_set;
pub mod prop;

pub type ParseResult<T> = Result<T, ParseErr>;

pub fn parse_flexible<'f>(
    formula: &'f str,
    strategy: CNFStrategy,
) -> ParseResult<ClauseSet<Lit<'f>>> {
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

fn to_cnf<'f>(
    node: &LogicNode<'f>,
    strategy: CNFStrategy,
) -> Result<ClauseSet<Lit<'f>>, FormulaConversionErr> {
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

#[derive(Debug, Eq, PartialEq)]
pub enum ParseErr {
    Expected(String, String),
    InvalidFormat,
    EmptyToken,
}

impl fmt::Display for ParseErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseErr::Expected(expected, got) => write!(f, "Expected {} but got {}", expected, got),
            ParseErr::InvalidFormat => write!(f, "Please use alphanumeric variables only, separate atoms with ',' and clauses with ';'."),
            ParseErr::EmptyToken => write!(f, "Encountered an empty token"),
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
#[derive(Debug, PartialEq, Eq, Clone)]
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

pub fn tokenize(formula: &str) -> ParseResult<Vec<Token>> {
    let mut f = formula;

    let mut tokens: Vec<Token> = vec![];

    while !f.is_empty() {
        let pos = match tokens.last() {
            Some(t) => t.src_pos + t.spelling.len(),
            None => 0,
        };
        f = extract_token(f, &mut tokens, pos)?;
    }

    Ok(tokens)
}

fn extract_token<'a>(
    formula: &'a str,
    tokens: &mut Vec<Token<'a>>,
    pos: usize,
) -> ParseResult<&'a str> {
    Ok(
        if formula.starts_with(|c| match c {
            '&' | '|' | '!' | '(' | ')' | ',' | ':' => true,
            _ => false,
        }) {
            let tt = match formula.chars().next().unwrap() {
                '&' => TokenKind::And,
                '|' => TokenKind::Or,
                '!' => TokenKind::Not,
                '(' => TokenKind::LParen,
                ')' => TokenKind::RParen,
                ',' => TokenKind::Comma,
                ':' => TokenKind::Colon,
                _ => TokenKind::Unknown,
            };
            tokens.push(Token {
                kind: tt,
                spelling: &formula[0..1],
                src_pos: pos,
            });
            &formula[1..]
        } else if formula.starts_with("->") {
            tokens.push(Token {
                kind: TokenKind::Impl,
                spelling: "->",
                src_pos: pos + 2,
            });
            &formula[2..]
        } else if formula.starts_with("<->") {
            tokens.push(Token {
                kind: TokenKind::Equiv,
                spelling: "<->",
                src_pos: pos + 3,
            });
            &formula[3..]
        } else if formula.starts_with("<=>") {
            tokens.push(Token {
                kind: TokenKind::Equiv,
                spelling: "<=>",
                src_pos: pos + 3,
            });
            &formula[3..]
        } else if formula.starts_with("\\ex") {
            tokens.push(Token {
                kind: TokenKind::Equiv,
                spelling: "\\ex",
                src_pos: pos + 3,
            });
            &formula[3..]
        } else if formula.starts_with("\\all") {
            tokens.push(Token {
                kind: TokenKind::Equiv,
                spelling: "\\all",
                src_pos: pos + 4,
            });
            &formula[pos + 4..]
        } else if formula.starts_with(|c: char| c.is_whitespace()) {
            &formula[1..]
        } else {
            let mut i = 0;

            for c in formula.chars() {
                match c {
                    'a'..='z' | 'A'..='Z' | '0'..='9' => {
                        i += 1;
                    }
                    '_' | '-' => break,
                    _ => break,
                }
            }

            let spelling = &formula[0..i];

            if spelling.is_empty() {
                return Err(ParseErr::EmptyToken);
            }

            let first = spelling.chars().next().unwrap();
            let kind = match first {
                'A'..='Z' => TokenKind::CapIdent,
                _ => TokenKind::LowIdent,
            };

            tokens.push(Token {
                kind,
                spelling,
                src_pos: pos,
            });

            &formula[i..]
        },
    )
}
