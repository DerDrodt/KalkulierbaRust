use std::fmt;

pub use clause_set::{parse_prop_clause_set, CNFStrategy};
pub use prop::parse_prop_formula;

use crate::{
    clause::ClauseSet,
    logic::{fo::Relation, transform::FormulaConversionErr},
    logic::{
        transform::fo_cnf::{fo_cnf, FOCNFErr},
        LogicNode,
    },
    symbol::Symbol,
};

use self::{clause_set::parse_fo_clause_set, fo::parse_fo_formula};

pub mod clause_set;
pub mod fo;
pub mod modal;
pub mod prop;
pub mod sequent;

pub type ParseResult<T> = Result<T, ParseErr>;

pub fn parse_prop_flexible(formula: &str, strategy: CNFStrategy) -> ParseResult<ClauseSet<Symbol>> {
    let likely_formula =
        formula.contains(|c| matches!(c, '&' | '|' | '\\' | '>' | '<' | '=' | '-'));
    /* let likely_clause_set = formula.contains(|c| match c {
        ';' | ',' => true,
        _ => false,
    }); */

    // TODO: DIMACS

    let clause_parse = match parse_prop_clause_set(formula) {
        Ok(res) => {
            return Ok(res);
        }
        Err(e) => e,
    };

    let formula_parse = match parse_prop_formula(formula) {
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

pub enum FOToCNFParseErr {
    ParseErr(ParseErr),
    CNFErr(FOCNFErr),
}

impl From<ParseErr> for FOToCNFParseErr {
    fn from(e: ParseErr) -> Self {
        Self::ParseErr(e)
    }
}

impl From<FOCNFErr> for FOToCNFParseErr {
    fn from(e: FOCNFErr) -> Self {
        Self::CNFErr(e)
    }
}

pub fn parse_fo_flexibly_to_cnf(formula: &str) -> Result<ClauseSet<Relation>, FOToCNFParseErr> {
    let is_formula = formula.contains(|c| matches!(c, '&' | '|' | '\\' | '>' | '<' | '=' | '-'));

    if is_formula {
        let n = parse_fo_formula(formula)?;
        return Ok(fo_cnf(n)?);
    }

    Ok(parse_fo_clause_set(formula)?)
}

fn to_cnf(
    node: LogicNode,
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
    EmptyFormula,
    EmptyFormulaAt(usize),
    BoundAndRel(Symbol),
    IncorrectRelArity(Symbol, usize, usize),
    ConstAndFn(Symbol),
    IncorrectFnArity(Symbol, usize, usize),
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
            ParseErr::UnboundVar(v) => write!(f, "Unbound var {}",v),
            ParseErr::EmptyFormula => write!(f, "Expected a formula but got an empty String"),
            ParseErr::EmptyFormulaAt(pos) => write!(f, "Empty formula at char {pos}"),
            ParseErr::BoundAndRel(name) => write!(f, "Identifier '{name}' is used both as a relation and bound variable"),
            ParseErr::IncorrectRelArity(name, expected, actual) => write!(f, "Relation {name} should have arity {expected} but has {actual}"),
            ParseErr::ConstAndFn(name) => write!(f, "Identifier '{name}' is used both as a function and constant"),
            ParseErr::IncorrectFnArity(name, expected, actual) =>  write!(f, "Function {name} should have arity {expected} but has {actual}"),
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
    Box,
    Diamond,
    Unknown,
    SignT,
    SignF,
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
            TokenKind::Box => "[]",
            TokenKind::Diamond => "<>",
            TokenKind::Unknown => "unknown",
            TokenKind::SignT => r"\sign T",
            TokenKind::SignF => r"\sign F",
        };

        write!(f, "{}", s)
    }
}

pub(crate) struct Tokenizer<'f> {
    formula: &'f str,
    pos: usize,
    extended: bool,
    modal: bool,
}

impl<'f> Tokenizer<'f> {
    pub(crate) fn new(formula: &'f str, extended: bool, modal: bool) -> Self {
        Self {
            formula,
            pos: 0,
            extended,
            modal,
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
            '[' => {
                if self.formula.starts_with("[]") {
                    (TokenKind::Box, "[]", 2)
                } else {
                    return Some(Err(ParseErr::Expected("[]".to_string(), "[".to_string())));
                }
            }
            '<' => {
                if self.formula.starts_with("<=>") {
                    (TokenKind::Equiv, "<=>", 3)
                } else if self.formula.starts_with("<->") {
                    (TokenKind::Equiv, "<->", 3)
                } else if self.modal && self.formula.starts_with("<>") {
                    (TokenKind::Diamond, "<>", 2)
                } else if self.modal {
                    return Some(Err(ParseErr::Expected(
                        "<=> or <>".to_string(),
                        "<".to_string(),
                    )));
                } else {
                    return Some(Err(ParseErr::Expected("<=>".to_string(), "<".to_string())));
                }
            }
            '\\' | '/' => {
                if self.formula.starts_with("\\ex") | self.formula.starts_with("/ex") {
                    (TokenKind::Ex, "\\ex", 3)
                } else if self.formula.starts_with("\\all") | self.formula.starts_with("/all") {
                    (TokenKind::All, "\\all", 4)
                } else if self.modal & self.formula.starts_with(r"\sign T") {
                    (TokenKind::SignT, r"\sign T", 7)
                } else if self.modal & self.formula.starts_with(r"\sign F") {
                    (TokenKind::SignF, r"\sign F", 7)
                } else {
                    return Some(Err(ParseErr::Expected(
                        if self.modal {
                            "Quantifier or sign"
                        } else {
                            "Quantifier"
                        }
                        .to_string(),
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
