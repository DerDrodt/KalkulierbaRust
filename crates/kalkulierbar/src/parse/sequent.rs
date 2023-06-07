use crate::logic::{transform::remove_equivs::remove_equivs, LogicNode};

use super::{fo::parse_fo_formula, parse_prop_formula, ParseErr, ParseResult};

pub fn parse_prop(formula: &str) -> ParseResult<(Vec<LogicNode>, Vec<LogicNode>)> {
    parse(formula, parse_prop_formula, |s| s.split(',').collect())
}

pub fn parse_fo(formula: &str) -> ParseResult<(Vec<LogicNode>, Vec<LogicNode>)> {
    parse(formula, parse_fo_formula, split_fo_formulas)
}

fn split_fo_formulas(s: &str) -> Vec<&str> {
    let mut fs = vec![];

    let mut parens = 0;
    let mut start_of_formula = 0;

    for (i, c) in s.chars().enumerate() {
        match c {
            '(' => parens += 1,
            ')' => parens -= 1,
            ',' if parens == 0 => {
                fs.push(&s[start_of_formula..i]);
                start_of_formula = i + 1;
            }
            _ => {}
        }
    }

    fs.push(&s[start_of_formula..s.len()]);
    fs
}

pub fn parse<P, S>(formula: &str, p: P, s: S) -> ParseResult<(Vec<LogicNode>, Vec<LogicNode>)>
where
    P: Fn(&str) -> ParseResult<LogicNode>,
    S: Fn(&str) -> Vec<&str>,
{
    // Find left and right formulas in the input string
    let sides: Vec<_> = formula.split("|-").collect();

    // If there is more than one '|-' in the input sting throw an error
    if sides.len() > 2 {
        let i = sides[0].len() + 2 + sides[1].len();
        return Err(ParseErr::Expected(
            "end of input or ','".to_string(),
            format!("|- at {i}"),
        ));
    }
    if sides.len() == 2 {
        let left = parse_formulas(sides[0], 0, &p, &s)?;
        let right = parse_formulas(sides[1], sides[0].len() + 2, &p, &s)?;
        Ok((left, right))
    } else {
        Ok((vec![], parse_formulas(sides[0], 0, &p, s)?))
    }
}

fn parse_formulas<P, S>(formulas: &str, pos: usize, p: &P, s: S) -> ParseResult<Vec<LogicNode>>
where
    P: Fn(&str) -> ParseResult<LogicNode>,
    S: Fn(&str) -> Vec<&str>,
{
    let input = s(formulas);
    let len = input.len();

    input
        .iter()
        .enumerate()
        .filter_map(|(i, f)| {
            let parsed = match p(f) {
                Ok(p) => p,
                Err(ParseErr::EmptyFormula) if i != 0 || len != 1 => {
                    return Some(Err(ParseErr::EmptyFormulaAt(pos)))
                }
                Err(ParseErr::EmptyFormula) => return None,
                Err(e) => return Some(Err(e)),
            };
            let n = remove_equivs(parsed);
            Some(Ok(n))
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::session;

    mod prop {
        use crate::calculi::sequent::{prop::PropSeqMove, SequentNode};

        use super::*;

        #[test]
        fn invalid() {
            session(|| {
                for s in [
                    "-->a", "<--", "--><=>", "!->", "a!", "a-->", "b<=>", "<->a", "<->", "(a&b v2",
                    "(a|b", "|- ,,", ",, |-", "|- a |-", "( |- )", "a | |- b", "a |- b a",
                ] {
                    assert!(parse_prop(s).is_err(), "{} did not fail", s)
                }
            })
        }

        #[test]
        fn valid() {
            let valid = [
                ("", " ⊢ "),
                ("a", " ⊢ a"),
                ("!a", " ⊢ ¬a"),
                ("a -> b", " ⊢ (a → b)"),
                ("a-> b", " ⊢ (a → b)"),
                ("a    ->b", " ⊢ (a → b)"),
                ("a->b", " ⊢ (a → b)"),
                ("a<->(b -> (!(c)))", " ⊢ ((a → (b → ¬c)) ∧ ((b → ¬c) → a))"),
                (
                    "(b & a <-> (a) | !b)",
                    " ⊢ (((b ∧ a) → (a ∨ ¬b)) ∧ ((a ∨ ¬b) → (b ∧ a)))",
                ),
                ("|- a", " ⊢ a"),
                ("|-!a", " ⊢ ¬a"),
                ("    |-    a -> b", " ⊢ (a → b)"),
                (" |- a-> b", " ⊢ (a → b)"),
                ("|- a    ->b", " ⊢ (a → b)"),
                ("a |-", "a ⊢ "),
                ("!a |-", "¬a ⊢ "),
                ("a -> b |-", "(a → b) ⊢ "),
                ("a-> b |-", "(a → b) ⊢ "),
                ("a    ->b |-", "(a → b) ⊢ "),
                ("a->b |-", "(a → b) ⊢ "),
                (
                    "a<->(b -> (!(c))) |-",
                    "((a → (b → ¬c)) ∧ ((b → ¬c) → a)) ⊢ ",
                ),
                (
                    "(b & a <-> (a) | !b)                 |-",
                    "(((b ∧ a) → (a ∨ ¬b)) ∧ ((a ∨ ¬b) → (b ∧ a))) ⊢ ",
                ),
                (" |- a,b", " ⊢ a, b"),
                (
                    "a,b,c,d,e,f |- g,h,i,j,k,l",
                    "a, b, c, d, e, f ⊢ g, h, i, j, k, l",
                ),
                (
                    "a & b -> c, a | c |- d <-> e",
                    "((a ∧ b) → c), (a ∨ c) ⊢ ((d → e) ∧ (e → d))",
                ),
            ];

            session(|| {
                for (f, e) in valid {
                    let (l, r) = parse_prop(f).expect(e);
                    let n = SequentNode::<PropSeqMove>::new(None, l, r, None);
                    assert_eq!(e, n.to_string());
                }
            })
        }
    }

    mod fo {
        use super::*;
        use crate::calculi::sequent::{fo::FOSeqMove, SequentNode};

        #[test]
        fn invalid() {
            session(|| {
                for s in [
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
                    "|- ,,",
                    ",, |-",
                    "|- a |-",
                    "( |- )",
                    "a | |- b",
                    "a |- b a",
                    "X",
                    "R(X)",
                    "R(X) |-",
                    "|- R(X)",
                    "|- R(X), R(X)",
                    "\\all X: P(\\all: X: P(X))",
                    "\\all X: P(Y)",
                    "\\all x: P(X)",
                    "\\all X P(X)",
                ] {
                    assert!(parse_fo(s).is_err(), "{} did not fail", s)
                }
            })
        }

        #[test]
        fn valid() {
            let valid = [
                ("P(c)", " ⊢ P(c)"),
                ("\\all X: P(X)", " ⊢ (∀X: P(X))"),
                ("\\all X:P(X)", " ⊢ (∀X: P(X))"),
                ("\\all X:           P(X)", " ⊢ (∀X: P(X))"),
                ("\\all X: \\all Y: \\all Z: R(m(X, m(Y, Z)), m(m(X,Y), Z))", " ⊢ (∀X: (∀Y: (∀Z: R(m(X, m(Y, Z)), m(m(X, Y), Z)))))"),
                ("\\ex Xyz: P(Xyz)", " ⊢ (∃Xyz: P(Xyz))"),
                ("!\\ex X: (P(X) <-> !P(X))", " ⊢ ¬(∃X: ((P(X) → ¬P(X)) ∧ (¬P(X) → P(X))))"),
                ("!(\\ex X: (P(X) <-> !P(X)))", " ⊢ ¬(∃X: ((P(X) → ¬P(X)) ∧ (¬P(X) → P(X))))"),
                ("\\ex Xyz: P(Xyz) & \\all X: P(X)", " ⊢ ((∃Xyz: P(Xyz)) ∧ (∀X: P(X)))"),
                ("!/ex X: (P(X) <-> !P(X))", " ⊢ ¬(∃X: ((P(X) → ¬P(X)) ∧ (¬P(X) → P(X))))"),
                ("!(/ex X: (P(X) <-> !P(X)))", " ⊢ ¬(∃X: ((P(X) → ¬P(X)) ∧ (¬P(X) → P(X))))"),
                ("/ex Xyz: P(Xyz) & /all X: P(X)", " ⊢ ((∃Xyz: P(Xyz)) ∧ (∀X: P(X)))"),

                ("|- P(c)", " ⊢ P(c)"),
                ("|- \\all X: P(X)", " ⊢ (∀X: P(X))"),
                ("|- \\all X:P(X)", " ⊢ (∀X: P(X))"),
                ("|- \\all X:           P(X)", " ⊢ (∀X: P(X))"),
                ("|- !(/ex X: (P(X) <-> !P(X)))", " ⊢ ¬(∃X: ((P(X) → ¬P(X)) ∧ (¬P(X) → P(X))))"),
                ("|- /ex Xyz: P(Xyz) & /all X: P(X)", " ⊢ ((∃Xyz: P(Xyz)) ∧ (∀X: P(X)))"),

                ("P(c) |-", "P(c) ⊢ "),
                ("\\all X: P(X)  |-", "(∀X: P(X)) ⊢ "),
                ("\\all X:P(X) |-", "(∀X: P(X)) ⊢ "),
                ("\\all X:           P(X)    |-", "(∀X: P(X)) ⊢ "),
                ("!(/ex X: (P(X) <-> !P(X)))  |-     ", "¬(∃X: ((P(X) → ¬P(X)) ∧ (¬P(X) → P(X)))) ⊢ "),
                ("/ex Xyz: P(Xyz) & /all X: P(X) |-   ", "((∃Xyz: P(Xyz)) ∧ (∀X: P(X))) ⊢ "),

                ("\\ex Xyz: P(Xyz) & \\all X: P(X), P(c) |- /ex Xyz: P(Xyz) & /all X: P(X), \\all X: \\all Y: \\all Z: R(m(X, m(Y, Z)), m(m(X,Y), Z))", "((∃Xyz: P(Xyz)) ∧ (∀X: P(X))), P(c) ⊢ ((∃Xyz: P(Xyz)) ∧ (∀X: P(X))), (∀X: (∀Y: (∀Z: R(m(X, m(Y, Z)), m(m(X, Y), Z)))))")
            ];

            session(|| {
                for (f, e) in valid {
                    let (l, r) = parse_fo(f).expect(e);
                    let n = SequentNode::<FOSeqMove>::new(None, l, r, None);
                    assert_eq!(e, n.to_string());
                }
            })
        }
    }
}
