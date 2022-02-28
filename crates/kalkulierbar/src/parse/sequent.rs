use crate::logic::{transform::remove_equivs::remove_equivs, LogicNode};

use super::{fo::parse_fo_formula, parse_prop_formula, ParseErr, ParseResult};

pub fn parse_prop(formula: &str) -> ParseResult<(Vec<LogicNode>, Vec<LogicNode>)> {
    parse(formula, parse_prop_formula)
}

pub fn parse_fo(formula: &str) -> ParseResult<(Vec<LogicNode>, Vec<LogicNode>)> {
    parse(formula, parse_fo_formula)
}

pub fn parse<P>(formula: &str, p: P) -> ParseResult<(Vec<LogicNode>, Vec<LogicNode>)>
where
    P: Fn(&str) -> ParseResult<LogicNode>,
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
        let left = parse_formulas(sides[0], 0, &p)?;
        let right = parse_formulas(sides[1], sides[0].len() + 2, &p)?;
        Ok((left, right))
    } else {
        Ok((vec![], parse_formulas(sides[0], 0, &p)?))
    }
}

fn parse_formulas<P>(formulas: &str, pos: usize, p: &P) -> ParseResult<Vec<LogicNode>>
where
    P: Fn(&str) -> ParseResult<LogicNode>,
{
    let input: Vec<_> = formulas.split(',').collect();
    let len = input.len();

    input
        .iter()
        .enumerate()
        .filter_map(|(i, f)| {
            let parsed = match p(f) {
                Ok(p) => p,
                Err(ParseErr::EmptyFormula) if i != 0 && len != 1 => {
                    return Some(Err(ParseErr::EmptyFormulaAt(pos)))
                }
                _ => return None,
            };
            let n = remove_equivs(parsed);
            Some(Ok(n))
        })
        .collect()
}
