pub mod cnf;
pub mod collectors;
pub mod fo_cnf;
pub mod logic_node_manipulation;
pub mod naive_cnf;
pub mod negation_normal;
pub mod prenex_normal;
pub mod remove_equivs;
pub mod signature;
pub mod skolem;
pub mod skolem_normal;
pub mod term_manipulator;
pub mod to_basic;
pub mod transformer;
pub mod tseytin_cnf;
pub mod unique_vars;
pub mod visitor;

pub use cnf::*;
pub use naive_cnf::FormulaConversionErr;
pub use negation_normal::negation_normal_form;

#[cfg(test)]
mod tests {
    use super::{negation_normal_form, unique_vars::unique_vars};
    use crate::{logic::transform::skolem::skolemize, parse::fo::parse_fo_formula, session};

    // based on issue #46 in internal gitlab, now inaccessible
    #[test]
    fn issue46() {
        let test_strs = [
            (
                "\\all X: Q(X,X) <=> R(c)",
                "(((∃X: ¬Q(X, X)) ∨ R(c)) ∧ ((∀Xv1: Q(Xv1, Xv1)) ∨ ¬R(c)))",
            ),
            ("\\ex X: \\ex X: R(X, X)", "(∃X: (∃Xv1: R(Xv1, Xv1)))"),
        ];

        session(|| {
            for (f, e) in test_strs {
                let parsed = parse_fo_formula(f).unwrap();
                let nnf = negation_normal_form(parsed).unwrap();
                let transformed = unique_vars(nnf);
                assert_eq!(e, transformed.to_string());
            }
        })
    }

    // based on issue #48 in internal gitlab, now inaccessible
    #[test]
    fn issue48() {
        let test_strs = [(
            "\\ex X: R(X) & (R(sk1) <-> R(usk1))",
            "(R(sk2) ∧ (R(sk1) <=> R(usk1)))",
        )];
        let invalid = "\\ex X: R(X) & R(sk-1)";

        session(|| {
            for (f, e) in test_strs {
                let parsed = parse_fo_formula(f).unwrap();
                let transformed = skolemize(parsed).unwrap();
                assert_eq!(e, transformed.to_string());
            }
            assert!(parse_fo_formula(invalid).is_err());
        })
    }
}
