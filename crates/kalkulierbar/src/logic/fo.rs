use std::fmt;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum FOTerm<'l> {
    QuantifiedVar(&'l str),
    Const(&'l str),
    Function(&'l str, Vec<FOTerm<'l>>),
}

impl<'l> fmt::Display for FOTerm<'l> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FOTerm::QuantifiedVar(name) => write!(f, "{}", name),
            FOTerm::Const(c) => write!(f, "{}", c),
            FOTerm::Function(name, args) => {
                let mut arg_str = String::new();

                for (i, a) in args.iter().enumerate() {
                    if i > 0 {
                        arg_str.push_str(", ");
                    }
                    arg_str.push_str(&a.to_string());
                }

                write!(f, "{}({})", name, arg_str)
            }
        }
    }
}
