pub enum FOTerm {
    QuantifiedVar(String),
    Const(String),
    Function(String, Vec<FOTerm>),
}
