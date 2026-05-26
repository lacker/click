pub type Symbol = u64;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    Apply {
        function: Box<Term>,
        argument: Box<Term>,
    },
    Lambda {
        parameter: Symbol,
        body: Box<Term>,
    },
    Var(Symbol),
    Quote(Symbol),
}
