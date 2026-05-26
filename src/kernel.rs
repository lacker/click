use std::collections::HashSet;

pub type Symbol = u64;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lambda {
    pub parameter: Symbol,
    pub body: Box<Term>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Term {
    Apply {
        function: Box<Term>,
        argument: Box<Term>,
    },
    Lambda(Lambda),
    Var(Symbol),
    Quote(Symbol),
}

pub fn substitute(term: &Term, variable: Symbol, replacement: &Term) -> Term {
    match term {
        Term::Apply { function, argument } => Term::Apply {
            function: Box::new(substitute(function, variable, replacement)),
            argument: Box::new(substitute(argument, variable, replacement)),
        },
        Term::Lambda(lambda) => {
            if lambda.parameter == variable {
                return term.clone();
            }

            if free_symbols(replacement).contains(&lambda.parameter) {
                let fresh = fresh_symbol(term, replacement, variable);
                let body = rename_bound_var(lambda.body.as_ref(), lambda.parameter, fresh);
                return Term::Lambda(Lambda {
                    parameter: fresh,
                    body: Box::new(substitute(&body, variable, replacement)),
                });
            }

            Term::Lambda(Lambda {
                parameter: lambda.parameter,
                body: Box::new(substitute(lambda.body.as_ref(), variable, replacement)),
            })
        }
        Term::Var(symbol) if *symbol == variable => replacement.clone(),
        Term::Var(_) | Term::Quote(_) => term.clone(),
    }
}

pub fn step(term: &Term) -> Option<Term> {
    match term {
        Term::Apply { function, argument } => match function.as_ref() {
            Term::Lambda(lambda) => {
                Some(substitute(lambda.body.as_ref(), lambda.parameter, argument))
            }
            _ => step(function)
                .map(|function| Term::Apply {
                    function: Box::new(function),
                    argument: argument.clone(),
                })
                .or_else(|| {
                    step(argument).map(|argument| Term::Apply {
                        function: function.clone(),
                        argument: Box::new(argument),
                    })
                }),
        },
        Term::Lambda(lambda) => step(lambda.body.as_ref()).map(|body| {
            Term::Lambda(Lambda {
                parameter: lambda.parameter,
                body: Box::new(body),
            })
        }),
        Term::Var(_) | Term::Quote(_) => None,
    }
}

pub fn normal_form(term: &Term) -> Term {
    let mut term = term.clone();
    while let Some(next) = step(&term) {
        term = next;
    }
    term
}

pub fn free_symbols(term: &Term) -> HashSet<Symbol> {
    let mut symbols = HashSet::new();
    add_free_symbols(term, &mut symbols);
    symbols
}

fn add_free_symbols(term: &Term, symbols: &mut HashSet<Symbol>) {
    match term {
        Term::Apply { function, argument } => {
            add_free_symbols(function, symbols);
            add_free_symbols(argument, symbols);
        }
        Term::Lambda(lambda) => {
            add_free_symbols(lambda.body.as_ref(), symbols);
            symbols.remove(&lambda.parameter);
        }
        Term::Var(symbol) => {
            symbols.insert(*symbol);
        }
        Term::Quote(_) => {}
    }
}

fn rename_bound_var(term: &Term, old: Symbol, new: Symbol) -> Term {
    match term {
        Term::Apply { function, argument } => Term::Apply {
            function: Box::new(rename_bound_var(function, old, new)),
            argument: Box::new(rename_bound_var(argument, old, new)),
        },
        Term::Lambda(lambda) if lambda.parameter == old => Term::Lambda(lambda.clone()),
        Term::Lambda(lambda) => Term::Lambda(Lambda {
            parameter: lambda.parameter,
            body: Box::new(rename_bound_var(lambda.body.as_ref(), old, new)),
        }),
        Term::Var(symbol) if *symbol == old => Term::Var(new),
        Term::Var(_) | Term::Quote(_) => term.clone(),
    }
}

fn fresh_symbol(term: &Term, replacement: &Term, variable: Symbol) -> Symbol {
    let mut symbols = HashSet::new();
    add_all_symbols(term, &mut symbols);
    add_all_symbols(replacement, &mut symbols);
    symbols.insert(variable);

    let mut symbol = 0;
    while symbols.contains(&symbol) {
        symbol += 1;
    }
    symbol
}

fn add_all_symbols(term: &Term, symbols: &mut HashSet<Symbol>) {
    match term {
        Term::Apply { function, argument } => {
            add_all_symbols(function, symbols);
            add_all_symbols(argument, symbols);
        }
        Term::Lambda(lambda) => {
            symbols.insert(lambda.parameter);
            add_all_symbols(lambda.body.as_ref(), symbols);
        }
        Term::Var(symbol) | Term::Quote(symbol) => {
            symbols.insert(*symbol);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lambda(parameter: Symbol, body: Term) -> Term {
        Term::Lambda(Lambda {
            parameter,
            body: Box::new(body),
        })
    }

    fn apply(function: Term, argument: Term) -> Term {
        Term::Apply {
            function: Box::new(function),
            argument: Box::new(argument),
        }
    }

    #[test]
    fn step_beta_reduces_identity_lambda() {
        let term = apply(lambda(1, Term::Var(1)), Term::Quote(2));

        assert_eq!(step(&term), Some(Term::Quote(2)));
    }

    #[test]
    fn normal_form_reduces_repeatedly() {
        let term = apply(
            lambda(1, apply(lambda(2, Term::Var(2)), Term::Var(1))),
            Term::Quote(3),
        );

        assert_eq!(normal_form(&term), Term::Quote(3));
    }

    #[test]
    fn substitution_respects_shadowing() {
        let term = lambda(1, Term::Var(1));

        assert_eq!(substitute(&term, 1, &Term::Quote(2)), term);
    }

    #[test]
    fn substitution_avoids_variable_capture() {
        let term = lambda(2, Term::Var(1));

        assert_eq!(substitute(&term, 1, &Term::Var(2)), lambda(0, Term::Var(2)));
    }

    #[test]
    fn free_symbols_ignores_bound_symbols_and_quotes() {
        assert_eq!(
            free_symbols(&lambda(1, apply(Term::Var(1), Term::Quote(2)))),
            HashSet::new()
        );
    }
}
