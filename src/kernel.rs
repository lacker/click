use std::collections::{HashMap, HashSet};

pub type Symbol = u64;
pub type Context = HashMap<Symbol, Prop>;

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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Prop {
    Equal(Term, Term),
    Implies(Box<Prop>, Box<Prop>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Proof {
    Assume(Symbol),
    Refl(Term),
    Symm(Box<Proof>),
    Trans(Box<Proof>, Box<Proof>),
    Beta {
        lambda: Lambda,
        argument: Term,
    },
    ImpliesIntro {
        assumption: Symbol,
        premise: Prop,
        proof: Box<Proof>,
    },
    ImpliesElim {
        implication: Box<Proof>,
        premise: Box<Proof>,
    },
}

pub fn check(proof: &Proof, prop: &Prop) -> bool {
    check_in_context(proof, prop, &Context::new())
}

pub fn check_in_context(proof: &Proof, prop: &Prop, context: &Context) -> bool {
    proven_prop(proof, context).as_ref() == Some(prop)
}

fn proven_prop(proof: &Proof, context: &Context) -> Option<Prop> {
    match proof {
        Proof::Assume(symbol) => context.get(symbol).cloned(),
        Proof::Refl(term) => Some(Prop::Equal(term.clone(), term.clone())),
        Proof::Symm(proof) => match proven_prop(proof, context)? {
            Prop::Equal(left, right) => Some(Prop::Equal(right, left)),
            Prop::Implies(_, _) => None,
        },
        Proof::Trans(first, second) => {
            match (proven_prop(first, context)?, proven_prop(second, context)?) {
                (Prop::Equal(left, middle), Prop::Equal(second_middle, right))
                    if middle == second_middle =>
                {
                    Some(Prop::Equal(left, right))
                }
                _ => None,
            }
        }
        Proof::Beta { lambda, argument } => {
            let applied = Term::Apply {
                function: Box::new(Term::Lambda(lambda.clone())),
                argument: Box::new(argument.clone()),
            };
            let reduced = substitute(lambda.body.as_ref(), lambda.parameter, argument);
            Some(Prop::Equal(applied, reduced))
        }
        Proof::ImpliesIntro {
            assumption,
            premise,
            proof,
        } => {
            let mut context = context.clone();
            context.insert(*assumption, premise.clone());
            let conclusion = proven_prop(proof, &context)?;
            Some(Prop::Implies(
                Box::new(premise.clone()),
                Box::new(conclusion),
            ))
        }
        Proof::ImpliesElim {
            implication,
            premise,
        } => {
            let premise = proven_prop(premise, context)?;
            match proven_prop(implication, context)? {
                Prop::Implies(expected_premise, conclusion)
                    if expected_premise.as_ref() == &premise =>
                {
                    Some(*conclusion)
                }
                _ => None,
            }
        }
    }
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

    fn equal(left: Term, right: Term) -> Prop {
        Prop::Equal(left, right)
    }

    fn implies(premise: Prop, conclusion: Prop) -> Prop {
        Prop::Implies(Box::new(premise), Box::new(conclusion))
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

    #[test]
    fn refl_proves_term_equal_to_itself() {
        let term = Term::Quote(1);

        assert!(check(
            &Proof::Refl(term.clone()),
            &Prop::Equal(term.clone(), term)
        ));
    }

    #[test]
    fn symm_flips_equality() {
        let proof = Proof::Symm(Box::new(Proof::Beta {
            lambda: Lambda {
                parameter: 1,
                body: Box::new(Term::Var(1)),
            },
            argument: Term::Quote(2),
        }));

        assert!(check(
            &proof,
            &Prop::Equal(
                Term::Quote(2),
                apply(lambda(1, Term::Var(1)), Term::Quote(2))
            )
        ));
    }

    #[test]
    fn trans_chains_matching_equalities() {
        let lambda = Lambda {
            parameter: 1,
            body: Box::new(Term::Var(1)),
        };
        let argument = Term::Quote(2);
        let applied = apply(Term::Lambda(lambda.clone()), argument.clone());
        let proof = Proof::Trans(
            Box::new(Proof::Beta {
                lambda,
                argument: argument.clone(),
            }),
            Box::new(Proof::Refl(argument.clone())),
        );

        assert!(check(&proof, &Prop::Equal(applied, argument)));
    }

    #[test]
    fn trans_rejects_mismatched_middle_terms() {
        let proof = Proof::Trans(
            Box::new(Proof::Refl(Term::Quote(1))),
            Box::new(Proof::Refl(Term::Quote(2))),
        );

        assert!(!check(&proof, &Prop::Equal(Term::Quote(1), Term::Quote(2))));
    }

    #[test]
    fn beta_proves_application_equal_to_substituted_body() {
        let lambda = Lambda {
            parameter: 1,
            body: Box::new(Term::Var(1)),
        };
        let argument = Term::Quote(2);

        assert!(check(
            &Proof::Beta {
                lambda: lambda.clone(),
                argument: argument.clone()
            },
            &Prop::Equal(apply(Term::Lambda(lambda), argument), Term::Quote(2))
        ));
    }

    #[test]
    fn assume_uses_context() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let mut context = Context::new();
        context.insert(7, prop.clone());

        assert!(check_in_context(&Proof::Assume(7), &prop, &context));
        assert!(!check(&Proof::Assume(7), &prop));
    }

    #[test]
    fn implies_intro_proves_assumption_implies_itself() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let proof = Proof::ImpliesIntro {
            assumption: 7,
            premise: prop.clone(),
            proof: Box::new(Proof::Assume(7)),
        };

        assert!(check(&proof, &implies(prop.clone(), prop)));
    }

    #[test]
    fn implies_elim_applies_implication() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let proof = Proof::ImpliesElim {
            implication: Box::new(Proof::ImpliesIntro {
                assumption: 7,
                premise: prop.clone(),
                proof: Box::new(Proof::Assume(7)),
            }),
            premise: Box::new(Proof::Refl(Term::Quote(1))),
        };

        assert!(check(&proof, &prop));
    }

    #[test]
    fn implies_elim_rejects_mismatched_premise() {
        let prop = equal(Term::Quote(1), Term::Quote(1));
        let other = equal(Term::Quote(2), Term::Quote(2));
        let proof = Proof::ImpliesElim {
            implication: Box::new(Proof::ImpliesIntro {
                assumption: 7,
                premise: prop.clone(),
                proof: Box::new(Proof::Assume(7)),
            }),
            premise: Box::new(Proof::Refl(Term::Quote(2))),
        };

        assert!(!check(&proof, &prop));
        assert!(!check(&proof, &other));
    }
}
