use super::{calculus::*, theory::Bindings};

pub fn step(term: &Term) -> Step {
    step_in_bindings(term, &Bindings::new())
}

pub(super) fn step_in_bindings(term: &Term, bindings: &Bindings) -> Step {
    match term {
        Term::Apply { function, argument } => step_apply(function, argument, bindings),
        Term::Lambda(_) => Step::Normal,
        Term::Nil => Step::Normal,
        Term::Cons { head, tail } => step_cons(head, tail, bindings),
        Term::Head(term) => step_head(term, bindings),
        Term::Tail(term) => step_tail(term, bindings),
        Term::ListCase(list_case) => step_list_case(list_case, bindings),
        Term::Const(name) => match bindings.term(*name) {
            Some(term) => Step::Reduced(term.clone()),
            None => Step::Normal,
        },
        Term::Error(_) | Term::Diverge => Step::Normal,
        Term::Var(_) | Term::Quote(_) => Step::Normal,
    }
}

fn step_apply(function: &Term, argument: &Term, bindings: &Bindings) -> Step {
    match function {
        Term::Lambda(lambda) => step_lambda_application(lambda, argument, bindings),
        Term::Error(_) | Term::Diverge => Step::Reduced(function.clone()),
        _ => match step_in_bindings(function, bindings) {
            Step::Reduced(function) => Step::Reduced(Term::Apply {
                function: Box::new(function),
                argument: Box::new(argument.clone()),
            }),
            Step::Normal if is_known_non_callable(function) => {
                Step::Reduced(runtime_error(function.clone()))
            }
            Step::Normal => step_neutral_application(function, argument, bindings),
        },
    }
}

fn step_lambda_application(lambda: &Lambda, argument: &Term, bindings: &Bindings) -> Step {
    match step_in_bindings(argument, bindings) {
        Step::Reduced(argument) => Step::Reduced(Term::Apply {
            function: Box::new(Term::Lambda(lambda.clone())),
            argument: Box::new(argument),
        }),
        Step::Normal if is_effect(argument) => Step::Reduced(argument.clone()),
        Step::Normal => Step::Reduced(substitute(lambda.body.as_ref(), lambda.parameter, argument)),
    }
}

fn step_neutral_application(function: &Term, argument: &Term, bindings: &Bindings) -> Step {
    match step_in_bindings(argument, bindings) {
        Step::Reduced(argument) => Step::Reduced(Term::Apply {
            function: Box::new(function.clone()),
            argument: Box::new(argument),
        }),
        Step::Normal if is_effect(argument) => Step::Reduced(argument.clone()),
        Step::Normal => Step::Normal,
    }
}

pub(super) fn argument_is_ready_for_beta(argument: &Term, bindings: &Bindings) -> bool {
    match step_in_bindings(argument, bindings) {
        Step::Reduced(_) => false,
        Step::Normal => !is_effect(argument),
    }
}

fn is_effect(term: &Term) -> bool {
    term.as_effect().is_some()
}

pub fn term_is_value(term: &Term) -> bool {
    term.as_value().is_some()
}

fn is_known_non_callable(term: &Term) -> bool {
    matches!(term, Term::Quote(_) | Term::Nil | Term::Cons { .. })
}

fn runtime_error(payload: Term) -> Term {
    Term::Error(Box::new(payload))
}

fn step_cons(head: &Term, tail: &Term, bindings: &Bindings) -> Step {
    match step_in_bindings(head, bindings) {
        Step::Reduced(head) => Step::Reduced(Term::Cons {
            head: Box::new(head),
            tail: Box::new(tail.clone()),
        }),
        Step::Normal if is_effect(head) => Step::Reduced(head.clone()),
        Step::Normal => match step_in_bindings(tail, bindings) {
            Step::Reduced(tail) => Step::Reduced(Term::Cons {
                head: Box::new(head.clone()),
                tail: Box::new(tail),
            }),
            Step::Normal if is_effect(tail) => Step::Reduced(tail.clone()),
            Step::Normal => Step::Normal,
        },
    }
}

fn step_head(term: &Term, bindings: &Bindings) -> Step {
    match step_in_bindings(term, bindings) {
        Step::Reduced(term) => Step::Reduced(Term::Head(Box::new(term))),
        Step::Normal => match term {
            Term::Cons { head, .. } => Step::Reduced(head.as_ref().clone()),
            Term::Error(_) | Term::Diverge => Step::Reduced(term.clone()),
            Term::Const(_)
            | Term::Var(_)
            | Term::Apply { .. }
            | Term::Head(_)
            | Term::Tail(_)
            | Term::ListCase(_) => Step::Normal,
            Term::Nil | Term::Quote(_) | Term::Lambda(_) => {
                Step::Reduced(runtime_error(term.clone()))
            }
        },
    }
}

fn step_tail(term: &Term, bindings: &Bindings) -> Step {
    match step_in_bindings(term, bindings) {
        Step::Reduced(term) => Step::Reduced(Term::Tail(Box::new(term))),
        Step::Normal => match term {
            Term::Cons { tail, .. } => Step::Reduced(tail.as_ref().clone()),
            Term::Error(_) | Term::Diverge => Step::Reduced(term.clone()),
            Term::Const(_)
            | Term::Var(_)
            | Term::Apply { .. }
            | Term::Head(_)
            | Term::Tail(_)
            | Term::ListCase(_) => Step::Normal,
            Term::Nil | Term::Quote(_) | Term::Lambda(_) => {
                Step::Reduced(runtime_error(term.clone()))
            }
        },
    }
}

fn step_list_case(list_case: &ListCase, bindings: &Bindings) -> Step {
    match step_in_bindings(list_case.list.as_ref(), bindings) {
        Step::Reduced(list) => Step::Reduced(Term::ListCase(ListCase {
            list: Box::new(list),
            nil: list_case.nil.clone(),
            cons: list_case.cons,
            cons_case: list_case.cons_case.clone(),
        })),
        Step::Normal => match list_case.list.as_ref() {
            Term::Nil => Step::Reduced(list_case.nil.as_ref().clone()),
            Term::Cons { .. } => Step::Reduced(substitute(
                list_case.cons_case.as_ref(),
                list_case.cons,
                list_case.list.as_ref(),
            )),
            Term::Error(_) | Term::Diverge => Step::Reduced(list_case.list.as_ref().clone()),
            Term::Const(_)
            | Term::Var(_)
            | Term::Apply { .. }
            | Term::Head(_)
            | Term::Tail(_)
            | Term::ListCase(_) => Step::Normal,
            Term::Quote(_) | Term::Lambda(_) => {
                Step::Reduced(runtime_error(list_case.list.as_ref().clone()))
            }
        },
    }
}

pub fn normal_form(term: &Term) -> Term {
    normal_form_in_bindings(term, &Bindings::new())
}

pub(super) fn normal_form_in_bindings(term: &Term, bindings: &Bindings) -> Term {
    let mut term = term.clone();
    loop {
        match step_in_bindings(&term, bindings) {
            Step::Reduced(next) => term = next,
            Step::Normal => return term,
        }
    }
}
