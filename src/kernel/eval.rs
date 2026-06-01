use super::{calculus::*, theory::Bindings};

pub fn step(computation: &Computation) -> Step {
    step_in_bindings(computation, &Bindings::new())
}

pub(super) fn step_in_bindings(computation: &Computation, bindings: &Bindings) -> Step {
    match computation {
        Computation::Apply { function, argument } => step_apply(function, argument, bindings),
        Computation::Lambda(_) => Step::Normal,
        Computation::Nil => Step::Normal,
        Computation::Cons { head, tail } => step_cons(head, tail, bindings),
        Computation::Head(computation) => step_head(computation, bindings),
        Computation::Tail(computation) => step_tail(computation, bindings),
        Computation::ListCase(list_case) => step_list_case(list_case, bindings),
        Computation::Const(name) => match bindings.computation(*name) {
            Some(computation) => Step::Reduced(computation.clone()),
            None => Step::Normal,
        },
        Computation::Error(_) | Computation::Diverge => Step::Normal,
        Computation::Var(_) | Computation::Quote(_) => Step::Normal,
    }
}

fn step_apply(function: &Computation, argument: &Computation, bindings: &Bindings) -> Step {
    match function {
        Computation::Lambda(lambda) => step_lambda_application(lambda, argument, bindings),
        Computation::Error(_) | Computation::Diverge => Step::Reduced(function.clone()),
        _ => match step_in_bindings(function, bindings) {
            Step::Reduced(function) => Step::Reduced(Computation::Apply {
                function: Box::new(function),
                argument: Box::new(argument.clone()),
            }),
            Step::Normal if is_known_non_callable(function) => Step::Reduced(runtime_error()),
            Step::Normal => step_neutral_application(function, argument, bindings),
        },
    }
}

fn step_lambda_application(lambda: &Lambda, argument: &Computation, bindings: &Bindings) -> Step {
    match step_in_bindings(argument, bindings) {
        Step::Reduced(argument) => Step::Reduced(Computation::Apply {
            function: Box::new(Computation::Lambda(lambda.clone())),
            argument: Box::new(argument),
        }),
        Step::Normal if is_effect(argument) => Step::Reduced(argument.clone()),
        Step::Normal => Step::Reduced(substitute(lambda.body.as_ref(), lambda.parameter, argument)),
    }
}

fn step_neutral_application(
    function: &Computation,
    argument: &Computation,
    bindings: &Bindings,
) -> Step {
    match step_in_bindings(argument, bindings) {
        Step::Reduced(argument) => Step::Reduced(Computation::Apply {
            function: Box::new(function.clone()),
            argument: Box::new(argument),
        }),
        Step::Normal if is_effect(argument) => Step::Reduced(argument.clone()),
        Step::Normal => Step::Normal,
    }
}

pub(super) fn argument_is_ready_for_beta(argument: &Computation, bindings: &Bindings) -> bool {
    match step_in_bindings(argument, bindings) {
        Step::Reduced(_) => false,
        Step::Normal => !is_effect(argument),
    }
}

fn is_effect(computation: &Computation) -> bool {
    computation.as_effect().is_some()
}

pub fn computation_is_value(computation: &Computation) -> bool {
    computation.as_value().is_some()
}

fn is_known_non_callable(computation: &Computation) -> bool {
    matches!(
        computation,
        Computation::Quote(_) | Computation::Nil | Computation::Cons { .. }
    )
}

fn runtime_error() -> Computation {
    Computation::Error(RUNTIME_ERROR)
}

fn step_cons(head: &Computation, tail: &Computation, bindings: &Bindings) -> Step {
    match step_in_bindings(head, bindings) {
        Step::Reduced(head) => Step::Reduced(Computation::Cons {
            head: Box::new(head),
            tail: Box::new(tail.clone()),
        }),
        Step::Normal if is_effect(head) => Step::Reduced(head.clone()),
        Step::Normal => match step_in_bindings(tail, bindings) {
            Step::Reduced(tail) => Step::Reduced(Computation::Cons {
                head: Box::new(head.clone()),
                tail: Box::new(tail),
            }),
            Step::Normal if is_effect(tail) => Step::Reduced(tail.clone()),
            Step::Normal => Step::Normal,
        },
    }
}

fn step_head(computation: &Computation, bindings: &Bindings) -> Step {
    match step_in_bindings(computation, bindings) {
        Step::Reduced(computation) => Step::Reduced(Computation::Head(Box::new(computation))),
        Step::Normal => match computation {
            Computation::Cons { head, .. } => Step::Reduced(head.as_ref().clone()),
            Computation::Error(_) | Computation::Diverge => Step::Reduced(computation.clone()),
            Computation::Const(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_) => Step::Normal,
            Computation::Nil | Computation::Quote(_) | Computation::Lambda(_) => {
                Step::Reduced(runtime_error())
            }
        },
    }
}

fn step_tail(computation: &Computation, bindings: &Bindings) -> Step {
    match step_in_bindings(computation, bindings) {
        Step::Reduced(computation) => Step::Reduced(Computation::Tail(Box::new(computation))),
        Step::Normal => match computation {
            Computation::Cons { tail, .. } => Step::Reduced(tail.as_ref().clone()),
            Computation::Error(_) | Computation::Diverge => Step::Reduced(computation.clone()),
            Computation::Const(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_) => Step::Normal,
            Computation::Nil | Computation::Quote(_) | Computation::Lambda(_) => {
                Step::Reduced(runtime_error())
            }
        },
    }
}

fn step_list_case(list_case: &ListCase, bindings: &Bindings) -> Step {
    match step_in_bindings(list_case.list.as_ref(), bindings) {
        Step::Reduced(list) => Step::Reduced(Computation::ListCase(ListCase {
            list: Box::new(list),
            nil: list_case.nil.clone(),
            cons: list_case.cons,
            cons_case: list_case.cons_case.clone(),
        })),
        Step::Normal => match list_case.list.as_ref() {
            Computation::Nil => Step::Reduced(list_case.nil.as_ref().clone()),
            Computation::Cons { .. } => Step::Reduced(substitute(
                list_case.cons_case.as_ref(),
                list_case.cons,
                list_case.list.as_ref(),
            )),
            Computation::Error(_) | Computation::Diverge => {
                Step::Reduced(list_case.list.as_ref().clone())
            }
            Computation::Const(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_) => Step::Normal,
            Computation::Quote(_) | Computation::Lambda(_) => Step::Reduced(runtime_error()),
        },
    }
}

pub fn normal_form(computation: &Computation) -> Computation {
    normal_form_in_bindings(computation, &Bindings::new())
}

pub fn normal_outcome(computation: &Computation) -> Option<Outcome> {
    normal_outcome_in_bindings(computation, &Bindings::new())
}

pub(super) fn normal_form_in_bindings(
    computation: &Computation,
    bindings: &Bindings,
) -> Computation {
    let mut computation = computation.clone();
    loop {
        match step_in_bindings(&computation, bindings) {
            Step::Reduced(next) => computation = next,
            Step::Normal => return computation,
        }
    }
}

pub(super) fn normal_outcome_in_bindings(
    computation: &Computation,
    bindings: &Bindings,
) -> Option<Outcome> {
    normal_form_in_bindings(computation, bindings).as_outcome()
}
