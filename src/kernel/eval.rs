use super::{calculus::*, theory::Bindings};

pub fn step(computation: &Computation) -> Step {
    step_in_bindings(computation, &Bindings::new())
}

pub(super) fn step_in_bindings(computation: &Computation, bindings: &Bindings) -> Step {
    match computation {
        Computation::Apply { function, argument } => step_apply(function, argument, bindings),
        Computation::Lambda(_) => Step::Normal,
        Computation::Nil => Step::Normal,
        Computation::Bv32(_) => Step::Normal,
        Computation::Cons { head, tail } => step_cons(head, tail, bindings),
        Computation::Head(computation) => step_head(computation, bindings),
        Computation::Tail(computation) => step_tail(computation, bindings),
        Computation::ListCase(list_case) => step_list_case(list_case, bindings),
        Computation::If {
            condition,
            then_branch,
            else_branch,
        } => step_if(condition, then_branch, else_branch, bindings),
        Computation::SymbolEq { left, right } => step_symbol_eq(left, right, bindings),
        Computation::Bv32Eq { left, right } => {
            step_bv32_binary(Bv32BinaryOp::Eq, left, right, bindings)
        }
        Computation::Bv32Add { left, right } => {
            step_bv32_binary(Bv32BinaryOp::Add, left, right, bindings)
        }
        Computation::Bv32Slt { left, right } => {
            step_bv32_binary(Bv32BinaryOp::Slt, left, right, bindings)
        }
        Computation::Bv32SignedAddOverflows { left, right } => {
            step_bv32_binary(Bv32BinaryOp::SignedAddOverflows, left, right, bindings)
        }
        Computation::ValueKind(computation) => step_value_kind(computation, bindings),
        Computation::Ref(name) => match bindings.computation(*name) {
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

fn is_effect(computation: &Computation) -> bool {
    computation.as_effect().is_some()
}

pub fn computation_is_value(computation: &Computation) -> bool {
    computation.as_value().is_some()
}

fn is_known_non_callable(computation: &Computation) -> bool {
    matches!(
        computation,
        Computation::Quote(_) | Computation::Nil | Computation::Cons { .. } | Computation::Bv32(_)
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
            Step::Normal if is_known_non_list(tail) => Step::Reduced(runtime_error()),
            Step::Normal => Step::Normal,
        },
    }
}

fn is_known_non_list(computation: &Computation) -> bool {
    matches!(
        computation,
        Computation::Quote(_) | Computation::Lambda(_) | Computation::Bv32(_)
    )
}

fn step_head(computation: &Computation, bindings: &Bindings) -> Step {
    match step_in_bindings(computation, bindings) {
        Step::Reduced(computation) => Step::Reduced(Computation::Head(Box::new(computation))),
        Step::Normal => match computation {
            Computation::Cons { head, .. } => Step::Reduced(head.as_ref().clone()),
            Computation::Error(_) | Computation::Diverge => Step::Reduced(computation.clone()),
            Computation::Ref(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_)
            | Computation::SymbolEq { .. }
            | Computation::Bv32Eq { .. }
            | Computation::Bv32Add { .. }
            | Computation::Bv32Slt { .. }
            | Computation::Bv32SignedAddOverflows { .. }
            | Computation::ValueKind(_)
            | Computation::If { .. } => Step::Normal,
            Computation::Nil
            | Computation::Quote(_)
            | Computation::Lambda(_)
            | Computation::Bv32(_) => Step::Reduced(runtime_error()),
        },
    }
}

fn step_tail(computation: &Computation, bindings: &Bindings) -> Step {
    match step_in_bindings(computation, bindings) {
        Step::Reduced(computation) => Step::Reduced(Computation::Tail(Box::new(computation))),
        Step::Normal => match computation {
            Computation::Cons { tail, .. } => Step::Reduced(tail.as_ref().clone()),
            Computation::Error(_) | Computation::Diverge => Step::Reduced(computation.clone()),
            Computation::Ref(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_)
            | Computation::SymbolEq { .. }
            | Computation::Bv32Eq { .. }
            | Computation::Bv32Add { .. }
            | Computation::Bv32Slt { .. }
            | Computation::Bv32SignedAddOverflows { .. }
            | Computation::ValueKind(_)
            | Computation::If { .. } => Step::Normal,
            Computation::Nil
            | Computation::Quote(_)
            | Computation::Lambda(_)
            | Computation::Bv32(_) => Step::Reduced(runtime_error()),
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
            Computation::Ref(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_)
            | Computation::SymbolEq { .. }
            | Computation::Bv32Eq { .. }
            | Computation::Bv32Add { .. }
            | Computation::Bv32Slt { .. }
            | Computation::Bv32SignedAddOverflows { .. }
            | Computation::ValueKind(_)
            | Computation::If { .. } => Step::Normal,
            Computation::Quote(_) | Computation::Lambda(_) | Computation::Bv32(_) => {
                Step::Reduced(runtime_error())
            }
        },
    }
}

fn step_if(
    condition: &Computation,
    then_branch: &Computation,
    else_branch: &Computation,
    bindings: &Bindings,
) -> Step {
    match step_in_bindings(condition, bindings) {
        Step::Reduced(condition) => Step::Reduced(Computation::If {
            condition: Box::new(condition),
            then_branch: Box::new(then_branch.clone()),
            else_branch: Box::new(else_branch.clone()),
        }),
        Step::Normal => match condition {
            Computation::Quote(TRUE_SYMBOL) => Step::Reduced(then_branch.clone()),
            Computation::Quote(FALSE_SYMBOL) => Step::Reduced(else_branch.clone()),
            Computation::Error(_) | Computation::Diverge => Step::Reduced(condition.clone()),
            Computation::Ref(_)
            | Computation::Var(_)
            | Computation::Apply { .. }
            | Computation::Head(_)
            | Computation::Tail(_)
            | Computation::ListCase(_)
            | Computation::SymbolEq { .. }
            | Computation::Bv32Eq { .. }
            | Computation::Bv32Add { .. }
            | Computation::Bv32Slt { .. }
            | Computation::Bv32SignedAddOverflows { .. }
            | Computation::ValueKind(_)
            | Computation::If { .. } => Step::Normal,
            Computation::Nil
            | Computation::Cons { .. }
            | Computation::Bv32(_)
            | Computation::Lambda(_)
            | Computation::Quote(_) => Step::Reduced(runtime_error()),
        },
    }
}

fn step_symbol_eq(left: &Computation, right: &Computation, bindings: &Bindings) -> Step {
    match step_in_bindings(left, bindings) {
        Step::Reduced(left) => Step::Reduced(Computation::SymbolEq {
            left: Box::new(left),
            right: Box::new(right.clone()),
        }),
        Step::Normal if is_effect(left) => Step::Reduced(left.clone()),
        Step::Normal if left.as_value().is_none() => Step::Normal,
        Step::Normal => match step_in_bindings(right, bindings) {
            Step::Reduced(right) => Step::Reduced(Computation::SymbolEq {
                left: Box::new(left.clone()),
                right: Box::new(right),
            }),
            Step::Normal if is_effect(right) => Step::Reduced(right.clone()),
            Step::Normal if right.as_value().is_none() => Step::Normal,
            Step::Normal => Step::Reduced(symbol_eq_result(left, right)),
        },
    }
}

fn symbol_eq_result(left: &Computation, right: &Computation) -> Computation {
    match (left, right) {
        (Computation::Quote(left), Computation::Quote(right)) if left == right => {
            Computation::Quote(TRUE_SYMBOL)
        }
        _ => Computation::Quote(FALSE_SYMBOL),
    }
}

#[derive(Clone, Copy)]
enum Bv32BinaryOp {
    Eq,
    Add,
    Slt,
    SignedAddOverflows,
}

fn step_bv32_binary(
    op: Bv32BinaryOp,
    left: &Computation,
    right: &Computation,
    bindings: &Bindings,
) -> Step {
    match step_in_bindings(left, bindings) {
        Step::Reduced(left) => Step::Reduced(rebuild_bv32_binary(op, left, right.clone())),
        Step::Normal if is_effect(left) => Step::Reduced(left.clone()),
        Step::Normal if left.as_value().is_none() => Step::Normal,
        Step::Normal => match left {
            Computation::Bv32(left_value) => match step_in_bindings(right, bindings) {
                Step::Reduced(right) => Step::Reduced(rebuild_bv32_binary(op, left.clone(), right)),
                Step::Normal if is_effect(right) => Step::Reduced(right.clone()),
                Step::Normal if right.as_value().is_none() => Step::Normal,
                Step::Normal => match right {
                    Computation::Bv32(right_value) => {
                        Step::Reduced(apply_bv32_binary(op, *left_value, *right_value))
                    }
                    _ => Step::Reduced(runtime_error()),
                },
            },
            _ => Step::Reduced(runtime_error()),
        },
    }
}

fn rebuild_bv32_binary(op: Bv32BinaryOp, left: Computation, right: Computation) -> Computation {
    match op {
        Bv32BinaryOp::Eq => Computation::Bv32Eq {
            left: Box::new(left),
            right: Box::new(right),
        },
        Bv32BinaryOp::Add => Computation::Bv32Add {
            left: Box::new(left),
            right: Box::new(right),
        },
        Bv32BinaryOp::Slt => Computation::Bv32Slt {
            left: Box::new(left),
            right: Box::new(right),
        },
        Bv32BinaryOp::SignedAddOverflows => Computation::Bv32SignedAddOverflows {
            left: Box::new(left),
            right: Box::new(right),
        },
    }
}

fn apply_bv32_binary(op: Bv32BinaryOp, left: u32, right: u32) -> Computation {
    match op {
        Bv32BinaryOp::Eq => boolean_computation(left == right),
        Bv32BinaryOp::Add => Computation::Bv32(left.wrapping_add(right)),
        Bv32BinaryOp::Slt => boolean_computation((left as i32) < (right as i32)),
        Bv32BinaryOp::SignedAddOverflows => {
            boolean_computation((left as i32).overflowing_add(right as i32).1)
        }
    }
}

fn boolean_computation(value: bool) -> Computation {
    Computation::Quote(if value { TRUE_SYMBOL } else { FALSE_SYMBOL })
}

fn step_value_kind(computation: &Computation, bindings: &Bindings) -> Step {
    match step_in_bindings(computation, bindings) {
        Step::Reduced(computation) => Step::Reduced(Computation::ValueKind(Box::new(computation))),
        Step::Normal if is_effect(computation) => Step::Reduced(computation.clone()),
        Step::Normal => value_kind_result(computation).map_or(Step::Normal, Step::Reduced),
    }
}

fn value_kind_result(computation: &Computation) -> Option<Computation> {
    match computation {
        Computation::Quote(_) => Some(Computation::Quote(SYMBOL_KIND_SYMBOL)),
        Computation::Lambda(_) => Some(Computation::Quote(LAMBDA_KIND_SYMBOL)),
        Computation::Bv32(_) => Some(Computation::Quote(BV32_KIND_SYMBOL)),
        Computation::Nil => Some(Computation::Quote(LIST_KIND_SYMBOL)),
        Computation::Cons { .. } if computation.as_list_value().is_some() => {
            Some(Computation::Quote(LIST_KIND_SYMBOL))
        }
        _ => None,
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
