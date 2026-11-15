use super::*;
use crate::kernel::VerificationSession;

fn name(name: &str) -> SpecExpression {
    SpecExpression::ProgramExpression(ProgramExpression::Variable(name.into()))
}
fn word(value: u64) -> SpecExpression {
    SpecExpression::Value(ProgramValue::UInt64(MachineTerm::uint64_constant(value)))
}
fn add(left: SpecExpression, right: SpecExpression) -> SpecExpression {
    SpecExpression::Add(Box::new(left), Box::new(right))
}
fn bind(name: &str, value: SpecExpression, body: SpecExpression) -> SpecExpression {
    SpecExpression::Let {
        name: name.into(),
        value: Box::new(value),
        body: Box::new(body),
    }
}
fn evaluate(scope: SpecScope<'_>, expression: &SpecExpression) -> SpecExpressionPath {
    let mut execution = ExecutionBudget::new();
    let mut paths = evaluate_spec_expression_paths_with_algebraic_bindings_in(
        scope,
        expression,
        &PureFactContext::new(),
        &mut SpecEvaluation::logical(&mut execution),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    paths.pop().unwrap()
}

#[test]
fn shared_let_values_keep_identity_shadowing_and_state_scope() {
    let _session = VerificationSession::enter();
    let state = ExecutionState::new().with_local(
        "x",
        ProgramValue::UInt64(MachineTerm::Variable(Variable(992400))),
    );
    let old = ExecutionState::new()
        .with_local("v", ProgramValue::UInt64(MachineTerm::uint64_constant(99)));
    let scope = SpecScope::unbound(&state, Some(&old));
    let value = add(name("x"), word(1));
    let expected = evaluate(scope, &value);
    let exports = KernelTermExport::machine_export_count();
    assert_eq!(
        evaluate(scope, &bind("v", value.clone(), name("v"))),
        expected
    );
    // `old` keeps the existing state-local name interpretation, even when
    // the current evaluation shadows that name with a retained value.
    assert_eq!(
        evaluate(
            scope,
            &bind(
                "v",
                value.clone(),
                SpecExpression::LoopEntryState(Box::new(name("v")))
            )
        )
        .value,
        word_value(99),
    );
    let shadowed = bind(
        "v",
        value.clone(),
        add(bind("v", word(7), name("v")), name("v")),
    );
    assert_eq!(
        evaluate(scope, &shadowed),
        evaluate(scope, &add(word(7), value))
    );
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    assert!(state.locals.binding("v").is_none());
}

#[test]
fn unused_shared_binding_keeps_its_shift_domain() {
    let _session = VerificationSession::enter();
    let state = ExecutionState::new().with_local(
        "x",
        ProgramValue::UInt64(MachineTerm::Variable(Variable(992401))),
    );
    let scope = SpecScope::unbound(&state, None);
    for count in [word(3), word(64), name("x")] {
        let value = SpecExpression::ShiftLeft(Box::new(name("x")), Box::new(count));
        let evaluated = evaluate(scope, &value);
        let exports = KernelTermExport::machine_export_count();
        let unused = evaluate(scope, &bind("ignored", value, word(0)));
        assert_eq!(unused.obligations, evaluated.obligations);
        assert_eq!(unused.value, word_value(0));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}

fn word_value(value: u64) -> SpecValue {
    ProgramValue::UInt64(MachineTerm::uint64_constant(value)).into()
}

#[test]
fn native_expression_reads_only_selected_shared_bindings() {
    let _session = VerificationSession::enter();
    let state = ExecutionState::new().with_local(
        "x",
        ProgramValue::UInt64(MachineTerm::Variable(Variable(992402))),
    );
    let scope = SpecScope::unbound(&state, None);
    let body = SpecExpression::ProgramExpression(ProgramExpression::Add(
        Box::new(ProgramExpression::Variable("v".into())),
        Box::new(ProgramExpression::Value(ProgramValue::UInt64(
            MachineTerm::uint64_constant(2),
        ))),
    ));
    let actual = evaluate(scope, &bind("v", add(name("x"), word(1)), body));
    let expected = evaluate(scope, &add(add(name("x"), word(1)), word(2)));
    assert_eq!(actual.value.observe(), expected.value.observe());
}

#[test]
fn native_fold_binders_shadow_shared_let_bindings() {
    let _session = VerificationSession::enter();
    let state =
        ExecutionState::new().with_local("x", int32(MachineTerm::Variable(Variable(992403))));
    let fold = SpecExpression::RangeFold {
        start: Box::new(SpecExpression::Value(int32(0))),
        end: Box::new(SpecExpression::Value(int32(2))),
        initial: Box::new(SpecExpression::Value(int32(0))),
        accumulator: "v".into(),
        item: "i".into(),
        body: Box::new(add(name("v"), SpecExpression::Value(int32(1)))),
    };
    let value = add(name("x"), SpecExpression::Value(int32(1)));
    let result = evaluate(SpecScope::unbound(&state, None), &bind("v", value, fold));
    assert_eq!(result.value.into_native(), int32(2));
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/binding_tests.rs");
}
