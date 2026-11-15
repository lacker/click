use super::*;
use crate::kernel::VerificationSession;

const FORMATS: [MachineIntegerType; 10] = [
    MachineIntegerType::Int8,
    MachineIntegerType::UInt8,
    MachineIntegerType::Int16,
    MachineIntegerType::UInt16,
    MachineIntegerType::Int32,
    MachineIntegerType::UInt32,
    MachineIntegerType::Int64,
    MachineIntegerType::UInt64,
    MachineIntegerType::Int128,
    MachineIntegerType::UInt128,
];

pub(super) fn cast_chain(
    root: &KernelTerm,
    target: ProgramType,
    count: usize,
) -> (SpecExpressionPath, usize) {
    let state = ExecutionState::new();
    let mut values = crate::persistent::PersistentMap::default();
    values.insert("x".to_string(), root.clone());
    let scope = SpecScope {
        values: Some(&values),
        ..SpecScope::unbound(&state, None)
    };
    let mut expression = SpecExpression::ProgramExpression(ProgramExpression::Variable("x".into()));
    for _ in 0..count {
        expression = SpecExpression::Cast(Box::new(expression), target);
    }
    let mut execution = ExecutionBudget::new();
    let (mut paths, work) = crate::instrumentation::measure_deterministic_work(|| {
        evaluate_spec_expression_paths_with_algebraic_bindings_in(
            scope,
            &expression,
            &PureFactContext::new(),
            &mut SpecEvaluation::logical(&mut execution),
        )
        .unwrap()
    });
    assert_eq!(paths.len(), 1);
    (paths.pop().unwrap(), work)
}

#[test]
fn identity_casts_preserve_exact_shared_roots_at_every_integer_width() {
    let _session = VerificationSession::enter();
    for format in FORMATS {
        let root =
            KernelTermImport::default().machine(format, &MachineTerm::Variable(Variable(995410)));
        for count in [1, 3] {
            let exports = KernelTermExport::machine_export_count();
            let (path, _) = cast_chain(&root, format.program_type(), count);
            assert_eq!(path.value, SpecValue::Shared(root.clone()), "{format:?}");
            assert!(path.facts.is_empty());
            assert!(path.obligations.is_empty());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
        }
    }
}

#[test]
fn identity_casts_keep_selected_read_states_distinct() {
    let _session = VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(995411));
    let before = crate::kernel::intern_memory(Memory::new());
    let after = crate::kernel::intern_memory(
        Memory::new().store(pointer.clone(), ProgramValue::Int32(7u32.into())),
    );
    let roots = [before, after].map(|memory| {
        let name = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &pointer,
            LoadKind::Int32,
            4,
        );
        crate::kernel::eval::registered_scalar_read_term(&name, MachineIntegerType::Int32).unwrap()
    });
    assert_ne!(roots[0], roots[1]);
    let exports = KernelTermExport::machine_export_count();
    for root in &roots {
        let (path, _) = cast_chain(root, ProgramType::Int32, 3);
        assert_eq!(path.value, SpecValue::Shared(root.clone()));
    }
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[test]
fn changed_type_cast_is_not_an_identity_cast() {
    let _session = VerificationSession::enter();
    let root = KernelTermImport::default().machine(
        MachineIntegerType::UInt64,
        &MachineTerm::uint64_constant(256),
    );
    let (path, _) = cast_chain(&root, ProgramType::UInt8, 1);
    assert_eq!(path.value.program_type(), ProgramType::UInt8);
    assert_ne!(path.value, SpecValue::Shared(root));
    assert_eq!(
        path.value.into_native(),
        ProgramValue::UInt8(MachineTerm::narrow_constant(MachineIntegerType::UInt8, 0))
    );
}

mod scaling_tests {
    include!("../../scaling_tests/kernel/spec/identity_cast_tests.rs");
}
