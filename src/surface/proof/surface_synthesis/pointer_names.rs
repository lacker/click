//! Complete pointer names retain payloads, independently of logical address
//! equality. The existing proof-local scope owns these selected source values.
use super::*;
use crate::kernel::SharedPointerValue;

pub(super) struct NamedValue {
    value: Value,
    name: String,
}
enum Value {
    Pointer(SharedPointerValue),
    Other(ProgramValue),
}
impl NamedValue {
    pub(super) fn new((value, name): (ProgramValue, String)) -> Self {
        let value = match value {
            ProgramValue::Pointer(pointer) => Value::Pointer(SharedPointerValue::import(&pointer)),
            value => Value::Other(value),
        };
        Self { value, name }
    }
}

/// The shared producer path needs neither an exported address nor a native
/// complete value. Scope ordering and lifetime are unchanged.
pub(super) fn shared_name(value: &SharedPointerValue) -> Option<String> {
    PROOF_LOCAL_VALUE_NAMES.with(|names| {
        names.borrow().iter().find_map(|named| match &named.value {
            Value::Pointer(held) if held.same_source_payload(value) => Some(named.name.clone()),
            _ => None,
        })
    })
}

pub(super) fn native_name(value: &ProgramValue) -> Option<String> {
    if let ProgramValue::Pointer(pointer) = value {
        return shared_name(&SharedPointerValue::import(pointer));
    }
    PROOF_LOCAL_VALUE_NAMES.with(|names| {
        names.borrow().iter().find_map(|named| match &named.value {
            Value::Other(held) if held == value => Some(named.name.clone()),
            _ => None,
        })
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{KernelTermExport, PointerValue, SubobjectExtent, VerificationSession};

    fn check_names(values: Vec<(&str, PointerValue)>) {
        let state = ExecutionState::new();
        let bindings: BTreeMap<_, _> = values
            .iter()
            .map(|(name, value)| (name.to_string(), ProgramValue::Pointer(value.clone())))
            .collect();
        let names = bindings
            .iter()
            .map(|(name, value)| (value.clone(), name.clone()))
            .collect();
        with_proof_local_value_names(names, || {
            for (name, pointer) in values {
                let retained = SharedPointerValue::import(&pointer);
                let read_root = crate::kernel::KernelTerm::retained_pointer_read(&pointer);
                let root = crate::kernel::KernelTermImport::default().argument(
                    &crate::kernel::PureFunctionArgument::Value(ProgramValue::Pointer(
                        pointer.clone(),
                    )),
                );
                let exports = KernelTermExport::machine_export_count();
                assert_eq!(shared_name(&retained).as_deref(), Some(name));
                let expression = synthesize_surface_value(
                    &ProgramValue::Pointer(pointer),
                    ParameterBinding::default(),
                    &state,
                )
                .unwrap();
                assert_eq!(
                    expression,
                    SurfaceTerm::ProgramExpression(ProgramExpression::Variable(name.into()))
                );
                assert_eq!(
                    raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new()),
                    Some(expression.clone()),
                );
                let formed_root = crate::kernel::KernelTerm::shared_pointer_value(retained.clone());
                assert_eq!(
                    raise_kernel_term(
                        &formed_root,
                        ParameterBinding::default(),
                        &state,
                        &BTreeMap::new()
                    ),
                    Some(expression.clone()),
                );
                let arithmetic_root = crate::kernel::KernelTerm::shared_pointer_arithmetic(
                    crate::kernel::MachineBinaryOp::Add,
                    1,
                    [
                        formed_root,
                        crate::kernel::KernelTerm::retained_native_machine_operand(
                            crate::kernel::MachineIntegerType::UInt64,
                            &crate::kernel::MachineTerm::uint64_constant(0),
                        ),
                    ],
                    retained.clone(),
                );
                assert_eq!(
                    raise_kernel_term(
                        &arithmetic_root,
                        ParameterBinding::default(),
                        &state,
                        &BTreeMap::new()
                    ),
                    Some(expression.clone()),
                );
                if let Some(root) = read_root {
                    assert_eq!(
                        raise_kernel_term(
                            &root,
                            ParameterBinding::default(),
                            &state,
                            &BTreeMap::new()
                        ),
                        Some(expression.clone()),
                    );
                }
                assert_eq!(KernelTermExport::machine_export_count(), exports);
                let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                    &expression,
                    BTreeMap::new(),
                    &state,
                    bindings.clone(),
                    bindings.clone(),
                    None,
                    &RecordedStates::new(),
                    SpecDefinitions::new(
                        &PredicateEnvironment::new(&[]),
                        &ClickFunctionEnvironment::new(&[]),
                    ),
                    BTreeSet::new(),
                    BTreeMap::new(),
                )
                .unwrap();
                let (value, _) = crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state, &spec, Some(&state), &PureFactContext::new(),
                ).unwrap();
                let ProgramValue::Pointer(restored) = value else {
                    panic!("pointer name")
                };
                assert!(retained.same_source_payload(&SharedPointerValue::import(&restored)));
            }
        });
    }

    #[test]
    fn numeric_pointer_observation_roots_raise_and_lower_through_existing_casts() {
        use crate::kernel::{
            KernelTermImport, MachineIntegerType, MachineTerm, PureFunctionArgument,
        };
        let _session = VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(1024950)),
            ProgramType::Int32Pointer,
        );
        let state = ExecutionState::new().with_local("p", ProgramValue::Pointer(pointer.clone()));
        let bindings = BTreeMap::from([("p".to_string(), ProgramValue::Pointer(pointer.clone()))]);
        for format in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
            let value = format.value_from_term(MachineTerm::object_pointer_address(
                pointer.pointer().clone(),
                pointer.object_class(),
            ));
            let root =
                KernelTermImport::default().argument(&PureFunctionArgument::Value(value.clone()));
            let expression =
                raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new())
                    .unwrap();
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                &expression,
                BTreeMap::new(),
                &state,
                bindings.clone(),
                bindings.clone(),
                None,
                &RecordedStates::new(),
                SpecDefinitions::new(
                    &PredicateEnvironment::new(&[]),
                    &ClickFunctionEnvironment::new(&[]),
                ),
                BTreeSet::new(),
                BTreeMap::new(),
            )
            .unwrap();
            let (restored, _) =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &spec,
                    Some(&state),
                    &PureFactContext::new(),
                )
                .unwrap();
            assert_eq!(restored, value, "{format:?}: {expression:?}");
        }
    }

    #[test]
    fn pointer_proof_names_preserve_qualifiers_instead_of_address_equality() {
        let _session = VerificationSession::enter();
        let plain = PointerValue::new(
            Pointer::symbolic(Variable(1015000)),
            ProgramType::Int32Pointer,
        );
        let qualified = plain.clone().with_pointee_constant(true);
        assert_eq!(
            plain, qualified,
            "logical equality intentionally ignores const"
        );
        check_names(vec![("a_plain", plain), ("z_const", qualified)]);
    }

    #[test]
    fn pointer_proof_names_keep_historical_extent_reads() {
        let _session = VerificationSession::enter();
        let address = crate::kernel::Memory::global_pointer("pointer-name-width");
        let before = Memory::new().with_block("pointer-name-width", 4);
        let after = before.clone().store(
            address.clone(),
            ProgramValue::Int32(MachineTerm::constant(12)),
        );
        let pointer = Pointer::symbolic(Variable(1015010));
        let make = |memory| {
            PointerValue::new(pointer.clone(), ProgramType::Int32Pointer).with_extent(Some(
                SubobjectExtent {
                    start: pointer.clone(),
                    width: MachineTerm::MemoryLoad(
                        crate::kernel::intern_memory(memory),
                        Box::new(address.clone()),
                        crate::kernel::LoadKind::Int32,
                    ),
                },
            ))
        };
        check_names(vec![("a_before", make(before)), ("z_after", make(after))]);
    }

    #[test]
    fn pointer_read_roots_raise_through_exact_complete_names() {
        let _session = VerificationSession::enter();
        let memory = Memory::new();
        let address = Pointer::symbolic(Variable(1018010));
        let seeded = memory.clone().with_seeded_cells(
            address.clone(),
            8,
            ProgramType::Int32Pointer,
            0,
            1,
            crate::kernel::intern_memory(memory),
        );
        let crate::kernel::ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) =
            seeded.load(&address)
        else {
            panic!("read result");
        };
        assert!(crate::kernel::KernelTerm::retained_pointer_read(&pointer).is_some());
        check_names(vec![
            ("read", pointer.clone()),
            ("const_read", pointer.with_pointee_constant(true)),
        ]);
    }

    #[test]
    fn pointer_proof_name_scopes_restore_exact_payload_bindings() {
        let _session = VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(1015020)),
            ProgramType::Int32Pointer,
        );
        let shared = SharedPointerValue::import(&pointer);
        let value = ProgramValue::Pointer(pointer);
        assert!(shared_name(&shared).is_none());
        with_proof_local_value_names(vec![(value.clone(), "outer".into())], || {
            assert_eq!(shared_name(&shared).as_deref(), Some("outer"));
            with_proof_local_value_names(vec![(value, "inner".into())], || {
                assert_eq!(shared_name(&shared).as_deref(), Some("inner"));
            });
            assert_eq!(shared_name(&shared).as_deref(), Some("outer"));
        });
        assert!(shared_name(&shared).is_none());
    }
}
