use super::*;
use crate::kernel::VerificationSession;
use std::hash::{Hash, Hasher};

fn hash(value: &impl Hash) -> u64 {
    let mut state = std::collections::hash_map::DefaultHasher::new();
    value.hash(&mut state);
    state.finish()
}

fn retained(value: &ProgramValue) -> StoredExecutionValue {
    let root = KernelTermImport::default().argument(&PureFunctionArgument::Value(value.clone()));
    ExecutionValue::Shared(root).into()
}

fn memory_matrix(values: &[ProgramValue]) {
    let native: Vec<_> = values
        .iter()
        .cloned()
        .map(StoredMemoryValue::from)
        .collect();
    let shared: Vec<_> = values
        .iter()
        .map(|value| {
            let root = match value {
                ProgramValue::Parameter(value) => KernelTermImport::default().algebraic(value),
                ProgramValue::Pointer(value) => {
                    KernelTerm::shared_pointer_value(SharedPointer::import_produced(value))
                }
                _ => KernelTermImport::default()
                    .argument(&PureFunctionArgument::Value(value.clone())),
            };
            StoredMemoryValue::from(ExecutionValue::Shared(root))
        })
        .collect();
    for i in 0..values.len() {
        assert_eq!(hash(&native[i]), hash(&shared[i]));
        for j in 0..values.len() {
            let order = values[i].cmp(&values[j]);
            for left in [&native[i], &shared[i]] {
                for right in [&native[j], &shared[j]] {
                    assert_eq!(left.cmp(right), order, "memory {i}/{j}");
                    assert_eq!(left == right, order.is_eq());
                    if left == right {
                        assert_eq!(hash(left), hash(right));
                    }
                }
            }
            assert_eq!(shared[i] == values[j], order.is_eq());
            assert_eq!(values[j] == shared[i], order.is_eq());
        }
    }
}

#[test]
fn nonnumeric_storage_keys_preserve_native_pairwise_order_and_hash_classes() {
    let _session = VerificationSession::enter();
    let mut values = vec![ProgramValue::Void];
    for word in [
        MachineTerm::ThreadHandle(crate::kernel::primitives::ThreadHandleId(998696)),
        MachineTerm::Constant {
            format: MachineIntegerType::UInt8,
            bits: 2,
        },
        MachineTerm::Variable(Variable(998601)),
        MachineTerm::bool_cast(
            MachineIntegerType::UInt8,
            ConditionTerm::Variable(Variable(998602)),
        ),
    ] {
        values.push(ProgramValue::Bool(word));
    }
    for bits in [0, 0x80000000, 0x7fc00001, 0x7fc00002] {
        values.push(ProgramValue::Float32(MachineTerm::uint32_constant(bits)));
    }
    for bits in [0, 0x8000000000000000, 0x7ff8000000000001] {
        values.push(ProgramValue::Float64(MachineTerm::uint64_constant(bits)));
    }
    values.push(ProgramValue::Pointer(Pointer::new(
        Address::symbolic(Variable(998603)),
        ProgramType::Int32Pointer,
    )));
    for left in &values {
        for right in &values {
            let expected = left.cmp(right);
            for a in [StoredExecutionValue::from(left.clone()), retained(left)] {
                for b in [StoredExecutionValue::from(right.clone()), retained(right)] {
                    assert_eq!(a.cmp(&b), expected, "{left:?} vs {right:?}");
                    assert_eq!(a == b, left == right);
                    if a == b {
                        assert_eq!(hash(&a), hash(&b));
                    }
                }
            }
            let a = StoredMemoryValue::from(left.clone());
            let b = StoredMemoryValue::from(right.clone());
            assert_eq!(a.cmp(&b), expected);
            let shared = StoredMemoryValue::from(retained(left).into_value());
            assert_eq!(
                hash(&a),
                hash(&shared),
                "equal memory carriers hash equally"
            );
            assert_eq!(a == b, left == right);
            if a == b {
                assert_eq!(hash(&a), hash(&b));
            }
        }
    }
    memory_matrix(&values);
}

#[test]
fn float_storage_preserves_exact_call_argument_carrier_distinctions() {
    let _session = VerificationSession::enter();
    let word = MachineTerm::Variable(Variable(998610));
    let arguments = [
        PureFunctionArgument::Value(ProgramValue::UInt32(word.clone())),
        PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt32,
            word,
        )),
    ];
    let values = arguments.map(|argument| {
        ProgramValue::Float32(MachineTerm::ClickFunctionApplication {
            name: "storage_contract".into(),
            arguments: vec![argument],
        })
    });
    assert_ne!(values[0], values[1]);
    for a in &values {
        for b in &values {
            let left = retained(a);
            let right = retained(b);
            assert_eq!(left == right, a == b);
            assert_eq!(left.cmp(&right), a.cmp(b));
            assert_eq!(left.same_native_value(&right), a == b);
        }
    }
}

#[test]
fn boolean_connective_keys_keep_native_condition_identity_and_order() {
    let _session = VerificationSession::enter();
    let a = ConditionTerm::Variable(Variable(998670));
    let b = ConditionTerm::Variable(Variable(998671));
    let cases = [
        ConditionTerm::Constant(false),
        a.clone(),
        ConditionTerm::BoolEqual(Box::new(a.clone()), Box::new(b.clone())),
        ConditionTerm::BoolIf {
            condition: Box::new(a.clone()),
            then_condition: Box::new(b.clone()),
            else_condition: Box::new(a.clone()),
        },
        ConditionTerm::BoolApplication(SharedPureApplication::intern("key_bool".into(), vec![])),
    ];
    let roots = cases
        .iter()
        .map(|term| KernelTermImport::default().condition(term))
        .collect::<Vec<_>>();
    let native = roots
        .iter()
        .map(|root| ExecutionValue::Shared(root.clone()).into_native())
        .collect::<Vec<_>>();
    for (i, a) in roots.iter().enumerate() {
        for (j, b) in roots.iter().enumerate() {
            let left = StoredExecutionValue::from(ExecutionValue::Shared(a.clone()));
            let right = StoredExecutionValue::from(ExecutionValue::Shared(b.clone()));
            assert_eq!(left.cmp(&right), native[i].cmp(&native[j]));
            assert_eq!(left == right, native[i] == native[j]);
            let legacy = StoredExecutionValue::from(native[i].clone());
            assert_eq!(left, legacy);
            assert_eq!(hash(&left), hash(&legacy));
        }
    }
    memory_matrix(&native);
}

#[test]
fn deep_boolean_key_construction_and_drop_use_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(|| {
            let _session = VerificationSession::enter();
            let atom = KernelTerm::variable(KernelType::Bool, Variable(998675));
            let other = KernelTerm::variable(KernelType::Bool, Variable(998676));
            let mut root = atom.clone();
            for _ in 0..4096 {
                root = KernelTerm::boolean_if_raw([atom.clone(), root, other.clone()]);
            }
            let value = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
            assert!(!root.has_cached_native_argument());
            let _ = hash(&value);
            assert!(!root.has_cached_native_argument());
            drop(root);
            drop(value);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn float_operation_keys_preserve_native_order_and_payloads() {
    let _session = VerificationSession::enter();
    let mut roots = Vec::new();
    for format in [KernelFloatType::Float32, KernelFloatType::Float64] {
        let atom =
            KernelTerm::variable(KernelType::Program(format.program_type()), Variable(998690));
        roots.push(atom.clone());
        roots.push(KernelTerm::float_negate(format, atom.clone()).unwrap());
        roots.push(
            KernelTerm::float_binary(
                format,
                FloatBinaryOperator::Add,
                [atom.clone(), atom.clone()],
            )
            .unwrap(),
        );
        roots.push(KernelTerm::float_call(
            format,
            "outer".into(),
            vec![(atom.clone(), None)],
        ));
        let integer =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(998691));
        roots.push(KernelTerm::float_convert(format, ProgramType::Int32, integer).unwrap());
        // A newly added opaque native word keeps its identity and native
        // ordering even when carried by an unsupported legacy float input.
        roots.push(KernelTermImport::default().float(
            format,
            &MachineTerm::ThreadHandle(crate::kernel::primitives::ThreadHandleId(998696)),
        ));
        let native = MachineTerm::If {
            condition: Box::new(ConditionTerm::Variable(Variable(998692))),
            then_term: Box::new(MachineTerm::constant(1)),
            else_term: Box::new(MachineTerm::constant(2)),
        };
        roots.push(KernelTermImport::default().float(format, &native));
    }
    let values = roots
        .iter()
        .map(|root| ExecutionValue::Shared(root.clone()).into_native())
        .collect::<Vec<_>>();
    for (i, a) in roots.iter().enumerate() {
        let a = StoredExecutionValue::from(ExecutionValue::Shared(a.clone()));
        let native = StoredExecutionValue::from(values[i].clone());
        assert_eq!(a, native);
        assert_eq!(hash(&a), hash(&native));
        for (j, b) in roots.iter().enumerate() {
            let b = StoredExecutionValue::from(ExecutionValue::Shared(b.clone()));
            assert_eq!(a.cmp(&b), values[i].cmp(&values[j]));
            assert_eq!(a == b, values[i] == values[j]);
        }
    }
    memory_matrix(&values);
}

#[test]
fn deep_float_key_construction_and_drop_use_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 << 10)
        .spawn(|| {
            let _session = VerificationSession::enter();
            let mut root =
                KernelTerm::variable(KernelType::Program(ProgramType::Float32), Variable(998695));
            for _ in 0..4096 {
                root = KernelTerm::float_negate(KernelFloatType::Float32, root).unwrap();
            }
            let stored = StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
            let exports = KernelTermExport::float_export_count();
            let _ = hash(&stored);
            assert_eq!(KernelTermExport::float_export_count(), exports);
            assert!(!root.has_cached_native_argument());
            drop(root);
            drop(stored);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn algebraic_storage_keys_preserve_native_order_and_carrier_classes() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = KernelMatch::test_scrutinee(vec![]);
    let ty = variable.algebraic_type.clone();
    let make = |node| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node,
    };
    let mut values = vec![variable.clone()];
    for name in ["A", "B"] {
        for fields in [
            vec![],
            vec![AlgebraicValue::Algebraic(variable.clone())],
            vec![AlgebraicValue::Program(ProgramValue::Parameter(Box::new(
                variable.clone(),
            )))],
            vec![AlgebraicValue::Integer(IntegerTerm::Variable(Variable(
                998733,
            )))],
            vec![AlgebraicValue::Program(ProgramValue::Bool(
                MachineTerm::Variable(Variable(998734)),
            ))],
        ] {
            values.push(make(AlgebraicTermNode::Constructor {
                variant: name.into(),
                fields,
            }));
        }
    }
    let word = MachineTerm::Variable(Variable(998735));
    for arg in [
        PureFunctionArgument::Value(ProgramValue::Int32(word.clone())),
        PureFunctionArgument::SharedMachine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            word,
        )),
        PureFunctionArgument::Algebraic(variable.clone()),
        PureFunctionArgument::Value(ProgramValue::Parameter(Box::new(variable.clone()))),
    ] {
        values.push(make(AlgebraicTermNode::PureFunctionApplication {
            name: "key_call".into(),
            arguments: vec![arg],
        }));
    }
    let pointer = Pointer::new(
        Address::symbolic(Variable(998737)),
        ProgramType::Int32Pointer,
    );
    for pointer in [pointer.clone(), pointer.with_pointee_constant(true)] {
        values.push(make(AlgebraicTermNode::Constructor {
            variant: "Pointer".into(),
            fields: vec![AlgebraicValue::Program(ProgramValue::Pointer(pointer))],
        }));
    }
    for address in [998738, 998739] {
        values.push(make(AlgebraicTermNode::MemoryLoad {
            point: crate::kernel::ProgramPoint::at(&intern_memory(SymbolicMemory::new())),
            pointer: Box::new(Address::symbolic(Variable(address))),
        }));
    }
    let condition = ConditionTerm::Variable(Variable(998736));
    let branches = values[..3].to_vec();
    for branch in branches {
        values.push(make(AlgebraicTermNode::If {
            condition: Box::new(condition.clone()),
            then_term: Box::new(branch.clone()),
            else_term: Box::new(variable.clone()),
        }));
    }
    for binding in [
        AlgebraicValue::Algebraic(variable.clone()),
        AlgebraicValue::Program(ProgramValue::Parameter(Box::new(variable.clone()))),
    ] {
        values.push(make(AlgebraicTermNode::Match {
            scrutinee: Box::new(variable.clone()),
            arms: vec![AlgebraicResultMatchArm {
                variant: "Arm".into(),
                bindings: vec![binding],
                body: variable.clone(),
                binding_names: BindingNames::written(&["ignored".into()]),
            }],
        }));
    }
    let natives: Vec<_> = values
        .iter()
        .map(|value| ProgramValue::Parameter(Box::new(value.clone())))
        .collect();
    let shared: Vec<_> = values
        .iter()
        .map(|value| {
            StoredExecutionValue::from(ExecutionValue::Shared(
                KernelTermImport::default().algebraic(value),
            ))
        })
        .collect();
    let native: Vec<_> = natives
        .iter()
        .cloned()
        .map(StoredExecutionValue::from)
        .collect();
    let exports = KernelTermExport::algebraic_export_count();
    for i in 0..values.len() {
        for j in 0..values.len() {
            let expected = natives[i].cmp(&natives[j]);
            assert_eq!(shared[i].cmp(&shared[j]), expected, "shared {i}/{j}");
            assert_eq!(native[i].cmp(&shared[j]), expected, "mixed {i}/{j}");
            assert_eq!(native[i] == shared[j], expected.is_eq());
            if expected.is_eq() {
                assert_eq!(hash(&native[i]), hash(&shared[j]));
            }
        }
        assert!(!shared[i].shared().unwrap().has_cached_native_argument());
    }
    assert_eq!(KernelTermExport::algebraic_export_count(), exports);
    memory_matrix(&natives);
}

#[test]
fn deep_algebraic_storage_keys_use_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            let _session = crate::kernel::VerificationSession::enter();
            let native = KernelMatch::test_scrutinee(vec![]);
            let mut root = KernelTermImport::default().algebraic(&native);
            for _ in 0..4096 {
                root = KernelConstructor {
                    algebraic_type: native.algebraic_type.clone(),
                    variant: "Deep".into(),
                    fields: vec![root],
                }
                .into_term();
            }
            let stored = StoredExecutionValue::from(ExecutionValue::Shared(root));
            let _ = hash(&stored);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pointer_storage_keys_preserve_the_complete_native_identity_tuple() {
    let _session = VerificationSession::enter();
    let pointer = Pointer::new(
        Address::symbolic(Variable(998750)),
        ProgramType::Int32Pointer,
    );
    let other = Address::symbolic(Variable(998751));
    let mut values = vec![
        pointer.clone(),
        pointer.clone().with_pointee_constant(true),
        pointer.clone().with_pointee_volatile(true),
        pointer.clone().with_type(ProgramType::VoidPointer),
        pointer
            .clone()
            .with_provenance(std::sync::Arc::new(other.clone())),
        pointer
            .clone()
            .with_bounds_owner(Some(std::sync::Arc::new(other.clone()))),
        pointer.clone().with_root_bounds(),
        pointer
            .clone()
            .with_root_bounds()
            .with_bounds_owner(Some(std::sync::Arc::new(other.clone()))),
    ];
    for width in [0, 1, 8] {
        values.push(pointer.clone().with_bounds(Some(SubobjectBounds {
            start: other.clone(),
            width: MachineTerm::constant(width),
        })));
    }
    for offset in [
        AddressOffset::Constant(-1),
        AddressOffset::Constant(0),
        AddressOffset::Variable(Variable(998752)),
        AddressOffset::Add(
            Box::new(AddressOffset::Variable(Variable(998752))),
            Box::new(AddressOffset::Constant(1)),
        ),
        AddressOffset::scaled_int32_node(MachineTerm::Variable(Variable(998753)), 4),
        AddressOffset::scaled_int64_node(MachineTerm::Variable(Variable(998754)), 8, false),
        AddressOffset::scaled_int64_node(MachineTerm::Variable(Variable(998754)), 8, true),
    ] {
        values.push(Pointer::new(
            Address {
                base: other.base.clone(),
                offset,
            },
            ProgramType::Int32Pointer,
        ));
    }
    let natives: Vec<_> = values.iter().cloned().map(ProgramValue::Pointer).collect();
    let shared: Vec<_> = natives
        .iter()
        .cloned()
        .map(|value| StoredExecutionValue::from(ExecutionValue::retain_formed_pointer(value)))
        .collect();
    let stored: Vec<_> = natives
        .iter()
        .cloned()
        .map(StoredExecutionValue::from)
        .collect();
    let exports = KernelTermExport::machine_export_count();
    for i in 0..values.len() {
        for j in 0..values.len() {
            let expected = natives[i].cmp(&natives[j]);
            assert_eq!(shared[i].cmp(&shared[j]), expected, "shared {i}/{j}");
            assert_eq!(stored[i].cmp(&shared[j]), expected, "mixed {i}/{j}");
            assert_eq!(stored[i] == shared[j], expected.is_eq());
            if expected.is_eq() {
                assert_eq!(hash(&stored[i]), hash(&shared[j]));
            }
        }
        assert!(!shared[i].shared().unwrap().has_cached_native_argument());
    }
    // The selected scalar subobject widths use their explicit compatibility
    // reader; no enclosing pointer descriptor is produced.
    assert!(KernelTermExport::machine_export_count() - exports <= 3);
    memory_matrix(&natives);
}

#[test]
fn deep_pointer_storage_keys_use_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            use crate::kernel::{KernelAddressOffset, SharedAddress};
            let _session = VerificationSession::enter();
            let value = SharedPointer::import_produced(&Pointer::new(
                Address::symbolic(Variable(998755)),
                ProgramType::Int32Pointer,
            ));
            let mut payload = value.node().clone();
            let atom = KernelAddressOffset::Variable(Variable(998756))
                .into_shared()
                .unwrap();
            let mut offset = atom.clone();
            for _ in 0..4096 {
                offset = KernelAddressOffset::Add([offset, atom.clone()])
                    .into_shared()
                    .unwrap();
            }
            payload.address = SharedAddress::new(payload.address.node().base.clone(), offset);
            payload.provenance = payload.address.clone();
            let stored = StoredExecutionValue::from(ExecutionValue::Shared(
                KernelTerm::shared_pointer_value(SharedPointer::new(payload)),
            ));
            let _ = hash(&stored);
            assert!(!stored.shared().unwrap().has_cached_native_argument());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn memory_numeric_keys_keep_native_syntax_instead_of_local_observations() {
    let _session = VerificationSession::enter();
    let word = MachineTerm::Variable(Variable(998795));
    let call = |arg| {
        ProgramValue::UInt32(MachineTerm::ClickFunctionApplication {
            name: "memory_carrier_key".into(),
            arguments: vec![arg],
        })
    };
    let a = call(PureFunctionArgument::Value(ProgramValue::UInt32(
        word.clone(),
    )));
    let b = call(PureFunctionArgument::SharedMachine(
        SharedMachineIntegerTerm::intern(MachineIntegerType::UInt32, word),
    ));
    assert_ne!(a, b);
    assert_eq!(
        StoredExecutionValue::from(a.clone()),
        StoredExecutionValue::from(b.clone())
    );
    let cells = [
        StoredMemoryValue::from(a.clone()),
        StoredMemoryValue::from(b.clone()),
    ];
    assert_ne!(cells[0], cells[1]);
    assert_eq!(cells[0].cmp(&cells[1]), a.cmp(&b));
    assert_eq!(hash(&cells[0]), hash(&a));
    assert_eq!(hash(&cells[1]), hash(&b));
}

#[test]
fn memory_hash_collisions_still_compare_values() {
    #[derive(Default)]
    struct Collision;
    impl Hasher for Collision {
        fn finish(&self) -> u64 {
            0
        }
        fn write(&mut self, _: &[u8]) {}
    }
    let _session = VerificationSession::enter();
    let values = [
        0,
        0x8000000000000000,
        0x7ff8000000000001,
        0x7ff8000000000002,
    ]
    .map(|bits| ProgramValue::Float64(MachineTerm::uint64_constant(bits)));
    let mut map = std::collections::HashMap::<
        StoredMemoryValue,
        usize,
        std::hash::BuildHasherDefault<Collision>,
    >::default();
    for (i, value) in values.iter().enumerate() {
        map.insert(StoredMemoryValue::from(value.clone()), i);
    }
    assert_eq!(map.len(), values.len());
    for (i, value) in values.iter().enumerate() {
        let root =
            KernelTermImport::default().argument(&PureFunctionArgument::Value(value.clone()));
        assert_eq!(
            map.get(&StoredMemoryValue::from(ExecutionValue::Shared(root))),
            Some(&i)
        );
    }
}

#[test]
fn retained_unsigned_cell_keys_preserve_exact_native_syntax() {
    let _session = crate::kernel::VerificationSession::enter();
    let format = MachineIntegerType::UInt32;
    let mut root = KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(998810));
    let three = KernelTermImport::default().machine(format, &MachineTerm::uint32_constant(3));
    let mut prior: Option<(StoredMemoryValue, ProgramValue)> = None;
    for depth in 1..=48 {
        root = KernelTerm::machine_binary_shared(
            format,
            MachineBinaryOp::Multiply,
            [root, three.clone()],
        );
        let shared = StoredMemoryValue::retained_word(&root).unwrap();
        let exports = KernelTermExport::machine_export_count();
        let _ = hash(&shared);
        assert_eq!(
            KernelTermExport::machine_export_count(),
            exports,
            "depth {depth}"
        );
        let native = ProgramValue::UInt32(KernelTermExport::machine(&root).unwrap());
        let stored = StoredMemoryValue::from(native.clone());
        assert_eq!(shared, stored);
        assert_eq!(hash(&shared), hash(&stored));
        if let Some((prior_shared, prior_native)) = &prior {
            assert_ne!(&shared, prior_shared);
            assert_eq!(shared.cmp(prior_shared), native.cmp(prior_native));
        }
        prior = Some((shared, native));
    }
}
