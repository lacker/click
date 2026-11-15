use super::*;

#[test]
fn machine_call_roots_preserve_types_arguments_and_native_roundtrips() {
    let _session = crate::kernel::VerificationSession::enter();
    let input = KernelTerm::variable(KernelType::Program(ProgramType::UInt32), Variable(995800));
    let native = SharedPureApplication::intern(
        "f".into(),
        vec![PureFunctionArgument::Value(ProgramValue::UInt32(
            MachineTerm::Variable(Variable(995800)),
        ))],
    );
    let retained = SharedPureApplication::intern(
        "f".into(),
        vec![PureFunctionArgument::SharedMachine(
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::UInt32, input.clone())
                .unwrap(),
        )],
    );
    let mut roots = Vec::new();
    for format in [
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
    ] {
        let exports = KernelTermExport::machine_export_count();
        let root = KernelTermImport::default().machine_call(format, &native);
        assert_eq!(
            root,
            KernelTermImport::default().machine_call(format, &retained)
        );
        assert_eq!(root.ty(), &KernelType::Program(format.program_type()));
        assert_eq!(root.children(), &[input.clone()]);
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert_eq!(
            KernelTermExport::machine(&root).unwrap(),
            MachineTerm::ClickFunctionApplication {
                name: "f".into(),
                arguments: native.arguments().to_vec()
            }
        );
        assert!(root.is_shared_machine_operand());
        roots.push(root);
    }
    for (i, a) in roots.iter().enumerate() {
        for b in &roots[i + 1..] {
            assert_ne!(a, b);
        }
    }
    let other = SharedPureApplication::intern("g".into(), native.arguments().to_vec());
    assert_ne!(
        roots[4],
        KernelTermImport::default().machine_call(MachineIntegerType::Int32, &other)
    );
}

#[test]
fn machine_call_roots_preserve_opaque_producer_payloads() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = PointerValue::new(Pointer::symbolic(Variable(995801)), ProgramType::VoidPointer);
    let application = SharedPureApplication::intern(
        "pointer_arg".into(),
        vec![PureFunctionArgument::Value(ProgramValue::Pointer(
            pointer.clone(),
        ))],
    );
    let format = MachineIntegerType::Int32;
    let root = KernelTermImport::default().machine_call(format, &application);
    assert_eq!(
        root,
        KernelTermImport::default().machine_call(format, &application)
    );
    let class = crate::kernel::effective_type::CAccessClass::Scalar(
        crate::kernel::effective_type::CScalarClass::Long,
    );
    let second = SharedPureApplication::intern(
        application.name().into(),
        vec![PureFunctionArgument::Value(ProgramValue::Pointer(
            pointer
                .clone()
                .with_declared_object_class(Some(class.clone())),
        ))],
    );
    assert_eq!(application, second, "semantic identity");
    assert_ne!(
        root,
        KernelTermImport::default().machine_call(format, &second),
        "distinct exact producer payloads"
    );
    let second_root = KernelTermImport::default().machine_call(format, &second);
    for (call, producer) in [(&root, &application), (&second_root, &second)] {
        assert!(std::ptr::eq(
            call.machine_conversion_leaf().unwrap(),
            producer.native_call(),
        ));
    }
    for (call, expected) in [(&root, None), (&second_root, Some(class))] {
        let MachineTerm::ClickFunctionApplication { arguments, .. } =
            KernelTermExport::machine(call).unwrap()
        else {
            panic!()
        };
        let PureFunctionArgument::Value(ProgramValue::Pointer(pointer)) = &arguments[0] else {
            panic!()
        };
        assert_eq!(pointer.object_class(), expected);
    }
    drop(application);
    let MachineTerm::ClickFunctionApplication { arguments, .. } =
        KernelTermExport::machine(&root).unwrap()
    else {
        panic!()
    };
    assert_eq!(
        arguments,
        vec![PureFunctionArgument::Value(ProgramValue::Pointer(pointer))]
    );
}

#[test]
fn machine_call_argument_order_and_read_states_remain_distinct() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(995802));
    let before = crate::kernel::intern_memory(Memory::new());
    let after = crate::kernel::intern_memory(
        Memory::new().store(pointer.clone(), ProgramValue::Int32(7u32.into())),
    );
    let calls = [before, after].map(|memory| {
        SharedPureApplication::intern(
            "read_arg".into(),
            vec![PureFunctionArgument::Value(ProgramValue::Int32(
                MachineTerm::MemoryLoad(memory, Box::new(pointer.clone()), LoadKind::Int32),
            ))],
        )
    });
    let roots = calls
        .map(|call| KernelTermImport::default().machine_call(MachineIntegerType::Int32, &call));
    assert_ne!(roots[0], roots[1]);
    let args = [1u32, 2].map(|x| PureFunctionArgument::Value(ProgramValue::Int32(x.into())));
    let a = SharedPureApplication::intern("ordered".into(), args.to_vec());
    let b = SharedPureApplication::intern("ordered".into(), args.into_iter().rev().collect());
    assert_ne!(
        KernelTermImport::default().machine_call(MachineIntegerType::Int32, &a),
        KernelTermImport::default().machine_call(MachineIntegerType::Int32, &b)
    );
}

mod scaling_tests {
    include!("../../../scaling_tests/kernel/primitives/kernel_term_machine_calls.rs");
}

#[test]
fn common_call_numeric_identity_matches_native_without_changing_payloads() {
    let _session = crate::kernel::VerificationSession::enter();
    for format in [
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
    ] {
        let application = SharedPureApplication::intern(
            "numeric_call".into(),
            vec![PureFunctionArgument::Value(ProgramValue::UInt32(
                MachineTerm::Variable(Variable(995820)),
            ))],
        );
        let root = KernelTermImport::default().machine_call(format, &application);
        let native = MachineTerm::ClickFunctionApplication {
            name: application.name().into(),
            arguments: application.arguments().to_vec(),
        };
        let exports = KernelTermExport::machine_export_count();
        assert_eq!(
            SharedMachineIntegerTerm::observe_shared(format, root.clone()).unwrap(),
            SharedMachineIntegerTerm::intern(format, native.clone())
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(matches!(root.node(), KernelTermNode::Call { .. }));
        assert_eq!(KernelTermExport::machine(&root).unwrap(), native);
    }
}

#[test]
fn native_call_import_before_shared_production_keeps_argument_handles() {
    for warm in [false, true] {
        let _session = crate::kernel::VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let argument = crate::kernel::binary_node!(
            Int32,
            Add,
            Box::new(MachineTerm::Variable(Variable(995942))),
            Box::new(MachineTerm::constant(1))
        );
        let application = SharedPureApplication::intern(
            "native_then_shared".into(),
            vec![PureFunctionArgument::Value(ProgramValue::Int32(argument))],
        );
        let imported = KernelTermImport::default().machine_call(format, &application);
        if warm {
            imported.machine_conversion_leaf().unwrap();
        }
        let child = imported.children()[0].clone();
        let retained = SharedPureApplication::intern(
            application.name().into(),
            vec![PureFunctionArgument::SharedMachine(
                SharedMachineIntegerTerm::from_shared(format, child.clone()).unwrap(),
            )],
        );
        let exports = KernelTermExport::machine_export_count();
        let produced = KernelTermImport::default().machine_call(format, &retained);
        assert_eq!(imported, produced);
        let MachineTerm::ClickFunctionApplication { arguments, .. } =
            produced.machine_conversion_leaf().unwrap()
        else {
            panic!()
        };
        let [PureFunctionArgument::SharedMachine(argument)] = arguments.as_slice() else {
            panic!("an earlier native input must not materialize a retained prefix");
        };
        assert_eq!(argument.shared_operand(), Some(&child));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
}
