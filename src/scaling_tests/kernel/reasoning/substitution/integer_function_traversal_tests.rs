// Scaling tests of `src/kernel/reasoning/substitution.rs` (module `integer_function_traversal_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn shared_integer_application_substitution_scales_with_dag_size() {
    let from = Variable(831);
    let mut samples = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut term: SharedIntegerTerm =
            IntegerTerm::from_machine(MachineIntegerType::Int32, MachineTerm::Variable(from))
                .unwrap()
                .into();
        for _ in 0..depth {
            term = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "pair".into(),
                vec![
                    PureFunctionArgument::Integer(term.clone()),
                    PureFunctionArgument::Integer(term),
                ],
            ))
            .into();
        }
        let (changed, work) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_bitvector_variable_in_integer(
                &term,
                from,
                &MachineTerm::Variable(Variable(832)),
            )
        });
        assert_ne!(&changed, term.as_ref());
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "application substitution expanded the DAG: {samples:?}"
        );
    }
}

#[test]
fn public_integer_substitution_keeps_array_ref_states_opaque() {
    let source = Variable(840);
    let pointer = ProgramValue::Pointer(PointerValue::new(
        Pointer {
            block: PointerBlock::Symbolic(Variable(841)),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramType::VoidPointer,
    ));
    let make_memory = |count: u64| {
        let mut memory = Memory::new().with_block("array", 8);
        for index in 0..count {
            memory = memory.with_block(PointerBlock::Heap(index + 1), 8);
        }
        memory
    };
    let make = |memory: Memory| {
        Proposition::Equal(
            Term::Integer(IntegerTerm::PureFunctionApplication(
                SharedPureApplication::intern(
                    "observe_array".into(),
                    vec![
                        PureFunctionArgument::Integer(IntegerTerm::var(source).into()),
                        PureFunctionArgument::ArrayRef {
                            memory,
                            pointer: pointer.clone(),
                            element_type: ProgramType::UInt8,
                        },
                    ],
                ),
            )),
            Term::Integer(IntegerTerm::constant_i64(0)),
        )
    };
    let retained_state = |proposition: Proposition| {
        let Proposition::Equal(Term::Integer(value), _) = proposition else {
            panic!("expected Integer equality")
        };
        let IntegerTerm::PureFunctionApplication(application) = value else {
            panic!("expected pure Integer application")
        };
        let [
            PureFunctionArgument::Integer(integer),
            PureFunctionArgument::ArrayRef { memory, .. },
        ] = application.arguments()
        else {
            panic!("expected Integer and ArrayRef arguments")
        };
        assert!(matches!(integer.as_ref(), IntegerTerm::Constant(_)));
        memory.clone()
    };
    // Construct the selected term before measuring its substitution. Pin
    // a constant ceiling across state sizes rather than exact equality
    // between two totals: fixed interning/bookkeeping costs can differ,
    // but traversing even the 256-block state would exceed this bound.
    for count in [0, 16, 256, 4096] {
        let memory = make_memory(count);
        let input = make(memory.clone());
        let replacement = IntegerTerm::constant_i64(7);
        let (changed, work) = crate::instrumentation::measure_deterministic_work(|| {
            substitute_integer_variable_in_pure_proposition(&input, source, &replacement)
                .expect("state substitution should be supported")
        });
        assert!(std::sync::Arc::ptr_eq(
            &retained_state(changed).blocks,
            &memory.blocks
        ));
        assert!(work > 0 && work <= 128, "{count} unrelated blocks: {work}");
    }
}
