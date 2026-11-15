// Scaling tests of `src/kernel/proof/term_rewrite.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::binary_node;

#[test]
fn full_pointer_alias_keeps_typed_constructor_fields_in_linear_work() {
    let class = crate::kernel::effective_type::CAccessClass::Struct(
        crate::kernel::effective_type::CStructClass::opaque("node"),
    );
    let from = PointerValue::new(
        Pointer::symbolic(Variable(970_001)),
        ProgramType::Int32Pointer,
    );
    let to = PointerValue::new(
        Pointer::symbolic(Variable(970_002)),
        ProgramType::Int32Pointer,
    );
    let typed = from.clone().with_object_class(Some(class.clone()));
    let mut work = Vec::new();
    for size in [16usize, 64, 256] {
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Node".into(),
            fields: vec![
                AlgebraicValueType::ObjectPointer(ProgramType::Int32Pointer, class.clone());
                size
            ],
        }]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "TypedPointers".into(),
            arguments: vec![],
        };
        let input = Term::Algebraic(AlgebraicTerm {
            algebraic_type: AlgebraicType {
                rigid: false,
                name: "TypedPointers".into(),
                arguments: vec![],
                variants: variants.clone(),
                schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                    value_type, variants,
                )]))),
            },
            node: AlgebraicTermNode::Constructor {
                variant: "Node".into(),
                fields: vec![AlgebraicValue::Program(ProgramValue::Pointer(typed.clone())); size],
            },
        });
        let (actual, units) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_pointer_value_exact(&from, &to).term(&input)
        });
        let Term::Algebraic(actual) = actual else {
            panic!("constructor expected")
        };
        let fields = actual
            .checked_constructor_fields()
            .expect("rewriting preserves the typed constructor");
        for field in fields {
            let AlgebraicValue::Program(ProgramValue::Pointer(pointer)) = field else {
                panic!("pointer field expected")
            };
            assert_eq!(pointer.pointer(), to.pointer());
            assert_eq!(pointer.designation(), to.designation());
            assert!(pointer.supports_object_class(&class));
        }
        work.push(units);
    }
    assert!(work[0] > 0);
    assert!(
        work[1] <= work[0] * 5 && work[2] <= work[0] * 20,
        "{work:?}"
    );

    // A cast's declared class is not checked evidence to transport.
    let unchecked =
        ProgramValue::Pointer(from.clone().with_declared_object_class(Some(class.clone())));
    let ProgramValue::Pointer(actual) =
        TermRewrite::for_pointer_value_exact(&from, &to).value(&unchecked)
    else {
        panic!("pointer expected")
    };
    assert!(!actual.supports_object_class(&class));

    // Numeric equality cannot replace the original object's designation.
    let ProgramValue::Pointer(actual) =
        TermRewrite::for_pointer_exact(from.pointer(), to.pointer())
            .value(&ProgramValue::Pointer(typed.clone()))
    else {
        panic!("pointer expected")
    };
    assert_eq!(actual.designation(), typed.designation());
    assert_eq!(actual.opaque_extent(), typed.opaque_extent());
}

#[test]
fn nested_c_folds_and_adt_matches_reserve_actual_nodes_linearly() {
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Case".into(),
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32)],
        }]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "FoldMatch".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "FoldMatch".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let mut expression = IntegerTerm::constant_i64(0);
        for index in 0..depth {
            let binding = Variable(10_000 + index as u64);
            let accumulator = Variable(11_000 + index as u64);
            let item = Variable(12_000 + index as u64);
            let fold = MachineTerm::RangeFold {
                start: Box::new(MachineTerm::constant(0)),
                end: Box::new(MachineTerm::constant(2)),
                initial: Box::new(MachineTerm::constant(0)),
                accumulator,
                item,
                body: Box::new(MachineTerm::Variable(accumulator)),
            };
            let observed = IntegerTerm::PureFunctionApplication(SharedPureApplication::intern(
                "observe_fold".into(),
                vec![PureFunctionArgument::Value(ProgramValue::Int32(fold))],
            ));
            let body = IntegerTerm::Add(observed.into(), expression.into());
            expression = IntegerTerm::AlgebraicMatch {
                scrutinee: Box::new(AlgebraicTerm {
                    algebraic_type: algebraic_type.clone(),
                    node: AlgebraicTermNode::Variable(Variable(13_000 + index as u64)),
                }),
                arms: vec![AlgebraicIntegerMatchArm {
                    binding_names: Default::default(),
                    variant: "Case".into(),
                    bindings: vec![AlgebraicValue::Program(ProgramValue::Int32(
                        MachineTerm::Variable(binding),
                    ))],
                    body: body.into(),
                }],
            };
        }
        let (visits, measured) = crate::instrumentation::measure_deterministic_work(|| {
            let from = MachineTerm::Variable(Variable(90_000));
            let to = MachineTerm::constant(0);
            let mut rewrite = TermRewrite::for_bits(&from, &to);
            let _ = rewrite.term(&Term::Integer(expression.clone()));
            rewrite.visits
        });
        assert!(visits >= depth, "nested match traversal was skipped");
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "nested carrier reservation expanded superlinearly: {work:?}"
        );
    }
}

#[test]
fn registered_load_rewrite_keeps_branching_pointer_dag_compact() {
    let source = Variable(3_104_000);
    let source_term = MachineTerm::Variable(source);
    let replacement = MachineTerm::constant(9);
    let mut work = Vec::new();
    let mut last_load = None;
    for depth in [8usize, 16, 32, 64] {
        let memory =
            crate::kernel::intern_memory(Memory::new().with_block(format!("branch-{depth}"), 64));
        let block = format!("branch-{depth}");
        let mut load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &Pointer {
                block: PointerBlock::Concrete(block.clone()),
                offset: PointerOffsetTerm::scaled_int32_node(source_term.clone(), 4),
            },
            crate::kernel::LoadKind::Int32,
            4,
        );
        for _ in 0..depth {
            load = crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &Pointer {
                    block: PointerBlock::Concrete(block.clone()),
                    offset: PointerOffsetTerm::Add(
                        Box::new(PointerOffsetTerm::scaled_int32_node(
                            MachineTerm::Variable(load),
                            4,
                        )),
                        Box::new(PointerOffsetTerm::scaled_int32_node(
                            MachineTerm::Variable(load),
                            4,
                        )),
                    ),
                },
                crate::kernel::LoadKind::Int32,
                4,
            );
        }
        let body = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            MachineTerm::Variable(load),
        ));
        let (output, measured) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_bits_checked(&source_term, &replacement);
            rewrite.enable_registered_load_resolution();
            let output = rewrite.term(&Term::Integer(body.clone()));
            assert!(!rewrite.unsupported_integer_scope);
            assert!(!rewrite.integer_work_exhausted);
            output
        });
        let Term::Integer(IntegerTerm::Machine(machine)) = output else {
            panic!("registered load carrier changed shape")
        };
        assert!(!machine.has_boxed_operand());
        let (retained_state, pointer, kind) =
            machine.operand_view().read().expect("structural read");
        assert_eq!(kind, crate::kernel::LoadKind::Int32);
        assert_ne!(
            pointer,
            &crate::kernel::eval::registered_load_for_variable(&load)
                .unwrap()
                .1
        );
        assert_eq!(retained_state, &memory);
        assert!(pointer.offset.native_scaled_values_for_output().iter().all(
            |value| matches!(value, MachineTerm::MemoryLoad(retained_state, _, _) if retained_state == &memory)
        ));
        last_load = Some(load);
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 64,
            "registered load DAG rewrite grew superlinearly: {work:?}"
        );
    }

    let load = last_load.expect("branching load was constructed");
    let mut cycle_rewrite = TermRewrite::for_bits_checked(&source_term, &replacement);
    cycle_rewrite.enable_registered_load_resolution();
    cycle_rewrite.registered_load_pointer_active.insert(load);
    let _ = cycle_rewrite.bits(&MachineTerm::Variable(load));
    assert_eq!(
        cycle_rewrite.refusal(),
        Some(RewriteRefusal::UnsupportedScope)
    );
}

#[test]
fn typed_integer_iota_consumes_the_shared_budget_before_deep_walk() {
    let limits = crate::instrumentation::TacticWorkLimits {
        simple: 8,
        smart: 8,
        control: 8,
    };
    let tactic = crate::instrumentation::TacticEvent {
        source_tactic_path: None,
        claim: "integer.typed_iota_budget".into(),
        tactic_index: 0,
        tactic_name: "typed_iota_budget".into(),
        class: "simple".into(),
        statement_index: 0,
        source_index: 0,
    };
    let mut measured_work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let scrutinee_variable = Variable(9960);
        let binding = Variable(9961);
        let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![AlgebraicVariantType {
            name: "Wrapped".into(),
            fields: vec![AlgebraicValueType::Integer],
        }]
        .into();
        let value_type = AlgebraicValueType::Algebraic {
            name: "BudgetMatch".into(),
            arguments: vec![],
        };
        let algebraic_type = AlgebraicType {
            rigid: false,
            name: "BudgetMatch".into(),
            arguments: vec![],
            variants: variants.clone(),
            schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
                value_type, variants,
            )]))),
        };
        let mut body = IntegerTerm::var(binding);
        for _ in 0..depth {
            body = IntegerTerm::Add(body.into(), IntegerTerm::constant_i64(1).into());
        }
        let input = IntegerTerm::AlgebraicMatch {
            scrutinee: Box::new(AlgebraicTerm {
                algebraic_type: algebraic_type.clone(),
                node: AlgebraicTermNode::Variable(scrutinee_variable),
            }),
            arms: vec![AlgebraicIntegerMatchArm {
                binding_names: Default::default(),
                variant: "Wrapped".into(),
                bindings: vec![AlgebraicValue::Integer(IntegerTerm::var(binding))],
                body: body.into(),
            }],
        };
        let constructor = AlgebraicTerm {
            algebraic_type,
            node: AlgebraicTermNode::Constructor {
                variant: "Wrapped".into(),
                fields: vec![AlgebraicValue::Integer(IntegerTerm::constant_i64(7))],
            },
        };
        let program_replacements = BTreeMap::new();
        let integer_replacements = BTreeMap::new();
        let mut algebraic_replacements = BTreeMap::new();
        algebraic_replacements.insert(scrutinee_variable, constructor);
        let ((output, exhausted, visits, work), events) =
            crate::instrumentation::with_tactic_work_limits(limits, || {
                crate::instrumentation::collect(|| {
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticStarted(tactic.clone()),
                    );
                    let mut rewrite = TermRewrite::for_typed_variables(
                        &program_replacements,
                        &integer_replacements,
                        &algebraic_replacements,
                    );
                    let (output, work) = crate::instrumentation::measure_deterministic_work(|| {
                        rewrite.integer(&input)
                    });
                    let result = (output, rewrite.integer_work_exhausted, rewrite.visits, work);
                    crate::instrumentation::emit(
                        crate::instrumentation::VerificationEvent::TacticFailed(tactic.clone()),
                    );
                    result
                })
            });
        assert!(exhausted, "typed iota must consume the enclosing budget");
        assert!(visits <= 16, "typed iota continued after budget exhaustion");
        assert!(work <= 16, "collector work ignored the enclosing budget");
        assert!(matches!(output, IntegerTerm::AlgebraicMatch { .. }));
        assert!(events.iter().any(|event| matches!(
            event,
            crate::instrumentation::VerificationEvent::TacticWorkBudgetExceeded { .. }
        )));
        measured_work.push(work);
    }
    assert!(measured_work.windows(2).all(|pair| pair[1] <= 16));
}

#[test]
fn integer_fold_rewrite_shared_wrappers_charge_linear_work() {
    let source = Variable(1_040);
    let accumulator = Variable(1_041);
    let item = Variable(1_042);
    let mut samples = Vec::new();
    for depth in [8, 16, 32, 64] {
        let mut common = IntegerTerm::var(Variable(1_043));
        for _ in 0..depth {
            let child: SharedIntegerTerm = common.into();
            common = IntegerTerm::Add(child.clone(), child);
        }
        let shared_body: SharedIntegerTerm = common.into();
        let make_fold = |initial| {
            IntegerTerm::range_fold(
                crate::kernel::IntegerRangeFoldIndex::Integer {
                    start: IntegerTerm::constant_i64(0).into(),
                    end: IntegerTerm::constant_i64(1).into(),
                },
                IntegerTerm::constant_i64(initial),
                accumulator,
                item,
                shared_body.as_ref().clone(),
            )
        };
        let root = IntegerTerm::Add(make_fold(0).into(), make_fold(1).into());
        let renamings = BTreeMap::new();
        let replacement = IntegerTerm::constant_i64(7);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            rewrite.term(&Term::Integer(root))
        });
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "shared fold rewrite work grew superlinearly: {samples:?}"
        );
    }
}

#[test]
fn integer_fold_nested_capture_and_nocapture_work_scales_linearly() {
    fn integer_index_fold(body: IntegerTerm, accumulator: Variable, item: Variable) -> IntegerTerm {
        IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body,
        )
    }

    fn int32_index_fold(body: IntegerTerm, accumulator: Variable, item: Variable) -> IntegerTerm {
        IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(MachineTerm::constant(1)),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body,
        )
    }

    let depths = [8, 16, 32, 64];
    let source = Variable(2_100_000);
    let replacement = IntegerTerm::constant_i64(7);
    let mut nocapture_work = Vec::new();
    for depth in depths {
        let mut nested = IntegerTerm::var(source);
        for level in 0..depth {
            let accumulator = Variable(2_100_100 + level as u64 * 2);
            let item = Variable(2_100_101 + level as u64 * 2);
            nested = integer_index_fold(
                IntegerTerm::add(nested, IntegerTerm::var(accumulator)),
                accumulator,
                item,
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let renamings = BTreeMap::new();
            let mut rewrite =
                TermRewrite::for_integer_variables(source, &replacement, false, &renamings);
            let result = rewrite.term(&Term::Integer(nested));
            (
                result,
                rewrite.unsupported_integer_scope,
                rewrite.integer_work_exhausted,
            )
        });
        assert!(!result.1 && !result.2);
        let Term::Integer(result) = result.0 else {
            unreachable!()
        };
        let mut free = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(&result, &mut free);
        assert!(!free.contains(&source));
        nocapture_work.push(work);
    }

    let integer_source = Variable(2_101_000);
    let integer_accumulator = Variable(2_101_001);
    let program_item = Variable(2_101_002);
    let mut integer_to_c_work = Vec::new();
    for depth in depths {
        let mut nested = IntegerTerm::var(integer_source);
        for _ in 0..depth {
            nested = int32_index_fold(
                IntegerTerm::add(nested, IntegerTerm::var(integer_accumulator)),
                integer_accumulator,
                program_item,
            );
        }
        let mut integer_to_c_replacement = IntegerTerm::var(integer_accumulator);
        for _ in 0..depth {
            integer_to_c_replacement = IntegerTerm::add(
                integer_to_c_replacement,
                IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                    crate::kernel::MachineIntegerType::Int32,
                    MachineTerm::Variable(program_item),
                )),
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let renamings = BTreeMap::new();
            let mut rewrite = TermRewrite::for_integer_variables(
                integer_source,
                &integer_to_c_replacement,
                false,
                &renamings,
            );
            let result = rewrite.term(&Term::Integer(nested));
            (
                result,
                rewrite.unsupported_integer_scope,
                rewrite.integer_work_exhausted,
            )
        });
        assert!(!result.1 && !result.2);
        let Term::Integer(result) = result.0 else {
            unreachable!()
        };
        let IntegerTerm::RangeFold {
            accumulator: fresh_accumulator,
            item: fresh_item,
            ..
        } = &result
        else {
            unreachable!()
        };
        assert_ne!(*fresh_accumulator, integer_accumulator);
        assert_ne!(*fresh_item, program_item);
        let mut free_integer = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(&result, &mut free_integer);
        assert!(free_integer.contains(&integer_accumulator));
        let mut free_c = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(&result, &mut free_c);
        assert!(free_c.contains(&program_item));
        integer_to_c_work.push(work);
    }

    let c_source = Variable(2_102_000);
    let c_accumulator = Variable(2_102_001);
    let integer_item = Variable(2_102_002);
    let mut c_to_integer_work = Vec::new();
    for depth in depths {
        let mut nested = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            MachineTerm::Variable(c_source),
        ));
        for _ in 0..depth {
            nested = integer_index_fold(
                IntegerTerm::add(nested, IntegerTerm::var(c_accumulator)),
                c_accumulator,
                integer_item,
            );
        }
        let mut replacement_value = IntegerTerm::var(c_accumulator);
        for _ in 0..depth {
            replacement_value = IntegerTerm::add(replacement_value, IntegerTerm::constant_i64(1));
        }
        let c_to_integer_replacement = MachineTerm::IntegerToMachine {
            value: SharedIntegerTerm::from(replacement_value),
            destination: crate::kernel::MachineIntegerType::Int32,
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let source_term = MachineTerm::Variable(c_source);
            let mut rewrite = TermRewrite::for_bits(&source_term, &c_to_integer_replacement);
            let result = rewrite.term(&Term::Integer(nested));
            (
                result,
                rewrite.unsupported_integer_scope,
                rewrite.integer_work_exhausted,
            )
        });
        assert!(!result.1 && !result.2);
        let Term::Integer(result) = result.0 else {
            unreachable!()
        };
        let IntegerTerm::RangeFold {
            accumulator: fresh_accumulator,
            ..
        } = &result
        else {
            unreachable!()
        };
        assert_ne!(*fresh_accumulator, c_accumulator);
        let mut free_integer = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_free_variables(&result, &mut free_integer);
        assert!(free_integer.contains(&c_accumulator));
        c_to_integer_work.push(work);
    }

    for samples in [nocapture_work, integer_to_c_work, c_to_integer_work] {
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 4,
                "nested fold rewrite work grew superlinearly: {samples:?}"
            );
        }
    }
}

#[test]
fn checked_fold_collectors_bound_mixed_carrier_payloads_and_opaque_states() {
    fn integer_index_fold(body: IntegerTerm, accumulator: Variable, item: Variable) -> IntegerTerm {
        IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::constant_i64(1).into(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body,
        )
    }

    fn int32_index_fold(body: IntegerTerm, accumulator: Variable, item: Variable) -> IntegerTerm {
        IntegerTerm::range_fold(
            crate::kernel::IntegerRangeFoldIndex::Int32 {
                start: crate::kernel::SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
                end: crate::kernel::SharedIntegerRangeEndpoint::intern(MachineTerm::constant(1)),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            item,
            body,
        )
    }

    fn memory_state_identity(depth: usize) -> crate::kernel::SharedMemory {
        let block = PointerBlock::Concrete("checked-fold-opaque".into());
        let mut memory = Memory::new().with_block(block.clone(), depth as u32 + 1);
        for offset in 0..depth {
            memory = memory.store(
                Pointer {
                    block: block.clone(),
                    offset: PointerOffsetTerm::Constant(offset as i64),
                },
                ProgramValue::Int32(MachineTerm::constant(offset as u32)),
            );
        }
        crate::kernel::intern_memory(memory)
    }

    // Memory states are opaque to lexical collection. Keep the
    // expression and its carrier payload fixed while changing only the
    // state size; the checked rewrite work must stay unchanged.
    let fixed_source = Variable(3_010_000);
    let fixed_accumulator = Variable(3_010_001);
    let fixed_item = Variable(3_010_002);
    let mut fixed_body = IntegerTerm::var(fixed_source);
    for _ in 0..16 {
        fixed_body = int32_index_fold(
            IntegerTerm::add(fixed_body, IntegerTerm::var(fixed_accumulator)),
            fixed_accumulator,
            fixed_item,
        );
    }
    let mut state_work = Vec::new();
    for state_size in [0usize, 256] {
        let memory = memory_state_identity(state_size);
        let pointer = Pointer {
            block: PointerBlock::Concrete("checked-fold-opaque".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let replacement_payload =
            MachineTerm::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Int32);
        let replacement = IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
            crate::kernel::MachineIntegerType::Int32,
            replacement_payload,
        ));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_checked_simple_budget(1_000_000, || {
                let renamings = BTreeMap::new();
                let mut rewrite = TermRewrite::for_integer_variables(
                    fixed_source,
                    &replacement,
                    false,
                    &renamings,
                );
                let output = rewrite.term(&Term::Integer(fixed_body.clone()));
                (
                    rewrite.unsupported_integer_scope,
                    rewrite.integer_work_exhausted,
                    output,
                )
            })
        });
        assert!(!result.0 && !result.1);
        assert!(matches!(result.2, Term::Integer(_)));
        state_work.push(work);
    }
    assert_eq!(state_work[0], state_work[1]);

    let mut integer_to_c_work = Vec::new();
    let mut c_to_integer_work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let memory = memory_state_identity(depth);
        let pointer = Pointer {
            block: PointerBlock::Concrete("checked-fold-opaque".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let integer_source = Variable(3_000_000 + depth as u64);
        let mut int32_body = IntegerTerm::var(integer_source);
        let mut integer_accumulators = Vec::new();
        let mut c_items = Vec::new();
        for level in 0..depth {
            let accumulator = Variable(3_001_000 + level as u64 * 2);
            let item = Variable(3_001_001 + level as u64 * 2);
            integer_accumulators.push(accumulator);
            c_items.push(item);
            int32_body = int32_index_fold(
                IntegerTerm::add(int32_body, IntegerTerm::var(accumulator)),
                accumulator,
                item,
            );
        }
        let integer_capture = *integer_accumulators.last().unwrap();
        let c_capture = *c_items.last().unwrap();
        let mut mixed_c_payload = MachineTerm::MemoryLoad(
            memory.clone(),
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Int32,
        );
        for _ in 0..depth {
            mixed_c_payload = binary_node!(
                Int32,
                Add,
                Box::new(mixed_c_payload),
                Box::new(MachineTerm::IntegerToMachine {
                    value: SharedIntegerTerm::from(IntegerTerm::var(integer_capture)),
                    destination: crate::kernel::MachineIntegerType::Int32,
                }),
            );
            mixed_c_payload = binary_node!(
                Int32,
                Add,
                Box::new(mixed_c_payload),
                Box::new(MachineTerm::Variable(c_capture)),
            );
        }
        let integer_to_c_replacement =
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                mixed_c_payload.clone(),
            ));
        let (result, work, attempts) = {
            let _collection_scope = crate::instrumentation::CheckedCollectionScope::new();
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                with_checked_simple_budget(10, || {
                    let renamings = BTreeMap::new();
                    let mut rewrite = TermRewrite::for_integer_variables(
                        integer_source,
                        &integer_to_c_replacement,
                        false,
                        &renamings,
                    );
                    let output = rewrite.term(&Term::Integer(int32_body.clone()));
                    (rewrite.integer_work_exhausted, output)
                })
            });
            let attempts = crate::instrumentation::checked_collection_attempts();
            (result, work, attempts)
        };
        assert!(result.0, "low checked budget unexpectedly completed");
        assert!(
            attempts <= 32,
            "collector kept attempting siblings: {attempts}"
        );
        assert!(
            work <= 64,
            "collector kept charging after exhaustion: {work}"
        );

        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_checked_simple_budget(1_000_000, || {
                let renamings = BTreeMap::new();
                let mut rewrite = TermRewrite::for_integer_variables(
                    integer_source,
                    &integer_to_c_replacement,
                    false,
                    &renamings,
                );
                let output = rewrite.term(&Term::Integer(int32_body.clone()));
                (
                    rewrite.unsupported_integer_scope,
                    rewrite.integer_work_exhausted,
                    output,
                )
            })
        });
        assert!(!result.0 && !result.1);
        let Term::Integer(output) = result.2 else {
            unreachable!()
        };
        let mut free_c = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(&output, &mut free_c);
        assert!(!free_c.contains(&integer_source));
        integer_to_c_work.push(work);

        let c_source = Variable(3_002_000 + depth as u64);
        let mut c_to_integer_body =
            IntegerTerm::Machine(crate::kernel::SharedMachineIntegerTerm::intern(
                crate::kernel::MachineIntegerType::Int32,
                MachineTerm::Variable(c_source),
            ));
        let mut math_accumulators = Vec::new();
        let mut mixed_c_items = Vec::new();
        for level in 0..depth {
            if level % 2 == 0 {
                let accumulator = Variable(3_003_000 + level as u64 * 2);
                let item = Variable(3_003_001 + level as u64 * 2);
                math_accumulators.push(accumulator);
                c_to_integer_body = integer_index_fold(c_to_integer_body, accumulator, item);
            } else {
                let accumulator = Variable(3_004_000 + level as u64 * 2);
                let item = Variable(3_004_001 + level as u64 * 2);
                mixed_c_items.push(item);
                c_to_integer_body = int32_index_fold(c_to_integer_body, accumulator, item);
            }
        }
        let math_capture = *math_accumulators.last().unwrap();
        let c_item_capture = *mixed_c_items.last().unwrap();
        let mut c_replacement =
            MachineTerm::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Int32);
        for _ in 0..depth {
            c_replacement = binary_node!(
                Int32,
                Add,
                Box::new(c_replacement),
                Box::new(MachineTerm::IntegerToMachine {
                    value: SharedIntegerTerm::from(IntegerTerm::var(math_capture)),
                    destination: crate::kernel::MachineIntegerType::Int32,
                }),
            );
            c_replacement = binary_node!(
                Int32,
                Add,
                Box::new(c_replacement),
                Box::new(MachineTerm::Variable(c_item_capture)),
            );
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            with_checked_simple_budget(1_000_000, || {
                let source = MachineTerm::Variable(c_source);
                let mut rewrite = TermRewrite::for_bits_checked(&source, &c_replacement);
                let output = rewrite.term(&Term::Integer(c_to_integer_body.clone()));
                (
                    rewrite.unsupported_integer_scope,
                    rewrite.integer_work_exhausted,
                    output,
                )
            })
        });
        assert!(!result.0 && !result.1);
        let Term::Integer(output) = result.2 else {
            unreachable!()
        };
        let mut free_c = std::collections::BTreeSet::new();
        crate::kernel::prelude::collect_integer_capture_bitvector_variables(&output, &mut free_c);
        assert!(!free_c.contains(&c_source));
        c_to_integer_work.push(work);
    }
    for samples in [integer_to_c_work, c_to_integer_work] {
        for pair in samples.windows(2) {
            assert!(
                pair[1] <= pair[0] * 8 + 64,
                "checked collector work grew too quickly: {samples:?}"
            );
        }
    }
}

#[test]
fn checked_substitution_collector_reuses_registered_load_dag() {
    let source = Variable(3_104_000);
    let mut work = Vec::new();
    for depth in [8usize, 16, 32, 64] {
        let memory = crate::kernel::intern_memory(Memory::new().with_block("array", 16));
        let leaf_pointer = Pointer {
            block: PointerBlock::Concrete("array".into()),
            offset: PointerOffsetTerm::scaled_int32_node(
                MachineTerm::IntegerToMachine {
                    value: IntegerTerm::var(source).into(),
                    destination: MachineIntegerType::Int32,
                },
                4,
            ),
        };
        let mut load = crate::kernel::eval::load_variable_for_exact_cell(
            &memory,
            &leaf_pointer,
            crate::kernel::LoadKind::Int32,
            4,
        );
        for _ in 0..depth {
            load = crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &Pointer {
                    block: PointerBlock::Concrete("array".into()),
                    offset: PointerOffsetTerm::Variable(load),
                },
                crate::kernel::LoadKind::Int32,
                4,
            );
        }
        let atom = Proposition::MemoryLoadable {
            memory: memory.as_ref().clone(),
            base: Pointer {
                block: PointerBlock::Concrete("array".into()),
                offset: PointerOffsetTerm::Variable(load),
            },
            bytes: MachineTerm::constant(4),
            wide: false,
        };
        let mut proposition = atom.clone();
        for _ in 0..depth {
            proposition = Proposition::And(Box::new(proposition), Box::new(atom.clone()));
        }
        let ((contains_source, nodes, exhausted), measured) =
            crate::instrumentation::measure_deterministic_work(|| {
                let mut collector = IntegerSubstitutionVariableCollector::checked();
                collector.collect(&proposition);
                (
                    collector.carriers.integer.contains(&source),
                    collector.carriers.nodes,
                    collector.exhausted(),
                )
            });
        assert!(
            contains_source,
            "registered pointer carrier was not collected"
        );
        assert!(!exhausted, "collector exhausted at depth {depth}");
        assert!(nodes > depth, "collector skipped the selected pointer DAG");
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3,
            "registered-load collector expanded a shared DAG: {work:?}"
        );
    }
}

#[test]
fn native_unsigned_offset_projection_checks_full_width_bounds_and_scopes() {
    let index = MachineTerm::Variable(Variable(989_100));
    let native = PointerOffsetTerm::scaled_int64_node(index.clone(), 4, true);
    let narrow =
        PointerOffsetTerm::scaled_int32_node(MachineTerm::uint32_from_64(index.clone()), 4);
    let bound = ConditionTerm::uint64_less_equal(
        index.clone(),
        MachineTerm::uint64_constant(1_073_741_823),
    );
    let projection = |condition, truth| {
        let conditions = HashMap::from([(condition, truth)]);
        let mut rewrite = TermRewrite::for_conditions(&conditions);
        let result = rewrite.offset(&native);
        assert!(rewrite.refusal().is_none());
        result
    };
    for (condition, truth) in [
        (bound.clone(), true),
        (
            ConditionTerm::uint64_less_than(
                index.clone(),
                MachineTerm::uint64_constant(1_073_741_824),
            ),
            true,
        ),
        (
            ConditionTerm::uint64_greater_equal(
                MachineTerm::uint64_constant(1_073_741_823),
                index.clone(),
            ),
            true,
        ),
        (
            ConditionTerm::uint64_greater_than(
                index.clone(),
                MachineTerm::uint64_constant(1_073_741_823),
            ),
            false,
        ),
        (
            ConditionTerm::uint64_greater_equal(
                index.clone(),
                MachineTerm::uint64_constant(1_073_741_824),
            ),
            false,
        ),
    ] {
        assert_eq!(projection(condition, truth), narrow);
    }
    for (condition, truth) in [
        (bound.clone(), false),
        (
            ConditionTerm::signed_less_equal(
                MachineTerm::uint32_from_64(index.clone()),
                MachineTerm::constant(1_073_741_823),
            ),
            true,
        ),
        (
            ConditionTerm::int64_signed_less_equal(
                index.clone(),
                MachineTerm::int64_constant(1_073_741_823),
            ),
            true,
        ),
        (
            ConditionTerm::uint64_less_equal(
                index.clone(),
                MachineTerm::uint64_constant(1u64 << 32),
            ),
            true,
        ),
        (
            ConditionTerm::uint64_less_than(index.clone(), MachineTerm::uint64_constant(0)),
            true,
        ),
        (
            ConditionTerm::uint64_equal(index.clone(), MachineTerm::uint64_constant(1u64 << 32)),
            true,
        ),
    ] {
        assert_eq!(projection(condition, truth), native);
    }
    let conditions = HashMap::from([(bound.clone(), true)]);
    let signed = PointerOffsetTerm::scaled_int64_node(index.clone(), 4, false);
    let mut rewrite = TermRewrite::for_conditions(&conditions);
    assert_eq!(rewrite.offset(&signed), signed);
    let binder = Proposition::ForAll {
        name: Default::default(),
        var: Variable(989_100),
        sort: Sort::ProgramInteger(MachineIntegerType::UInt64),
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(native.clone(), narrow.clone()),
            true,
        )),
    };
    assert_eq!(rewrite.proposition(&binder), binder);
    assert!(rewrite.refusal().is_none());
    let goal = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(native.clone(), narrow),
        true,
    );
    let premise = Proposition::ConditionIs(bound, true);
    let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&premise));
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            std::slice::from_ref(&premise),
            &facts
        )
        .is_ok()
    );
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &goal,
            &[premise],
            &crate::kernel::proof::ProofFacts::from_ordered(&[])
        )
        .is_err()
    );
    let mut costs = Vec::new();
    let mut preparation_overheads = Vec::new();
    for size in [0, 8, 64, 512] {
        let mut explicit = conditions.clone();
        for offset in 0..size {
            explicit.insert(
                ConditionTerm::uint64_less_equal(
                    MachineTerm::Variable(Variable(990_000 + offset)),
                    MachineTerm::uint64_constant(123),
                ),
                true,
            );
        }
        let (mut rewrite, prep) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_conditions(&explicit)
        });
        assert_eq!(prep, 0, "scalar rewrites do not prepare pointer bounds");
        let (_, pointer_prep) = crate::instrumentation::measure_deterministic_work(|| {
            assert_ne!(rewrite.offset(&native), native);
        });
        assert!(pointer_prep > size as usize);
        preparation_overheads.push(pointer_prep - size as usize);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..64 {
                assert_ne!(rewrite.offset(&native), native);
            }
        });
        assert!(rewrite.refusal().is_none());
        costs.push(work);
    }
    assert!(
        preparation_overheads
            .iter()
            .all(|cost| *cost == preparation_overheads[0]),
        "pointer-bound preparation must charge one pass over explicit premises: {preparation_overheads:?}"
    );
    assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
}

fn generic_read_alias_rewrite_work(count: u64, unrelated: u64, warm: bool) -> usize {
    let _session = crate::kernel::VerificationSession::enter();
    let parameter = TypeParameterName::intern("GenericRewriteScalingT");
    let stored = ProgramValue::Parameter(Box::new(AlgebraicTerm {
        algebraic_type: parameter.algebraic_type(),
        node: AlgebraicTermNode::Variable(Variable(996_030)),
    }));
    let mut memory = Memory::new();
    for index in 0..=unrelated {
        memory = memory.store(
            Pointer {
                block: PointerBlock::Heap(996_100 + index),
                offset: PointerOffsetTerm::Constant(0),
            },
            stored.clone(),
        );
    }
    let memory = crate::kernel::intern_memory(memory);
    let from = PointerValue::new(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramType::Int32Pointer,
    );
    let read = AlgebraicTermNode::parameter_load(memory.clone(), from.pointer().clone(), parameter);
    // Catch up the input's pointer-reachable index once for the warm-query
    // axis. Every measured alias is still fresh. The cold axis below charges
    // this initial delta as well and grows cells and queries together.
    if warm {
        let _ = AlgebraicTermNode::parameter_load(
            memory.clone(),
            Pointer::symbolic(Variable(998_000)),
            parameter,
        );
    }
    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
        for index in 0..count {
            let to = PointerValue::new(
                Pointer::symbolic(Variable(997_000 + index)),
                ProgramType::Int32Pointer,
            );
            let rewritten = TermRewrite::for_pointer_value_exact(&from, &to).value(&read);
            let expected =
                AlgebraicTermNode::parameter_load(memory.clone(), to.pointer().clone(), parameter);
            assert_eq!(rewritten, expected);
            assert_ne!(rewritten, stored);
        }
    });
    work
}

#[test]
fn generic_read_alias_rewrites_scale_with_selected_reads() {
    let samples = [8, 16, 32, 64].map(|count| generic_read_alias_rewrite_work(count, 16, false));
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn generic_read_alias_rewrites_ignore_caught_up_unrelated_cells() {
    let samples =
        [0, 16, 64, 256].map(|unrelated| generic_read_alias_rewrite_work(8, unrelated, true));
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn generic_read_alias_rewrites_keep_cold_total_work_linear() {
    let samples = [8, 16, 32, 64].map(|size| generic_read_alias_rewrite_work(size, size, false));
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 64),
        "{samples:?}"
    );
}

fn full_pointer_read_version_rewrite_work(count: u64, unrelated: u64) -> usize {
    let _session = crate::kernel::VerificationSession::enter();
    let to = PointerValue::new(
        Pointer::symbolic(Variable(997_500)),
        ProgramType::Int32PointerPointer,
    );
    let stored = ProgramValue::pointer(Pointer::symbolic(Variable(997_501)));
    let mut memory = Memory::new();
    for index in 0..unrelated {
        memory = memory.store(
            Pointer::symbolic(Variable(998_500 + index)),
            ProgramValue::Int32(7u32.into()),
        );
    }
    let memory = memory.store(to.pointer().clone(), stored.clone());
    let inputs = (0..count)
        .map(|index| {
            let from = PointerValue::new(
                Pointer::symbolic(Variable(999_500 + index)),
                ProgramType::Int32PointerPointer,
            );
            let read =
                memory.symbolic_pointer_version_load(from.pointer(), ProgramType::Int32Pointer);
            (from, read)
        })
        .collect::<Vec<_>>();
    let (rewritten, work) = crate::instrumentation::measure_deterministic_work(|| {
        inputs
            .iter()
            .map(|(from, read)| TermRewrite::for_pointer_value_exact(from, &to).value(read))
            .collect::<Vec<_>>()
    });
    let expected = memory.symbolic_pointer_version_load(to.pointer(), ProgramType::Int32Pointer);
    assert_ne!(expected, stored);
    assert!(rewritten.iter().all(|value| *value == expected));
    work
}

#[test]
fn full_pointer_read_version_rewrites_scale_with_selected_reads() {
    let samples = [8, 16, 32, 64].map(|count| full_pointer_read_version_rewrite_work(count, 16));
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn full_pointer_read_version_rewrites_ignore_unrelated_cells() {
    let samples =
        [0, 16, 64, 256].map(|unrelated| full_pointer_read_version_rewrite_work(8, unrelated));
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

fn numeric_pointer_read_rewrite_work(
    depth: usize,
    repeats: usize,
    unrelated: u64,
    separate: bool,
) -> usize {
    let _session = crate::kernel::VerificationSession::enter();
    let from = MachineTerm::Variable(Variable(997_020));
    let to = MachineTerm::Variable(Variable(997_021));
    let address = |index| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(index, 8),
    };
    let mut memory = Memory::new();
    for index in 0..unrelated {
        memory = memory.store(
            Pointer {
                block: if separate {
                    PointerBlock::Temporary(998_020 + index)
                } else {
                    PointerBlock::Symbolic(Variable(998_020 + index))
                },
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramValue::Int32(7u32.into()),
        );
    }
    let memory = memory.store(address(to.clone()), ProgramValue::pointer(Pointer::null()));
    let memory = crate::kernel::intern_memory(memory);
    let mut input = address(from.clone());
    for _ in 0..depth {
        input = Pointer::version_read(&memory, &input);
    }
    let input = ProgramValue::pointer(input);
    let (outputs, work) = crate::instrumentation::measure_deterministic_work(|| {
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        (0..repeats)
            .map(|_| rewrite.value(&input))
            .collect::<Vec<_>>()
    });
    let mut expected = address(to);
    for _ in 0..depth {
        expected = Pointer::version_read(&memory, &expected);
    }
    let expected = ProgramValue::pointer(expected);
    assert_ne!(expected, input);
    assert!(outputs.iter().all(|output| *output == expected));
    work
}

#[test]
fn numeric_pointer_read_rewrites_scale_with_nested_definitions() {
    let samples =
        [8, 16, 32, 64].map(|depth| numeric_pointer_read_rewrite_work(depth, 1, 16, false));
    assert!(samples[0] > 0);
    assert!(
        samples
            .windows(3)
            .all(|points| points[2] - points[1] <= 2 * (points[1] - points[0]) + 8),
        "{samples:?}"
    );
}

#[test]
fn numeric_pointer_read_rewrites_reuse_shared_definitions() {
    let samples =
        [1, 4, 16, 64].map(|repeats| numeric_pointer_read_rewrite_work(64, repeats, 16, false));
    assert!(samples[0] > 0);
    for (repeats, work) in [1, 4, 16, 64].into_iter().zip(samples) {
        assert!(work <= samples[0] + 16 * repeats, "{samples:?}");
    }
}

#[test]
fn numeric_pointer_read_rewrites_ignore_other_potential_alias_cells() {
    let samples =
        [0, 16, 64, 256].map(|unrelated| numeric_pointer_read_rewrite_work(8, 1, unrelated, false));
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn numeric_pointer_read_rewrites_ignore_separate_storage() {
    let samples =
        [0, 16, 64, 256].map(|unrelated| numeric_pointer_read_rewrite_work(8, 1, unrelated, true));
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn arithmetic_comparison_memos_are_bounded_and_session_local() {
    let mut cold_work = Vec::new();
    for size in [4usize, 16, 64] {
        let variable = MachineTerm::Variable(Variable(978_445));
        let mut expression = variable.clone();
        for _ in 0..size {
            expression = MachineTerm::logical_machine_binary(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                expression,
                MachineTerm::constant(0),
            );
        }
        let goal = Proposition::ConditionIs(ConditionTerm::equal(expression, variable), true);
        let measure = || {
            crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::arithmetic_comparison_form(&goal)
            })
        };
        let first;
        {
            let _session = crate::kernel::VerificationSession::enter();
            assert!(
                with_checked_simple_budget(2, || crate::kernel::arithmetic_comparison_form(&goal))
                    .is_none()
            );
            // A budget refusal must not become a cached negative answer.
            first = measure();
            assert!(first.0.is_some());
            let warm = measure();
            assert_eq!(warm.0, first.0);
            assert!(warm.1 <= 2, "completed lookup should reuse the comparison");
        }
        {
            let _session = crate::kernel::VerificationSession::enter();
            let fresh = measure();
            assert_eq!(
                fresh, first,
                "prior verification must not warm the next one"
            );
        }
        cold_work.push(first.1);
    }
    assert!(cold_work[1] <= 4 * cold_work[0] + 32);
    assert!(cold_work[2] <= 4 * cold_work[1] + 32);
}

#[test]
fn shared_carrier_collection_reuses_growing_prefixes_without_exporting() {
    let mut samples = Vec::new();
    for size in [8usize, 32, 96] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let variable = Variable(982801);
        let mut root = KernelTerm::variable(KernelType::Program(ProgramType::Int32), variable);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                root = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [root.clone(), root.clone()],
                );
                let machine = SharedMachineIntegerTerm::from_shared(format, root.clone()).unwrap();
                let proposition = Proposition::ConditionIs(
                    ConditionTerm::IntegerEqual(
                        IntegerTerm::Machine(machine.clone()).into(),
                        IntegerTerm::constant_i64(0).into(),
                    ),
                    true,
                );
                let mut collector = IntegerSubstitutionVariableCollector::checked();
                collector.collect(&proposition);
                assert!(!collector.exhausted());
                let mut found = BTreeSet::new();
                collector.extend_into(&mut found);
                assert_eq!(found, BTreeSet::from([variable]));
                assert!(!machine.has_boxed_operand());
                // Comparison forms must use the same collector without exporting.
                assert!(crate::kernel::eval::comparison_form(&proposition).is_none());
                assert!(!machine.has_boxed_operand());
            }
        });
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        let [(small, sw), (large, lw)] = pair else {
            unreachable!()
        };
        assert!(lw * small * 4 <= sw * large * 5, "{samples:?}");
    }
}

#[test]
fn shared_machine_fold_endpoints_rewrite_in_linear_dag_work() {
    let mut work = Vec::new();
    for size in [16usize, 64, 256] {
        let _session = VerificationSession::enter();
        let source = MachineTerm::Variable(Variable(989911));
        let replacement = MachineTerm::Variable(Variable(989912));
        let format = MachineIntegerType::Int32;
        let mut root =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(989911));
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                format,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
        }
        let endpoint = SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0))
            .with_shared_operand(root)
            .unwrap();
        let fold = Term::Integer(IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Int32 {
                start: endpoint.clone(),
                end: endpoint,
            },
            IntegerTerm::constant_i64(0),
            Variable(989913),
            Variable(989914),
            IntegerTerm::var(Variable(989913)),
        ));
        let exports = KernelTermExport::machine_export_count();
        let (output, measured) = crate::instrumentation::measure_deterministic_work(|| {
            let mut rewrite = TermRewrite::for_bits_checked(&source, &replacement);
            let output = rewrite.term(&fold);
            assert!(rewrite.refusal().is_none());
            let (Term::Integer(original), Term::Integer(rewritten)) = (&fold, &output) else {
                panic!("Integer folds");
            };
            let mut graph = crate::kernel::equality_graph::EqualityGraph::default();
            assert!(!graph.are_integer_equal(original, rewritten));
            graph.add_int32_equality(&source, &replacement);
            assert!(graph.are_integer_equal(original, rewritten));
            output
        });
        assert!(matches!(
            output,
            Term::Integer(IntegerTerm::RangeFold { .. })
        ));
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "shared endpoint work: {work:?}");
    }
}

#[test]
fn retained_rewrite_sources_do_not_expand_growing_dags() {
    let mut work = Vec::new();
    for size in [16usize, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let mut source =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(992550));
        let replacement = MachineTerm::Variable(Variable(992551));
        let expected = IntegerTerm::from_machine(format, replacement.clone()).unwrap();
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..size {
                source = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [source.clone(), source.clone()],
                );
                let goal = IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(format, source.clone()).unwrap(),
                );
                let mut rewrite = TermRewrite::for_machine_operands_checked(
                    MachineOperandView::Shared(&source),
                    MachineOperandView::Legacy(&replacement),
                );
                assert_eq!(rewrite.integer(&goal), expected);
                assert!(rewrite.changed);
                assert!(rewrite.refusal().is_none());
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "retained source work: {work:?}");
    }
}

#[test]
fn retained_rewrite_replacements_do_not_reindex_growing_prefixes() {
    let mut work = Vec::new();
    for size in [16usize, 64, 256] {
        let _session = VerificationSession::enter();
        let format = MachineIntegerType::Int32;
        let source =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(992560));
        let goal = IntegerTerm::Machine(
            SharedMachineIntegerTerm::from_shared(format, source.clone()).unwrap(),
        );
        let mut replacement =
            KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(992561));
        let exports = KernelTermExport::machine_export_count();
        let (_, measured) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                replacement = KernelTerm::machine_binary_shared(
                    format,
                    MachineBinaryOp::Add,
                    [
                        replacement.clone(),
                        KernelTerm::variable(
                            KernelType::Program(ProgramType::Int32),
                            Variable(992562 + index as u64),
                        ),
                    ],
                );
                let mut rewrite = TermRewrite::for_machine_operands_checked(
                    MachineOperandView::Shared(&source),
                    MachineOperandView::Shared(&replacement),
                );
                let result = rewrite.integer(&goal);
                assert!(rewrite.changed);
                assert!(rewrite.refusal().is_none());
                let IntegerTerm::Machine(result) = result else {
                    panic!("machine result")
                };
                assert!(
                    matches!(result.operand_view(), MachineOperandView::Shared(root) if root == &replacement)
                );
            }
        });
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        work.push(measured);
    }
    for pair in work.windows(2) {
        assert!(
            pair[1] <= pair[0] * 5,
            "retained replacement work: {work:?}"
        );
    }
}

#[test]
fn resource_read_collection_scales_with_selected_arguments() {
    let mut work = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let memory = crate::kernel::intern_memory(Memory::new());
        let arguments = (0..size)
            .map(|index| {
                AlgebraicValue::Program(ProgramValue::Int32(MachineTerm::MemoryLoad(
                    memory.clone(),
                    Box::new(Pointer::symbolic(Variable(3_219_100 + index as u64))),
                    LoadKind::Int32,
                )))
            })
            .collect();
        let goal = Proposition::ResourceContains {
            parent: Box::new(Resource::Composite {
                name: "selected".into(),
                arguments,
            }),
            child: Box::new(Resource::Emp),
        };
        let (reads, cost) = crate::instrumentation::measure_deterministic_work(|| {
            let mut collector = IntegerSubstitutionVariableCollector::checked();
            collector.collect_read_terms();
            collector.collect(&goal);
            assert!(!collector.exhausted());
            collector.take_read_terms().count()
        });
        assert_eq!(reads, size);
        work.push(cost);
    }
    assert!(work[0] > 0);
    for pair in work.windows(2) {
        assert!(pair[1] > pair[0]);
        assert!(
            pair[1] <= 3 * pair[0],
            "selected resource collection: {work:?}"
        );
    }
}

#[test]
fn one_proposition_read_comparison_batch_scales_with_selected_reads() {
    let mut work = Vec::new();
    for size in [8usize, 16, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(Memory::new());
        let reads: Vec<_> = (0..size)
            .map(|index| {
                MachineTerm::MemoryLoad(
                    memory.clone(),
                    Box::new(Pointer::symbolic(Variable(4_021_000 + index as u64))),
                    LoadKind::Int32,
                )
            })
            .collect();
        let arguments = reads
            .iter()
            .map(|read| {
                let shared = KernelTermImport::default()
                    .machine_arithmetic(MachineIntegerType::Int32, read)
                    .expect("shared read");
                AlgebraicValue::Integer(IntegerTerm::Machine(
                    SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, shared)
                        .unwrap(),
                ))
            })
            .collect();
        // All reads occur in one goal. Rewalking this goal for each replacement
        // is quadratic even though a collection of single-read goals is linear.
        let goal = Proposition::ResourceContains {
            parent: Box::new(Resource::Composite {
                name: "many_reads".into(),
                arguments,
            }),
            child: Box::new(Resource::Emp),
        };
        let (result, cost) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::comparison_read_batch(
                &goal,
                reads
                    .iter()
                    .enumerate()
                    .map(|(index, read)| (read.clone(), MachineTerm::constant(index as u32))),
            )
            .expect("selected comparison")
        });
        let expected = Proposition::ResourceContains {
            parent: Box::new(Resource::Composite {
                name: "many_reads".into(),
                arguments: (0..size)
                    .map(|index| AlgebraicValue::Integer(IntegerTerm::constant_i64(index as i64)))
                    .collect(),
            }),
            child: Box::new(Resource::Emp),
        };
        assert_eq!(result, expected);
        work.push(cost);
    }
    assert!(work[0] > 0);
    for pair in work.windows(2) {
        assert!(pair[1] > pair[0]);
        assert!(pair[1] <= 3 * pair[0], "single proposition batch: {work:?}");
    }
}

#[test]
fn pointer_index_reconstruction_keeps_cold_dags_shared() {
    let mut samples = Vec::new();
    for depth in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let ty = MachineIntegerType::Int32;
        let source = MachineTerm::Variable(Variable(1007320));
        let target = MachineTerm::Variable(Variable(1007321));
        let mut root =
            KernelTerm::variable(KernelType::Program(ty.program_type()), Variable(1007320));
        for _ in 0..depth {
            root =
                KernelTerm::machine_binary_shared(ty, MachineBinaryOp::Add, [root.clone(), root]);
        }
        let offset = PointerOffsetTerm::Int32Scaled {
            value: SharedMachineIntegerTerm::from_shared(ty, root).unwrap(),
            byte_width: 4,
        };
        let before = KernelTermExport::machine_export_count();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_bits_checked(&source, &target).offset(&offset)
        });
        assert_ne!(result, offset);
        assert_eq!(KernelTermExport::machine_export_count(), before);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] * 5, "{samples:?}");
    }
}

#[test]
fn compound_exact_replacement_ignores_only_call_argument_carrier() {
    let _session = VerificationSession::enter();
    let format = MachineIntegerType::Int32;
    let argument = MachineTerm::Variable(Variable(998_930));
    let call = |argument| MachineTerm::ClickFunctionApplication {
        name: "compound_exact_call".into(),
        arguments: vec![argument],
    };
    let native_call = call(PureFunctionArgument::Value(ProgramValue::Int32(
        argument.clone(),
    )));
    let shared_call = call(PureFunctionArgument::SharedMachine(
        SharedMachineIntegerTerm::intern(format, argument),
    ));
    let compound = |operation, value| {
        MachineTerm::machine_binary(format, operation, value, MachineTerm::constant(1))
    };
    for depth in [4, 16, 64] {
        let mut source = native_call.clone();
        let mut target = shared_call.clone();
        for _ in 0..depth {
            source = compound(MachineBinaryOp::Add, source);
            target = compound(MachineBinaryOp::Add, target);
        }
        let replacement = MachineTerm::constant(13);
        let exports = KernelTermExport::machine_export_count();
        let (actual, work) = crate::instrumentation::measure_deterministic_work(|| {
            TermRewrite::for_bits(&source, &replacement).bits(&target)
        });
        assert_eq!(actual, replacement);
        assert!(work < depth * 50 + 200, "depth={depth}: {work}");
        assert_eq!(KernelTermExport::machine_export_count(), exports);
    }
    let source = compound(MachineBinaryOp::Add, native_call);
    let distinct = compound(MachineBinaryOp::Subtract, shared_call);
    let replacement = MachineTerm::constant(13);
    assert_eq!(
        TermRewrite::for_bits(&source, &replacement).bits(&distinct),
        distinct
    );
}

#[test]
fn narrowing_rewrite_visits_scale_with_selected_expression() {
    let from = MachineTerm::Variable(Variable(91));
    let to = MachineTerm::Variable(Variable(92));
    let make = |value: &MachineTerm, size| {
        Term::Bitvector32(MachineTerm::ClickFunctionApplication {
            name: "many".into(),
            arguments: vec![
                PureFunctionArgument::Value(ProgramValue::UInt32(
                    MachineTerm::legacy_cast(
                        MachineCastSpelling::UInt32From64,
                        Box::new(value.clone())
                    )
                ));
                size
            ],
        })
    };
    for size in [16, 64, 256] {
        let mut rewrite = TermRewrite::for_bits(&from, &to);
        assert_eq!(rewrite.term(&make(&from, size)), make(&to, size));
        assert!(rewrite.changed);
        assert_eq!(rewrite.visits, 2 + 2 * size);
    }
}

#[test]
fn conditional_reduction_work_scales_with_selected_expression() {
    let condition = ConditionTerm::Variable(Variable(51));
    let conditions = HashMap::from([(condition.clone(), true)]);
    for size in [16, 64, 256] {
        let input = Term::Bitvector32(MachineTerm::ClickFunctionApplication {
            name: "many".into(),
            arguments: vec![
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::If {
                    condition: Box::new(condition.clone()),
                    then_term: Box::new(MachineTerm::constant(7)),
                    else_term: Box::new(MachineTerm::constant(0)),
                },));
                size
            ],
        });
        let expected = Term::Bitvector32(MachineTerm::ClickFunctionApplication {
            name: "many".into(),
            arguments: vec![
                PureFunctionArgument::Value(ProgramValue::Int32(MachineTerm::constant(
                    7
                ),));
                size
            ],
        });
        let mut rewrite = TermRewrite::for_conditions(&conditions);
        assert_eq!(rewrite.term(&input), expected);
        assert_eq!(rewrite.visits, 2 + 3 * size);
    }
}
