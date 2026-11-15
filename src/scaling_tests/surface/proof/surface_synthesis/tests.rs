// Scaling tests of `src/surface/proof/surface_synthesis/tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn boolean_local_synthesis_round_trips_and_scales_with_local_population() {
    for size in [16usize, 64, 256, 1024] {
        let mut state = ExecutionState::new();
        for index in 0..size {
            state = state.with_local(
                format!("a_{index:04}"),
                crate::kernel::bool_value(MachineTerm::Variable(Variable(2000 + index as u64))),
            );
        }
        let value = crate::kernel::bool_value(MachineTerm::Variable(Variable(9000)));
        let ProgramValue::Bool(term) = &value else {
            unreachable!()
        };
        state = state.with_local("z_bool", value.clone());
        let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
            synthesize_surface_bitvector(
                term,
                ParameterBinding::default(),
                &state,
                &BTreeMap::new(),
            )
        });
        let surface = surface.expect("a normalized Boolean local has its source spelling");
        assert_eq!(
            surface,
            ContractExpression::ProgramExpression(ProgramExpression::Variable("z_bool".into()))
        );
        assert!(
            work >= size && work <= size + 64,
            "{size} locals: {work} work"
        );
        let equality = ClickProposition::Comparison {
            left: surface.clone(),
            operator: ComparisonOperator::Equal,
            right: surface,
        };
        // A `Bool` equals itself (rule L-Eq), so the equality folds.
        let lowered = relower_written_proposition(&equality, &state).unwrap();
        assert_eq!(
            lowered,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true)
        );
    }
}

#[test]
fn pointer_spelling_skips_cyclic_offsets_and_tries_the_next_local() {
    std::thread::Builder::new()
        .stack_size(1792 * 1024)
        .spawn(|| {
            for size in [1usize, 8, 32, 128] {
                let pointer = Pointer {
                    block: crate::kernel::PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Constant(0),
                };
                let cyclic = Pointer {
                    block: pointer.block.clone(),
                    offset: PointerOffsetTerm::scaled_int32_node(
                        MachineTerm::pointer_address(pointer.clone()),
                        4,
                    ),
                };
                let mut state = ExecutionState::new();
                for index in 0..size {
                    state = state.with_local(
                        format!("a_{index:04}"),
                        ProgramValue::typed_pointer(cyclic.clone(), ProgramType::Int32Pointer),
                    );
                }
                let synthesize = |state: &ExecutionState| {
                    synthesize_surface_pointer(
                        &pointer,
                        ParameterBinding::default(),
                        state,
                        &BTreeMap::new(),
                    )
                };
                let (missing, work) =
                    crate::instrumentation::measure_deterministic_work(|| synthesize(&state));
                assert!(missing.is_none());
                assert!(work >= size && work <= 4 * size + 64, "{size}: {work}");
                state = state.with_local(
                    "z_pointer",
                    ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
                );
                for _ in 0..2 {
                    let (found, work) =
                        crate::instrumentation::measure_deterministic_work(|| synthesize(&state));
                    assert_eq!(found, Some(ProgramExpression::Variable("z_pointer".into())));
                    assert!(work >= size && work <= 4 * size + 64, "{size}: {work}");
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn pointer_local_synthesis_skips_unrelated_pointer_blocks() {
    let mut samples = Vec::new();
    for size in [4usize, 16, 64, 256, 1024] {
        let mut state = ExecutionState::new();
        for i in 0..size {
            state = state.with_local(
                format!("a_{i:04}"),
                ProgramValue::pointer(Pointer::symbolic(Variable(982_000 + i as u64))),
            );
        }
        let base = Pointer::symbolic(Variable(984_000));
        state = state.with_local("z_base", ProgramValue::pointer(base.clone()));
        let selected = base.offset_by_bytes(8);
        let (expression, work) = crate::instrumentation::measure_deterministic_work(|| {
            synthesize_surface_pointer(
                &selected,
                ParameterBinding::default(),
                &state,
                &BTreeMap::new(),
            )
        });
        assert_eq!(
            expression,
            Some(ProgramExpression::Add(
                Box::new(ProgramExpression::Variable("z_base".into())),
                Box::new(ProgramExpression::Value(int32(2))),
            ))
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn integer_division_synthesis_work_tracks_the_selected_expression() {
    use crate::kernel::{IntegerTerm, SharedIntegerTerm};
    let variable = Variable(8_410_000);
    let names = BTreeMap::from([(variable, "n".to_string())]);
    let state = ExecutionState::new();
    let samples = [4usize, 8, 16, 32].map(|size| {
        let mut term: SharedIntegerTerm = IntegerTerm::Variable(variable).into();
        for level in 0..size {
            let divisor = IntegerTerm::Constant(4.into()).into();
            term = if level % 2 == 0 {
                IntegerTerm::TruncatingQuotient(term, divisor)
            } else {
                IntegerTerm::TruncatingRemainder(term, divisor)
            }
            .into();
        }
        let _scope = SurfaceSynthesisScope::enter();
        let surface =
            synthesize_surface_integer(&term, ParameterBinding::default(), &state, &names)
                .expect("the selected quotient/remainder chain is spellable");
        let mut cursor = &surface;
        for level in (0..size).rev() {
            let ContractExpression::Call { name, arguments } = cursor else {
                panic!("the selected division node lost its spelling");
            };
            assert_eq!(
                name,
                if level % 2 == 0 {
                    "truncating_quotient"
                } else {
                    "truncating_remainder"
                }
            );
            assert_eq!(arguments.len(), 2);
            assert_eq!(arguments[1], ContractExpression::IntegerLiteral("4".into()));
            cursor = &arguments[0];
        }
        assert_eq!(*cursor, ContractExpression::Binding("n".into()));
        let work = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let slot = slot.borrow();
            let budget = slot.as_ref().unwrap();
            assert_eq!(budget.depth, 0);
            assert_eq!(budget.exhausted_category, None);
            SURFACE_SYNTHESIS_WORK_LIMIT - budget.remaining_work
        });
        assert!(work >= size && work <= 3 * size + 8, "{size}: {work}");
        work
    });
    for pair in samples.windows(2) {
        assert!(pair[1] > pair[0] && pair[1] <= 2 * pair[0], "{samples:?}");
    }
}

#[test]
fn integer_division_synthesis_refuses_shared_dag_expansion_within_its_budget() {
    use crate::kernel::{IntegerTerm, SharedIntegerTerm};
    let variable = Variable(8_420_000);
    let names = BTreeMap::from([(variable, "n".to_string())]);
    let state = ExecutionState::new();
    for size in [16usize, 32, 64, 128] {
        let mut term: SharedIntegerTerm = IntegerTerm::Variable(variable).into();
        for _ in 0..size {
            term = IntegerTerm::TruncatingRemainder(term.clone(), term).into();
        }
        let _scope = SurfaceSynthesisScope::enter();
        assert!(
            synthesize_surface_integer(&term, ParameterBinding::default(), &state, &names)
                .is_none()
        );
        SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let slot = slot.borrow();
            let budget = slot.as_ref().unwrap();
            assert_eq!(budget.depth, 0);
            assert_eq!(budget.exhausted_category, Some("integer"));
            let work = SURFACE_SYNTHESIS_WORK_LIMIT - budget.remaining_work;
            assert!(
                work > 0 && work <= SURFACE_SYNTHESIS_WORK_LIMIT,
                "{size}: {work}"
            );
        });
    }
}

#[test]
fn allocation_result_names_use_one_index_as_recorded_history_grows() {
    let mut samples = Vec::new();
    let mut insertion_samples = Vec::new();
    for count in [4usize, 16, 64, 128] {
        let source = format!(
            "void f() {{ int32* p; {} }}",
            "p = malloc(4);".repeat(count)
        );
        let function = crate::languages::c::syntax::parse_function(&source).unwrap();
        let layout =
            crate::surface::lowering::SourceExecutionLayout::for_function(&function).unwrap();
        let mut retained_states = RecordedStates::new().with_source_layout(layout.clone());
        let mut last = Pointer::null();
        let mut last_region = 0;
        let mut insertion_work = 0;
        for n in 0..count {
            last = Pointer {
                block: PointerBlock::Heap(990_000 + n as u64),
                offset: PointerOffsetTerm::Constant(0),
            };
            last_region = layout
                .source_path_region(&[SourcePathStep::Statement(n + 1)], ProgramPointKind::Exit)
                .unwrap();
            let (_, work) = crate::persistent::measure_persistent_work(|| {
                retained_states.insert(
                    ProgramPointRef {
                        region: CodeRegionRef::Region(last_region),
                        kind: ProgramPointKind::Exit,
                    },
                    ExecutionState::new().with_local(
                        "p",
                        ProgramValue::typed_pointer(last.clone(), ProgramType::Int32Pointer),
                    ),
                )
            });
            insertion_work += work;
        }
        insertion_samples.push((count, insertion_work));
        let ((answer, work), indexed) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                retained_states.allocation_result(&last)
            })
        });
        assert_eq!(answer, Some(CodeRegionRef::Region(last_region)));
        assert_eq!(work, 1);
        samples.push(indexed);
    }
    let (base_count, base_work) = insertion_samples[0];
    assert!(base_work > 0);
    assert!(
        insertion_samples
            .iter()
            .all(|(count, work)| { *work <= base_work * count / base_count * 4 }),
        "{insertion_samples:?}"
    );
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 4 + 8),
        "{samples:?}"
    );
}

#[test]
fn boolean_synthesis_tracks_expression_size_not_unrelated_names() {
    let mut costs = Vec::new();
    for size in [4usize, 16, 64, 256] {
        let mut names = BTreeMap::new();
        for i in 0..size {
            names.insert(Variable(9100 + i as u64), format!("unused_{i}"));
        }
        names.insert(Variable(9000), "flag".into());
        let flag = ConditionTerm::Variable(Variable(9000));
        let fact = Proposition::ConditionIs(
            ConditionTerm::bool_application(
                "choose",
                vec![crate::kernel::PureFunctionArgument::Value(
                    ProgramValue::of_bool(flag),
                )],
            ),
            true,
        );
        let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
            synthesize_surface_proposition_with_bound_variable_names(
                &fact,
                ParameterBinding::default(),
                &ExecutionState::new(),
                &names,
            )
        });
        assert!(surface.is_some());
        costs.push(work);
    }
    assert!(
        costs[0] > 0 && costs.iter().all(|cost| *cost <= costs[0] + 64),
        "{costs:?}"
    );
    for size in [4usize, 8, 16, 32] {
        let mut condition = ConditionTerm::Constant(false);
        for i in 0..size {
            condition = ConditionTerm::bool_if(
                ConditionTerm::bool_application(&format!("p{i}"), vec![]),
                ConditionTerm::Constant(true),
                condition,
            );
        }
        let fact = Proposition::ConditionIs(condition, true);
        let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
            synthesize_surface_proposition(
                &fact,
                ParameterBinding::default(),
                &ExecutionState::new(),
            )
        });
        assert!(surface.is_some());
        assert!(work >= size && work <= 20 * size + 64, "{size}: {work}");
    }
}

#[test]
fn leading_domain_recognition_retains_shared_arithmetic() {
    use crate::kernel::{
        IntegerTerm, KernelTerm, KernelType, MachineBinaryOp, SharedMachineIntegerTerm, Variable,
    };
    let mut previous = None;
    for size in [8, 32, 96] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut root = KernelTerm::variable(
            KernelType::Program(MachineIntegerType::Int32.program_type()),
            Variable(991704),
        );
        for _ in 0..size {
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root.clone()],
            );
        }
        let operand =
            SharedMachineIntegerTerm::from_shared(MachineIntegerType::Int32, root).unwrap();
        for subtract in [false, true] {
            let left = IntegerTerm::Machine(operand.clone()).into();
            let right = IntegerTerm::constant(1.into()).into();
            let exact = if subtract {
                IntegerTerm::Subtract(left, right)
            } else {
                IntegerTerm::Add(left, right)
            };
            let upper = Proposition::ConditionIs(
                ConditionTerm::IntegerLessEqual(
                    exact.clone().into(),
                    IntegerTerm::constant(i32::MAX.into()).into(),
                ),
                true,
            );
            let lower = Proposition::ConditionIs(
                ConditionTerm::IntegerGreaterEqual(
                    exact.into(),
                    IntegerTerm::constant(i32::MIN.into()).into(),
                ),
                true,
            );
            assert!(!is_leading_add_definedness_guard(&upper));
            let domain = Proposition::And(Box::new(upper), Box::new(lower));
            let (recognized, work) = crate::instrumentation::measure_deterministic_work(|| {
                is_leading_add_definedness_guard(&domain)
            });
            assert_eq!(recognized, !subtract);
            assert!(!operand.has_boxed_operand());
            if !subtract {
                if let Some((old_size, old_work)) = previous {
                    assert!(work <= old_work * size / old_size + 32);
                }
                previous = Some((size, work));
            }
        }
    }
}

#[test]
fn common_arithmetic_names_ignore_unrelated_locals_without_exports() {
    use crate::kernel::{KernelTermExport, KernelTermImport, VerificationSession};
    for size in [16, 64, 256] {
        let _session = VerificationSession::enter();
        let native = MachineTerm::logical_machine_binary(
            MachineIntegerType::Int32,
            MachineBinaryOp::Add,
            MachineTerm::Variable(Variable(993410)),
            MachineTerm::constant(1),
        );
        let root = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
        let mut state = ExecutionState::new().with_local("current", ProgramValue::Int32(native));
        for index in 0..size {
            state = state.with_local(
                format!("noise_{index}"),
                ProgramValue::Int32(MachineTerm::Variable(Variable(994000 + index))),
            );
        }
        let exports = KernelTermExport::machine_export_count();
        let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
            raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new())
        });
        assert_eq!(
            surface,
            Some(SurfaceTerm::ProgramExpression(ProgramExpression::Variable(
                "current".into()
            )))
        );
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 32, "{size} unrelated locals: {work} work");
    }
}

#[test]
fn nested_fold_binder_freshening_scales_with_selected_surface() {
    for unrelated in [0, 128, 512] {
        let _ambient = (0..unrelated)
            .map(|n| {
                (
                    format!("ambient_{n}"),
                    SurfaceTerm::IntegerLiteral("0".into()),
                )
            })
            .collect::<BTreeMap<_, _>>();
        for size in [8, 32, 128] {
            let mut expression = SurfaceTerm::Binding("__click_binder_0".into());
            let mut markers = Vec::new();
            for n in 0..size {
                let accumulator = format!("\0acc{n}");
                let item = format!("\0item{n}");
                markers.extend([(accumulator.clone(), None), (item.clone(), None)]);
                expression = SurfaceTerm::RangeFold {
                    start: Box::new(SurfaceTerm::IntegerLiteral("0".into())),
                    end: Box::new(SurfaceTerm::Binding("n".into())),
                    initial: Box::new(SurfaceTerm::Binding(accumulator.clone())),
                    accumulator,
                    item,
                    body: Box::new(expression),
                };
            }
            let (renamed, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::surface::lowering::name_synthesized_binders(&expression, &markers).unwrap()
            });
            assert_eq!(work, 4 * size + 1, "size={size}, unrelated={unrelated}");
            let text = diagnostics::describe_contract_expression(&renamed);
            assert!(!text.contains('\0'));
            assert!(text.contains("__click_binder_0"));
        }
    }
}

#[test]
fn nested_fold_surface_raising_scales_without_ambient_local_scan() {
    let mut baseline = BTreeMap::new();
    for unrelated in [0, 64, 256] {
        for size in [3, 9, 27] {
            let _session = crate::kernel::VerificationSession::enter();
            let n = MachineTerm::Variable(Variable(720000));
            let mut state = ExecutionState::new().with_local("n", ProgramValue::Int32(n.clone()));
            for i in 0..unrelated {
                state = state.with_local(
                    format!("unused_{i}"),
                    ProgramValue::Int32(MachineTerm::Variable(Variable(730000 + i))),
                );
            }
            let mut term = MachineTerm::Variable(Variable(720001));
            for _ in 0..size {
                term = MachineTerm::RangeFold {
                    start: Box::new(MachineTerm::constant(0)),
                    end: Box::new(n.clone()),
                    initial: Box::new(MachineTerm::constant(0)),
                    accumulator: Variable(720001),
                    item: Variable(720002),
                    body: Box::new(term),
                };
            }
            let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
                synthesize_surface_bitvector(
                    &term,
                    ParameterBinding::default(),
                    &state,
                    &BTreeMap::new(),
                )
            });
            assert!(surface.is_some(), "size={size}");
            if unrelated == 0 {
                baseline.insert(size, work);
            } else {
                assert_eq!(work, baseline[&size], "size={size}, unrelated={unrelated}");
            }
            assert!(work <= 100 * size + 100, "size={size}: {work}");
        }
    }
}

#[test]
fn common_match_surface_work_tracks_selected_body_without_exports() {
    use crate::kernel::{
        AlgebraicTermNode, AlgebraicValueType, BindingNames, KernelMatch, KernelMatchArm,
        KernelTerm, KernelTermExport, KernelTermImport, KernelType, MachineBinaryOp,
        PureFunctionArgument,
    };
    for size in [8, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let scrutinee =
            KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(ProgramType::Int32)]);
        let AlgebraicTermNode::Variable(id) = scrutinee.node else {
            panic!()
        };
        let mut import = KernelTermImport::default();
        let scrutinee = import.argument(&PureFunctionArgument::Algebraic(scrutinee));
        let bound = KernelTerm::variable(KernelType::Program(ProgramType::Int32), Variable(991950));
        let mut body = bound.clone();
        for _ in 0..size {
            body = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [body, bound.clone()],
            );
        }
        let matched = KernelMatch::new(
            KernelType::Program(ProgramType::Int32),
            scrutinee,
            vec![(
                KernelMatchArm {
                    variant: "Arm".into(),
                    bindings: vec![bound],
                    binding_names: BindingNames::written(&["item".into()]),
                },
                body,
            )],
        )
        .unwrap();
        let names = BTreeMap::from([(id, "payload".into())]);
        let exports = KernelTermExport::machine_export_count();
        let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
            matches::raise_match(
                &matched,
                ParameterBinding::default(),
                &ExecutionState::new(),
                &names,
            )
        });
        assert!(surface.is_some());
        assert_eq!(KernelTermExport::machine_export_count(), exports);
        assert!(work <= 100 * size + 100, "size={size}, work={work}");
    }
}

#[test]
fn nested_fold_match_call_surface_work_ignores_unrelated_locals() {
    use crate::kernel::{
        AlgebraicValueType, BindingNames, KernelFold, KernelFoldIndex, KernelMatch, KernelMatchArm,
        KernelTerm, KernelTermExport, KernelTermImport, KernelType, PureFunctionArgument,
    };
    let mut baseline = BTreeMap::new();
    for unrelated in [0, 64, 256] {
        for depth in [3, 9, 27] {
            let _session = crate::kernel::VerificationSession::enter();
            let n = MachineTerm::Variable(Variable(992000));
            let mut state = ExecutionState::new().with_local("n", ProgramValue::Int32(n.clone()));
            for i in 0..unrelated {
                state = state.with_local(
                    format!("unused_{i}"),
                    ProgramValue::Int32(MachineTerm::Variable(Variable(993000 + i))),
                );
            }
            let mut import = KernelTermImport::default();
            let scrutinee = import.argument(&PureFunctionArgument::Algebraic(
                KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(ProgramType::Int32)]),
            ));
            let ty = KernelType::Program(ProgramType::Int32);
            let zero = import.machine(MachineIntegerType::Int32, &MachineTerm::constant(0));
            let end = import.machine(MachineIntegerType::Int32, &n);
            let declaration = KernelTerm::variable(ty.clone(), Variable(992003));
            let mut root = KernelTerm::variable(ty.clone(), Variable(992001));
            for _ in 0..depth {
                let matched = KernelMatch::new(
                    ty.clone(),
                    scrutinee.clone(),
                    vec![(
                        KernelMatchArm {
                            variant: "Arm".into(),
                            bindings: vec![declaration.clone()],
                            binding_names: BindingNames::written(&["field".into()]),
                        },
                        root,
                    )],
                )
                .unwrap()
                .into_term();
                let folded = KernelFold::new(
                    KernelFoldIndex::Int32,
                    Variable(992001),
                    Variable(992002),
                    [zero.clone(), end.clone(), zero.clone(), matched],
                )
                .unwrap()
                .into_term();
                root = KernelTerm::checked_call(ty.clone(), "wrapped".into(), vec![folded]);
            }
            let names = BTreeMap::from([(Variable(991900), "payload".into())]);
            let exports = KernelTermExport::machine_export_count();
            let (surface, work) = crate::instrumentation::measure_deterministic_work(|| {
                raise_kernel_term(&root, ParameterBinding::default(), &state, &names)
            });
            let surface = surface.expect("nested fold/match/call spelling");
            let text = crate::surface::diagnostics::describe_contract_expression(&surface);
            assert!(!text.contains('\0'));
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            if unrelated == 0 {
                baseline.insert(depth, work);
            } else {
                assert_eq!(
                    work, baseline[&depth],
                    "depth={depth}, unrelated={unrelated}"
                );
            }
            assert!(work <= 500 * depth + 500, "depth={depth}, work={work}");
        }
    }
}

#[test]
fn array_argument_state_lookup_ignores_unrelated_recorded_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = ProgramValue::pointer(Pointer::symbolic(Variable(981_400)));
    let cell = Pointer {
        block: PointerBlock::Concrete("selected-array-memory".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let selected = ExecutionState::new()
        .with_local("p", pointer.clone())
        .with_memory(
            Memory::new()
                .with_block("selected-array-memory", 4)
                .store(cell.clone(), int32(1)),
        );
    let selector = ProgramPointSelector::from(ProgramPointRef {
        region: CodeRegionRef::Region(0),
        kind: ProgramPointKind::Exit,
    });
    let arguments = [crate::kernel::PureFunctionArgument::ArrayRef {
        memory: selected.memory().clone(),
        pointer,
        element_type: ProgramType::Int32,
    }];
    let mut samples = Vec::new();
    let mut baseline = None;
    for size in [8, 32, 128, 512] {
        let mut points = RecordedStates::new();
        points.insert(selector.clone(), selected.clone());
        for index in 1..=size {
            points.insert(
                ProgramPointRef {
                    region: CodeRegionRef::Region(index),
                    kind: ProgramPointKind::Exit,
                },
                selected.clone().with_memory(
                    Memory::new()
                        .with_block("selected-array-memory", 4)
                        .store(cell.clone(), int32(index as u32 + 1)),
                ),
            );
        }
        let current = selected.clone().with_memory(
            Memory::new()
                .with_block("selected-array-memory", 4)
                .store(cell.clone(), int32(u32::MAX)),
        );
        let _points = SynthesisRecordedPointsScope::enter(&points);
        synthesize_surface_call(
            "selected",
            &arguments,
            ParameterBinding::default(),
            &current,
            &BTreeMap::new(),
        )
        .unwrap();
        let ((call, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                synthesize_surface_call(
                    "selected",
                    &arguments,
                    ParameterBinding::default(),
                    &current,
                    &BTreeMap::new(),
                )
                .expect("the selected memory is recorded")
            })
        });
        let SurfaceTerm::Call { arguments, .. } = call else {
            panic!("call")
        };
        assert!(
            matches!(&arguments[0], SurfaceTerm::At { selector: actual, .. } if *actual == selector)
        );
        assert_eq!(*baseline.get_or_insert(work), work);
        samples.push(map_work);
    }
    assert!(
        samples[3] < samples[0] * 4 + 128,
        "state lookup scanned history: {samples:?}"
    );
}
