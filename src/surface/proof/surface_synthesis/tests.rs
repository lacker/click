use super::*;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};
use crate::kernel::{MachineCastSpelling, MachineTerm};

#[test]
fn separate_round_trips_without_generating_extent_obligations() {
    use crate::kernel::{MemoryRange, PointerValue, Resource};
    for wide in [false, true] {
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(997001)),
            ProgramType::Int32Pointer,
        );
        let end = MachineTerm::Variable(Variable(997002));
        let zero = if wide {
            MachineTerm::uint64_constant(0)
        } else {
            MachineTerm::constant(0)
        };
        let range = if wide {
            MemoryRange::from_pointer_value_wide(&pointer, zero.clone(), end.clone(), 4)
        } else {
            MemoryRange::from_pointer_value(&pointer, zero.clone(), end.clone(), 4)
        };
        let empty = if wide {
            MemoryRange::from_pointer_value_wide(&pointer, zero.clone(), zero, 4)
        } else {
            MemoryRange::from_pointer_value(&pointer, zero.clone(), zero, 4)
        };
        let expected = Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(range)),
            right: Box::new(Resource::Memory(empty)),
        };
        let state = ExecutionState::new()
            .with_local("p", ProgramValue::Pointer(pointer.clone()))
            .with_local(
                "n",
                if wide {
                    ProgramValue::UInt64(end.clone())
                } else {
                    ProgramValue::Int32(end.clone())
                },
            );
        let parameters = vec![
            crate::languages::interface::ImportedParameter::new(
                InterfaceType::Int32Pointer,
                "p".into(),
                None,
            ),
            crate::languages::interface::ImportedParameter::new(
                if wide {
                    InterfaceType::UInt64(crate::languages::c::target::LongRank::LongLong)
                } else {
                    InterfaceType::Int32
                },
                "n".into(),
                None,
            ),
        ];
        let arguments = vec![
            ProgramExpression::Value(ProgramValue::Pointer(pointer)),
            ProgramExpression::Value(if wide {
                ProgramValue::UInt64(end)
            } else {
                ProgramValue::Int32(end)
            }),
        ];
        let raised = synthesize_surface_proposition_with_names(
            &expected,
            ParameterBinding::new(&parameters, &arguments),
            &state,
            &BTreeMap::new(),
        )
        .expect("separation has a structural spelling");
        let text = crate::surface::printing::source_click_proposition(&raised);
        let ty = if wide { "uint64" } else { "int32" };
        let parsed = parser::parse(&format!(
            "theorem probe(p: int32*, n: {ty}) {{ requires {text}; ensures true; }}"
        ))
        .unwrap();
        let Requirement::Proposition(written) = &parsed.theorem_definitions()[0].requires()[0]
        else {
            panic!()
        };
        let (lowered, _, _, obligations) =
            crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
                written, &PureFactContext::new(),
                ContractEnvironment::new(&BTreeMap::new(), &BTreeMap::new()),
                FixedStateFrame::new(&state, &state, None, &RecordedStates::default()),
                SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::new(&[])),
                FixedStateLoweringOptions::default(),
            ).unwrap();
        assert_eq!(lowered, expected, "{text}");
        assert!(
            obligations.is_empty(),
            "naming ranges must not owe physical extents: {obligations:?}"
        );
    }
}

/// Compare structural lowering separately from proving the use site's debts.
/// Ordinary proof operations still check those debts before admitting a fact.
fn relower_written_proposition(
    surface: &ClickProposition,
    state: &ExecutionState,
) -> Result<Proposition, String> {
    relower_written_proposition_with_states(surface, state, state, &RecordedStates::default())
}

fn relower_written_proposition_with_states(
    surface: &ClickProposition,
    pre_state: &ExecutionState,
    state: &ExecutionState,
    recorded_states: &RecordedStates,
) -> Result<Proposition, String> {
    crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
        surface,
        &PureFactContext::new(),
        ContractEnvironment::new(&BTreeMap::new(), &BTreeMap::new()),
        FixedStateFrame::new(pre_state, state, None, recorded_states),
        SpecDefinitions::new(
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
        ),
        FixedStateLoweringOptions::default(),
    )
    .map(|(proposition, _, _, _)| proposition)
}

/// One cell of a foreign static or file-scope object, spelled the way a
/// caller's own contract writes it: the qualified name under the source
/// alias, then the flat cell index used by the caller-side resource range.
fn qualified_cell(name: &str, base: &ProgramValue, index: i32) -> ContractExpression {
    ContractExpression::Index(
        Box::new(ContractExpression::QualifiedC {
            name: name.to_string(),
            lowered: ProgramExpression::Value(base.clone()),
        }),
        Box::new(ContractExpression::IntegerLiteral(index.to_string())),
    )
}

fn qualified_multidimensional_cell(
    name: &str,
    base: &ProgramValue,
    row: i32,
    column: i32,
    columns: i32,
) -> ContractExpression {
    let flat_index = row * columns + column;
    ContractExpression::ArrayIndex {
        base: Box::new(ContractExpression::QualifiedC {
            name: name.to_string(),
            lowered: ProgramExpression::Value(base.clone()),
        }),
        indexes: vec![
            ContractExpression::ProgramExpression(ProgramExpression::Value(int32(row as u32))),
            ContractExpression::ProgramExpression(ProgramExpression::Value(int32(column as u32))),
        ],
        dimensions: vec![1, columns as u32],
        lowered: ProgramExpression::Index(
            Box::new(ProgramExpression::Value(base.clone())),
            Box::new(ProgramExpression::Value(int32(flat_index as u32))),
        ),
    }
}

/// The spellings a caller's own contract records for a foreign object's
/// cells, the state that holds the object, and the load term of each cell.
///
/// This is the situation at a call whose callee's precondition reads its own
/// `static` or file-scope array: the caller stated the cells in its own
/// contract, which records the qualified spellings against their kernel
/// pointers, and the emitted requirement then reads the very same cells.
fn recorded_qualified_cells(
    block: &str,
    name: &str,
    cells: i32,
) -> (ExecutionState, SurfacePropositionMap, Vec<MachineTerm>) {
    let state = ExecutionState::new()
        .with_memory(Memory::new().with_block(block, 4 * u32::try_from(cells).unwrap()));
    let base = ProgramValue::typed_pointer(
        Pointer {
            block: PointerBlock::Concrete(block.into()),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramType::Int32Pointer,
    );
    let mut sources = SurfacePropositionMap::default();
    let loads = (0..cells)
        .map(|index| {
            let written = ClickProposition::Comparison {
                left: qualified_cell(name, &base, index),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(5))),
            };
            let lowered = relower_written_proposition(&written, &state)
                .expect("a qualified cell comparison lowers at a state holding the object");
            sources
                .record_lowering(&written, &lowered)
                .expect("the comparison lowers to matching logical structure");
            // The load term as lowering produced it: a registered load
            // variable, one of the two forms an emitted requirement carries.
            let Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: load,
                    right: _,
                },
                _,
            ) = lowered
            else {
                panic!("a qualified cell comparison lowers to one load equality");
            };
            *load
        })
        .collect();
    (state, sources, loads)
}

/// The precondition every `static_array_parity_*`, `static_local_arrays`, and
/// `file_scope_static_arrays` call carries: each cell of the callee's own
/// static array is strictly inside `(-1000, 1000)`, left-nested exactly as
/// the contract's `and` chain lowers.
fn cells_within_bounds(loads: &[MachineTerm]) -> Proposition {
    let clauses = loads.iter().flat_map(|load| {
        [
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: Box::new(load.clone()),
                    right: Box::new(MachineTerm::constant((-1000i32) as u32)),
                },
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(load.clone()),
                    right: Box::new(MachineTerm::constant(1000)),
                },
                true,
            ),
        ]
    });
    clauses
        .reduce(|left, right| Proposition::And(Box::new(left), Box::new(right)))
        .expect("a bounded object has at least one cell")
}

fn synthesized_under_sources(
    proposition: &Proposition,
    sources: &SurfacePropositionMap,
    state: &ExecutionState,
) -> Option<ClickProposition> {
    let _sources = QualifiedSynthesisScope::enter(sources);
    let _budget = SurfaceSynthesisScope::enter();
    synthesize_surface_proposition(proposition, ParameterBinding::default(), state)
}

/// Every qualified name the spelling of a proposition reaches for.
fn qualified_names_in(proposition: &ClickProposition) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let mut propositions = vec![proposition];
    while let Some(proposition) = propositions.pop() {
        match proposition {
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                propositions.push(left);
                propositions.push(right);
            }
            ClickProposition::Comparison { left, right, .. } => {
                for expression in [left, right] {
                    let mut base = expression;
                    while let ContractExpression::Index(inner, _)
                    | ContractExpression::Field { base: inner, .. }
                    | ContractExpression::ArrayIndex { base: inner, .. } = base
                    {
                        base = inner;
                    }
                    if let ContractExpression::QualifiedC { name, .. } = base {
                        names.insert(name.clone());
                    }
                }
            }
            _ => {}
        }
    }
    names
}

/// A call requirement that reads a foreign static or file-scope object's
/// cells is spelled as the qualified indexed objects the caller can already
/// write, and that spelling lowers back to exactly the requirement.
///
/// Package 10(c2) needs this: the planner may only state a requirement in a
/// `have` whose goal equals the requirement, so a spelling that merely looks
/// right is useless. Before this, `record_lowering` indexed only a bare
/// qualified object, so an indexed one left `qualified_load_sources` empty
/// and the requirement had no spelling at all.
///
/// Both forms an emitted requirement carries are covered: the registered
/// load variable lowering produces, and the resolved `MemoryLoad` the
/// prerequisite check names when it resolves loads along the memory
/// derivations. Those two are one cell under the kernel's naming law, and
/// the comparison is made in the registry-resolved form so that a spelling
/// of either is checked against the same cells.
#[test]
fn spelling_validation_cannot_defer_its_debts_to_a_statement_probe() {
    let state = ExecutionState::new().with_local(
        "x",
        ProgramValue::Int32(MachineTerm::Variable(Variable(894321))),
    );
    let candidate = ClickProposition::Comparison {
        left: ContractExpression::Call {
            name: "to_integer".into(),
            arguments: vec![ContractExpression::Add(
                Box::new(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable("x".into()),
                )),
                Box::new(ContractExpression::IntegerLiteral("1".into())),
            )],
        },
        operator: ComparisonOperator::Equal,
        right: ContractExpression::IntegerLiteral("0".into()),
    };
    let proposition = relower_written_proposition(&candidate, &state).unwrap();
    let (accepted, probe) = super::super::execution_planning::probe_open_obligations(|| {
        synthesized_surface_matches_proposition(
            &candidate,
            &proposition,
            ParameterBinding::default(),
            &state,
        )
    });
    assert!(
        !accepted,
        "a spelling check must refuse its own unproved arithmetic domain"
    );
    assert!(
        probe.recorded.is_empty(),
        "a presentation check must not add execution debts"
    );
}

#[test]
fn qualified_static_read_spellings_retain_entry_and_current_epochs() {
    let _session = crate::kernel::VerificationSession::enter();
    let (entry, sources, loads) =
        recorded_qualified_cells("file-static:alpha.c:calls", "alpha::calls", 1);
    let address = Pointer {
        block: PointerBlock::Concrete("file-static:alpha.c:calls".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let post = entry
        .clone()
        .with_memory(entry.memory().clone().store(address.clone(), int32(7)));
    let current = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_memory_ref(post.memory()),
        address,
        crate::kernel::LoadKind::Int32,
    );
    let named = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(current.clone()),
            right: Box::new(loads[0].clone()),
        },
        true,
    );
    let resolve = crate::kernel::resolve_load_variables_from_registry;
    let shared = Proposition::ConditionIs(
        ConditionTerm::integer_equal(
            crate::kernel::IntegerTerm::from_machine(MachineIntegerType::Int32, current).unwrap(),
            crate::kernel::IntegerTerm::add(
                crate::kernel::IntegerTerm::from_machine(
                    MachineIntegerType::Int32,
                    loads[0].clone(),
                )
                .unwrap(),
                crate::kernel::IntegerTerm::constant_i64(1),
            ),
        ),
        true,
    );
    let _sources = QualifiedSynthesisScope::enter(&sources);
    for goal in [named.clone(), resolve(&named), shared] {
        let spelled = synthesize_surface_proposition_at_entry_and_post(
            &goal,
            ParameterBinding::default(),
            &entry,
            &post,
        )
        .expect("qualified static reads keep the selected epochs");
        assert!(format!("{spelled:?}").contains("Old("), "{spelled:?}");
        let lowered = relower_written_proposition_with_states(
            &spelled,
            &entry,
            &post,
            &RecordedStates::new(),
        )
        .unwrap();
        assert_eq!(resolve(&lowered), resolve(&goal), "{spelled:?}");
    }
}

#[test]
fn foreign_static_cell_requirements_round_trip_through_their_qualified_spelling() {
    let (state, sources, loads) = recorded_qualified_cells(
        "static:increment_twice:values#static0",
        "static_local::increment_twice::values",
        3,
    );
    let requirement = cells_within_bounds(&loads);
    let resolve = crate::kernel::resolve_load_variables_from_registry;
    for requirement in [requirement.clone(), resolve(&requirement)] {
        let spelled = synthesized_under_sources(&requirement, &sources, &state)
            .expect("the requirement must be spellable");
        assert_eq!(
            relower_written_proposition(&spelled, &state)
                .as_ref()
                .map(resolve),
            Ok(resolve(&requirement)),
            "the spelling must lower back to exactly the requirement"
        );

        // The spelling is the caller's own qualified path, not a raw cell
        // address the language cannot write.
        assert_eq!(
            qualified_names_in(&spelled),
            BTreeSet::from(["static_local::increment_twice::values".to_string()]),
            "unexpected spelling {spelled:?}"
        );

        // Without the recorded spelling there is no qualified path to use,
        // so this is the index doing the work, not an accident of the state.
        let unrecorded =
            synthesized_under_sources(&requirement, &SurfacePropositionMap::default(), &state);
        assert!(
            unrecorded.map(|surface| relower_written_proposition(&surface, &state)
                .as_ref()
                .map(resolve)
                == Ok(resolve(&requirement)))
                != Some(true),
            "the qualified index must be what makes this spellable"
        );
    }
}

#[test]
fn qualified_multidimensional_cell_recovery_preserves_its_source_rank() {
    let block = "static:increment_twice:values#static0";
    let state = ExecutionState::new().with_memory(Memory::new().with_block(block, 12));
    let base = ProgramValue::typed_pointer(
        Pointer {
            block: PointerBlock::Concrete(block.into()),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramType::Int32Pointer,
    );
    let surface = ClickProposition::Comparison {
        left: qualified_multidimensional_cell(
            "static_local::increment_twice::values",
            &base,
            0,
            2,
            3,
        ),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(5))),
    };
    let lowered = relower_written_proposition(&surface, &state)
        .expect("a qualified multidimensional cell comparison lowers");
    let mut sources = SurfacePropositionMap::default();
    sources
        .record_lowering(&surface, &lowered)
        .expect("the multidimensional source spelling records");
    let spelled = synthesized_under_sources(&lowered, &sources, &state)
        .expect("the recorded multidimensional spelling is recoverable");
    assert!(matches!(
        spelled,
        ClickProposition::Comparison {
            left: ContractExpression::ArrayIndex { .. },
            ..
        }
    ));
    assert_eq!(
        relower_written_proposition(&spelled, &state),
        Ok(lowered),
        "the recovered spelling must lower to the exact cell"
    );
}

#[test]
fn multidimensional_array_definedness_tracks_local_roots_and_indexes() {
    let lowered = ProgramExpression::Index(
        Box::new(ProgramExpression::Variable("grid".into())),
        Box::new(ProgramExpression::Variable("column".into())),
    );
    let local = ContractExpression::ArrayIndex {
        base: Box::new(ContractExpression::ProgramExpression(
            ProgramExpression::Variable("grid".into()),
        )),
        indexes: vec![ContractExpression::ProgramExpression(
            ProgramExpression::Variable("row".into()),
        )],
        dimensions: vec![1],
        lowered: lowered.clone(),
    };
    assert!(contract_expression_mentions_program_local(
        &local,
        &BTreeSet::from(["grid", "column"]),
    ));
    assert!(contract_expression_mentions_program_local(
        &local,
        &BTreeSet::from(["row", "column"]),
    ));

    let qualified = ContractExpression::ArrayIndex {
        base: Box::new(ContractExpression::QualifiedC {
            name: "static_local::f::grid".into(),
            lowered: ProgramExpression::Value(int32(0)),
        }),
        indexes: vec![ContractExpression::ProgramExpression(
            ProgramExpression::Value(int32(0)),
        )],
        dimensions: vec![1],
        lowered: ProgramExpression::Index(
            Box::new(ProgramExpression::Variable("global_grid".into())),
            Box::new(ProgramExpression::Value(int32(0))),
        ),
    };
    assert!(!contract_expression_mentions_program_local(
        &qualified,
        &BTreeSet::new(),
    ));
}

/// One fixture's call requirement over a foreign object: spellable as that
/// object's qualified cells, and re-lowering to the same cells.
fn assert_foreign_object_requirement_is_spellable(block: &str, name: &str, cells: i32) {
    let (state, sources, loads) = recorded_qualified_cells(block, name, cells);
    let requirement = cells_within_bounds(&loads);
    let resolve = crate::kernel::resolve_load_variables_from_registry;
    let spelled = synthesized_under_sources(&requirement, &sources, &state)
        .unwrap_or_else(|| panic!("`{name}`: the call requirement must be spellable"));
    assert_eq!(
        qualified_names_in(&spelled),
        BTreeSet::from([name.to_string()]),
        "`{name}`: unexpected spelling {spelled:?}"
    );
    assert_eq!(
        relower_written_proposition(&spelled, &state)
            .as_ref()
            .map(resolve),
        Ok(resolve(&requirement)),
        "`{name}`: the spelling must lower back to the requirement"
    );
}

/// `file_scope_static_arrays` calls `alpha` and `beta`, each bounding the
/// two cells of its own translation unit's `static int32 values[2]`. Two
/// same-named file-scope objects stay separate spellings.
#[test]
fn file_scope_static_array_call_requirements_are_spellable() {
    assert_foreign_object_requirement_is_spellable(
        "global:values#file-static:alpha.c",
        "alpha_file::values",
        2,
    );
    assert_foreign_object_requirement_is_spellable(
        "global:values#file-static:beta.c",
        "beta_file::values",
        2,
    );
}

/// The caller of `forall_loadable_range.c`: `range_probe(uint8 bytes[],
/// int32 len)`, its byte pointer an external argument and its length
/// symbolic, exactly as the fixture reaches the call.
fn external_byte_range_caller() -> (
    Vec<crate::languages::interface::ImportedParameter>,
    Vec<ProgramExpression>,
    ExecutionState,
) {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(100_000)), 1),
    };
    let pointer = ProgramValue::typed_pointer(pointer, ProgramType::UInt8Pointer);
    let length = ProgramValue::Int32(MachineTerm::Variable(Variable(1)));
    let parameters = vec![
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::UInt8Pointer,
            "bytes".to_string(),
            None,
        ),
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32,
            "len".to_string(),
            None,
        ),
    ];
    let arguments = vec![
        ProgramExpression::Value(pointer.clone()),
        ProgramExpression::Value(length.clone()),
    ];
    let state = ExecutionState::new()
        .with_local("bytes", pointer)
        .with_local("len", length);
    (parameters, arguments, state)
}

#[test]
fn exact_external_zero_based_byte_range_round_trips_symbolic_end() {
    let (parameters, arguments, state) = external_byte_range_caller();
    let requirement = Proposition::MemoryLoadable {
        memory: state.memory().clone(),
        base: match &arguments[0] {
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.pointer().clone(),
            _ => unreachable!(),
        },
        bytes: MachineTerm::add(MachineTerm::Variable(Variable(1)), MachineTerm::constant(1)),
        wide: false,
    };
    let synthesized = synthesize_source_projection_proposition_with_bound_variable_names(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
        &BTreeMap::new(),
    )
    .expect("the exact external byte range must be spellable");
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement must remain one viewability: {synthesized:?}");
    };
    assert_eq!(segment.base, ProgramExpression::Variable("bytes".into()));
    assert_eq!(segment.start, ProgramExpression::Value(int32(0)));
    assert_eq!(
        segment.end,
        ProgramExpression::Add(
            Box::new(ProgramExpression::Variable("len".into())),
            Box::new(ProgramExpression::Value(int32(1))),
        )
    );
    assert_eq!(
        relower_written_proposition(&synthesized, &state),
        Ok(requirement)
    );
}

#[test]
fn exact_external_zero_based_byte_range_resolves_direct_variable_argument() {
    let (parameters, mut arguments, state) = external_byte_range_caller();
    let base = match &arguments[0] {
        ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.pointer().clone(),
        _ => unreachable!(),
    };
    arguments[0] = ProgramExpression::Variable("bytes".into());
    let requirement = Proposition::MemoryLoadable {
        memory: state.memory().clone(),
        base,
        bytes: MachineTerm::add(MachineTerm::Variable(Variable(1)), MachineTerm::constant(1)),
        wide: false,
    };
    let synthesized = synthesize_source_projection_proposition_with_bound_variable_names(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
        &BTreeMap::new(),
    )
    .expect("the exact named local argument must resolve to its declared byte parameter");
    let ClickProposition::Loadable { segment } = synthesized else {
        panic!("the requirement must remain one viewability");
    };
    assert_eq!(segment.base, ProgramExpression::Variable("bytes".into()));
}

#[test]
fn exact_external_zero_based_byte_range_rejects_ambiguous_alias() {
    let (mut parameters, mut arguments, state) = external_byte_range_caller();
    parameters.push(crate::languages::interface::ImportedParameter::new(
        InterfaceType::UInt8Pointer,
        "alias".to_string(),
        None,
    ));
    arguments.push(arguments[0].clone());
    let requirement = Proposition::MemoryLoadable {
        memory: state.memory().clone(),
        base: match &arguments[0] {
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.pointer().clone(),
            _ => unreachable!(),
        },
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    assert!(
        synthesize_source_projection_proposition_with_bound_variable_names(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state,
            &BTreeMap::new(),
        )
        .is_none(),
        "an exact aliased pointer must not select one source spelling by position"
    );
}

/// The `forall_loadable_range` call requirement as the kernel emits it:
/// every in-range byte of an external-argument pointer is loadable, its byte
/// count left as the written `(k + 1) - k`.
fn external_byte_range_requirement(binder: Variable, length: &MachineTerm) -> Proposition {
    let index = MachineTerm::Variable(binder);
    Proposition::ForAll {
        name: Default::default(),
        var: binder,
        sort: Sort::ProgramInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: Box::new(MachineTerm::constant(0)),
                        right: Box::new(index.clone()),
                    },
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(index.clone()),
                        right: Box::new(length.clone()),
                    },
                    true,
                )),
            )),
            Box::new(Proposition::MemoryLoadable {
                memory: Memory::new(),
                base: Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Add(
                        Box::new(PointerOffsetTerm::scaled_int32_node(
                            MachineTerm::Variable(Variable(100_000)),
                            1,
                        )),
                        Box::new(PointerOffsetTerm::scaled_int32_node(index.clone(), 1)),
                    ),
                },
                bytes: binary_node!(
                    Int32,
                    Subtract,
                    Box::new(binary_node!(
                        Int32,
                        Add,
                        Box::new(index.clone()),
                        Box::new(MachineTerm::constant(1)),
                    )),
                    Box::new(index),
                ),
                wide: false,
            }),
        )),
    }
}

fn external_symbolic_element_context(
    memory: Memory,
) -> (
    Vec<crate::languages::interface::ImportedParameter>,
    Vec<ProgramExpression>,
    ExecutionState,
) {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(100_000)), 1),
    };
    let pointer = ProgramValue::typed_pointer(pointer, ProgramType::UInt8Pointer);
    let index = ProgramValue::Int32(MachineTerm::Variable(Variable(100_001)));
    let parameters = vec![
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::UInt8Pointer,
            "bytes".to_string(),
            None,
        ),
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32,
            "index".to_string(),
            None,
        ),
    ];
    let arguments = vec![
        ProgramExpression::Value(pointer.clone()),
        ProgramExpression::Value(index.clone()),
    ];
    let state = ExecutionState::new()
        .with_memory(memory)
        .with_local("bytes", pointer)
        .with_local("index", index);
    (parameters, arguments, state)
}

fn external_symbolic_element_requirement(memory: Memory, index: Variable) -> Proposition {
    external_symbolic_element_requirement_term(memory, MachineTerm::Variable(index))
}

fn external_symbolic_element_requirement_term(memory: Memory, index: MachineTerm) -> Proposition {
    Proposition::MemoryLoadable {
        memory,
        base: Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::scaled_int32_node(
                    MachineTerm::Variable(Variable(100_000)),
                    1,
                )),
                Box::new(PointerOffsetTerm::scaled_int32_node(index.clone(), 1)),
            ),
        },
        bytes: binary_node!(
            Int32,
            Subtract,
            Box::new(binary_node!(
                Int32,
                Add,
                Box::new(index.clone()),
                Box::new(MachineTerm::constant(1)),
            )),
            Box::new(index),
        ),
        wide: false,
    }
}

fn external_symbolic_element_constant_byte_requirement(
    memory: Memory,
    index: Variable,
) -> Proposition {
    let mut requirement = external_symbolic_element_requirement(memory, index);
    let Proposition::MemoryLoadable { bytes, .. } = &mut requirement else {
        unreachable!();
    };
    *bytes = MachineTerm::constant(1);
    requirement
}

/// The unresolved `strlen` carrier: an existential length whose successor is
/// defined, followed by a guarded universal one-byte loadability range. The
/// caller's outer `loadable(bytes[0..len + 1])` fact is a separate premise;
/// this regression targets the quantified `k` carrier that retains `1`.
fn full_external_guarded_range_surface() -> ClickProposition {
    let length =
        ContractExpression::ProgramExpression(ProgramExpression::Variable("__click_q0".into()));
    let index =
        ContractExpression::ProgramExpression(ProgramExpression::Variable("__click_q1".into()));
    let quantified_range = ClickProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: ProgramExpression::Variable("bytes".into()),
            start: ProgramExpression::Variable("__click_q1".into()),
            end: ProgramExpression::Add(
                Box::new(ProgramExpression::Variable("__click_q1".into())),
                Box::new(ProgramExpression::Value(int32(1))),
            ),
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    "bytes".into(),
                )),
                start: index.clone(),
                end: ContractExpression::Add(
                    Box::new(index.clone()),
                    Box::new(ContractExpression::ProgramExpression(
                        ProgramExpression::Value(int32(1)),
                    )),
                ),
            },
        },
    };
    let all_before_loadable = ClickProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "__click_q1".into(),
        written_name: None,
        body: Box::new(ClickProposition::Implies(
            Box::new(ClickProposition::And(
                Box::new(ClickProposition::Comparison {
                    left: index.clone(),
                    operator: ComparisonOperator::GreaterEqual,
                    right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(
                        0,
                    ))),
                }),
                Box::new(ClickProposition::Comparison {
                    left: index.clone(),
                    operator: ComparisonOperator::LessThan,
                    right: length.clone(),
                }),
            )),
            Box::new(quantified_range),
        )),
    };
    ClickProposition::Exists {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: "__click_q0".into(),
        written_name: None,
        body: Box::new(ClickProposition::And(
            Box::new(ClickProposition::Defined {
                expression: ContractExpression::ProgramExpression(ProgramExpression::Add(
                    Box::new(ProgramExpression::Variable("__click_q0".into())),
                    Box::new(ProgramExpression::Value(int32(1))),
                )),
            }),
            Box::new(all_before_loadable),
        )),
    }
}

fn replace_full_external_cstr_range_with_constant_byte_count(requirement: &mut Proposition) {
    fn replace(proposition: &mut Proposition, inside_forall: bool) -> bool {
        match proposition {
            Proposition::MemoryLoadable { bytes, .. } if inside_forall => {
                *bytes = MachineTerm::constant(1);
                true
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                replace(left, inside_forall) || replace(right, inside_forall)
            }
            Proposition::Not(body) | Proposition::Exists { body, .. } => {
                replace(body, inside_forall)
            }
            Proposition::ForAll { body, .. } => replace(body, true),
            _ => false,
        }
    }
    assert!(
        replace(requirement, false),
        "the strlen requirement must contain a quantified range"
    );
}

#[test]
fn full_guarded_requirement_with_variable_argument_round_trips() {
    let memory = Memory::new().with_block("strlen:production-bytes", 16);
    let (parameters, concrete_arguments, state) = external_symbolic_element_context(memory.clone());
    let pointer = match &concrete_arguments[0] {
        ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.clone(),
        _ => panic!("the production-shaped argument must be a pointer"),
    };
    let arguments = vec![
        ProgramExpression::Variable("bytes".to_string()),
        concrete_arguments[1].clone(),
    ];
    let requirement_surface = full_external_guarded_range_surface();
    let requirement = relower_written_proposition(&requirement_surface, &state)
        .expect("the production-shaped strlen requirement must lower");
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state,
        )
        .expect("the guarded strlen requirement must be spellable")
    };
    assert!(matches!(synthesized, ClickProposition::Exists { .. }));
    let lowered = relower_written_proposition(&synthesized, &state)
        .expect("the synthesized existential must lower through the have path");
    let resolve = crate::kernel::resolve_load_variables_from_registry;
    assert!(
        crate::kernel::proof::propositions_are_alpha_equal(
            &resolve(&lowered),
            &resolve(&requirement)
        ),
        "lowered: {lowered:?}\nrequirement: {requirement:?}"
    );
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&resolve(&lowered)),
        crate::kernel::proof::proposition_identity_key(&resolve(&requirement)),
        "the variable argument must preserve canonical load identity"
    );
    assert_eq!(
        state.locals().get_native("bytes").as_deref(),
        Some(&ProgramValue::Pointer(pointer))
    );
}

#[test]
fn full_guarded_constant_byte_requirement_with_variable_argument_round_trips() {
    let memory = Memory::new().with_block("strlen:production-constant-bytes", 16);
    let (parameters, concrete_arguments, state) = external_symbolic_element_context(memory.clone());
    let pointer = match &concrete_arguments[0] {
        ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.clone(),
        _ => panic!("the production-shaped argument must be a pointer"),
    };
    let arguments = vec![
        ProgramExpression::Variable("bytes".to_string()),
        concrete_arguments[1].clone(),
    ];
    let requirement_surface = full_external_guarded_range_surface();
    let mut requirement = relower_written_proposition(&requirement_surface, &state)
        .expect("the production-shaped strlen requirement must lower");
    replace_full_external_cstr_range_with_constant_byte_count(&mut requirement);
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state,
        )
        .expect("the guarded constant-byte strlen requirement must be spellable")
    };
    assert!(matches!(synthesized, ClickProposition::Exists { .. }));
    let lowered = relower_written_proposition(&synthesized, &state)
        .expect("the synthesized existential must lower through the have path");
    let resolve = crate::kernel::resolve_load_variables_from_registry;
    assert!(
        crate::kernel::proof::propositions_are_alpha_equal(
            &resolve(&lowered),
            &resolve(&requirement)
        ),
        "lowered: {lowered:?}\nrequirement: {requirement:?}"
    );
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&resolve(&lowered)),
        crate::kernel::proof::proposition_identity_key(&resolve(&requirement)),
        "the variable argument must preserve canonical load identity"
    );
    assert_eq!(
        state.locals().get_native("bytes").as_deref(),
        Some(&ProgramValue::Pointer(pointer))
    );
}

#[test]
fn strlen_symbolic_element_range_round_trips_exactly() {
    let memory = Memory::new().with_block("strlen:bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let requirement = external_symbolic_element_requirement(memory, Variable(100_001));
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state,
        )
        .expect("strlen's reduced one-element range must be spellable")
    };
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement must remain one viewability: {synthesized:?}");
    };
    assert_eq!(segment.base, ProgramExpression::Variable("bytes".into()));
    assert_eq!(segment.start, ProgramExpression::Variable("index".into()));
    assert_eq!(
        segment.end,
        ProgramExpression::Add(
            Box::new(ProgramExpression::Variable("index".into())),
            Box::new(ProgramExpression::Value(int32(1))),
        )
    );
    let lowered = relower_written_proposition(&synthesized, &state)
        .expect("the synthesized range must lower through the have path");
    assert_eq!(lowered, requirement);
}

#[test]
fn strlen_symbolic_element_constant_byte_range_round_trips_exactly() {
    let memory = Memory::new().with_block("strlen:constant-symbolic-bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let requirement =
        external_symbolic_element_constant_byte_requirement(memory, Variable(100_001));
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state,
        )
        .expect("a constant one-byte symbolic range must be spellable")
    };
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement must remain one viewability: {synthesized:?}");
    };
    assert_eq!(
        segment.base,
        ProgramExpression::Add(
            Box::new(ProgramExpression::Variable("bytes".into())),
            Box::new(ProgramExpression::Variable("index".into())),
        )
    );
    assert_eq!(segment.start, ProgramExpression::Value(int32(0)));
    assert_eq!(segment.end, ProgramExpression::Value(int32(1)));
    assert_eq!(
        relower_written_proposition(&synthesized, &state),
        Ok(requirement)
    );
}

#[test]
fn strlen_symbolic_element_range_rejects_wrong_identity() {
    let memory = Memory::new().with_block("strlen:bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());

    let wrong_base = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::scaled_int32_node(
                    MachineTerm::Variable(Variable(100_002)),
                    1,
                )),
                Box::new(PointerOffsetTerm::scaled_int32_node(
                    MachineTerm::Variable(Variable(100_001)),
                    1,
                )),
            ),
        },
        bytes: binary_node!(
            Int32,
            Subtract,
            Box::new(binary_node!(
                Int32,
                Add,
                Box::new(MachineTerm::Variable(Variable(100_001))),
                Box::new(MachineTerm::constant(1)),
            )),
            Box::new(MachineTerm::Variable(Variable(100_001))),
        ),
        wide: false,
    };
    assert!(
        synthesize_surface_proposition(
            &wrong_base,
            ParameterBinding::new(&parameters, &arguments),
            &state
        )
        .is_none()
    );

    let wrong_index = external_symbolic_element_requirement(memory.clone(), Variable(100_002));
    assert!(
        synthesize_surface_proposition(
            &wrong_index,
            ParameterBinding::new(&parameters, &arguments),
            &state
        )
        .is_none(),
        "an index with no source binding must not be inferred from the ambient state"
    );

    let wrong_width = {
        let mut requirement =
            external_symbolic_element_requirement(memory.clone(), Variable(100_001));
        let Proposition::MemoryLoadable { base, .. } = &mut requirement else {
            unreachable!();
        };
        base.offset = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::scaled_int32_node(
                MachineTerm::Variable(Variable(100_000)),
                2,
            )),
            Box::new(PointerOffsetTerm::scaled_int32_node(
                MachineTerm::Variable(Variable(100_001)),
                2,
            )),
        );
        requirement
    };
    assert!(
        synthesize_surface_proposition(
            &wrong_width,
            ParameterBinding::new(&parameters, &arguments),
            &state
        )
        .is_none(),
        "the element width must be the declared one-byte parameter width"
    );

    let ambient_only = external_symbolic_element_requirement(memory, Variable(100_001));
    assert!(
        synthesize_surface_proposition(&ambient_only, ParameterBinding::default(), &state)
            .is_none(),
        "a local pointer must not substitute for the producer's external parameter"
    );
}

#[test]
fn strlen_constant_element_range_falls_back_to_general_synthesis() {
    let memory = Memory::new().with_block("strlen:constant-bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let requirement = external_symbolic_element_requirement_term(memory, MachineTerm::constant(3));
    let synthesized = synthesize_surface_proposition(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
    )
    .expect("a constant reduced element must retain the historical range fallback");
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement must remain one viewability: {synthesized:?}");
    };
    assert_eq!(segment.base, ProgramExpression::Variable("bytes".into()));
    assert_eq!(segment.start, ProgramExpression::Value(int32(3)));
    assert_eq!(segment.end, ProgramExpression::Value(int32(4)));
    let lowered = relower_written_proposition(&synthesized, &state)
        .expect("the historical fallback must still lower the constant range");
    let Proposition::MemoryLoadable { base, bytes, .. } = lowered else {
        panic!("the lowered fallback must remain one viewability");
    };
    assert_eq!(bytes, MachineTerm::constant(1));
    assert_eq!(
        base.offset,
        PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::scaled_int32_node(
                MachineTerm::Variable(Variable(100_000)),
                1
            )),
            Box::new(PointerOffsetTerm::Constant(3)),
        )
    );
}

#[test]
fn strlen_zero_based_element_range_round_trips_exactly() {
    let memory = Memory::new().with_block("strlen:zero-based-bytes", 16);
    let (parameters, mut arguments, state) = external_symbolic_element_context(memory.clone());
    let pointer = ProgramValue::typed_pointer(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramType::UInt8Pointer,
    );
    arguments[0] = ProgramExpression::Value(pointer.clone());
    let state = state.with_local("bytes", pointer);
    let mut requirement = external_symbolic_element_requirement(memory, Variable(100_001));
    let Proposition::MemoryLoadable { base, .. } = &mut requirement else {
        unreachable!();
    };
    base.offset = PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(100_001)), 1);
    let synthesized = synthesize_surface_proposition(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
    )
    .expect("the canonical zero-based strlen element must be spellable");
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement must remain one viewability: {synthesized:?}");
    };
    assert_eq!(segment.base, ProgramExpression::Variable("bytes".into()));
    assert_eq!(segment.start, ProgramExpression::Variable("index".into()));
    assert_eq!(
        segment.end,
        ProgramExpression::Add(
            Box::new(ProgramExpression::Variable("index".into())),
            Box::new(ProgramExpression::Value(int32(1))),
        )
    );
    assert_eq!(
        relower_written_proposition(&synthesized, &state),
        Ok(requirement)
    );
}

#[test]
fn non_external_named_range_still_uses_general_synthesis() {
    let memory = Memory::new().with_block("local:elements", 8);
    let pointer = ProgramValue::typed_pointer(
        Pointer {
            block: PointerBlock::Concrete("local:elements".into()),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramType::UInt8Pointer,
    );
    let start = ProgramValue::Int32(MachineTerm::Variable(Variable(100_001)));
    let state = ExecutionState::new()
        .with_memory(memory.clone())
        .with_local("elements", pointer)
        .with_local("start", start);
    let requirement = Proposition::MemoryLoadable {
        memory,
        base: Pointer {
            block: PointerBlock::Concrete("local:elements".into()),
            offset: PointerOffsetTerm::scaled_int32_node(
                MachineTerm::Variable(Variable(100_001)),
                1,
            ),
        },
        bytes: binary_node!(
            Int32,
            Subtract,
            Box::new(binary_node!(
                Int32,
                Add,
                Box::new(MachineTerm::Variable(Variable(100_001))),
                Box::new(MachineTerm::constant(1)),
            )),
            Box::new(MachineTerm::Variable(Variable(100_001))),
        ),
        wide: false,
    };
    let synthesized =
        synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
            .expect("the general named-range path must remain available for local pointers");
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement should remain one viewability: {synthesized:?}");
    };
    assert_eq!(segment.base, ProgramExpression::Variable("elements".into()));
    assert_eq!(segment.start, ProgramExpression::Variable("start".into()));
    assert_eq!(
        segment.end,
        ProgramExpression::Add(
            Box::new(ProgramExpression::Variable("start".into())),
            Box::new(ProgramExpression::Value(int32(1))),
        )
    );
    let lowered = relower_written_proposition(&synthesized, &state)
        .expect("the local named range must lower through the existing path");
    assert_eq!(lowered, requirement);
}

#[test]
fn strlen_quantified_element_range_requirement_round_trips() {
    let memory = Memory::new().with_block("strlen:quantified-bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let binder = Variable(100_002);
    let requirement = Proposition::ForAll {
        name: Default::default(),
        var: binder,
        sort: Sort::ProgramInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: Box::new(MachineTerm::Variable(binder)),
                        right: Box::new(MachineTerm::constant(0)),
                    },
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(MachineTerm::Variable(binder)),
                        right: Box::new(MachineTerm::Variable(Variable(100_001))),
                    },
                    true,
                )),
            )),
            Box::new(external_symbolic_element_requirement(memory, binder)),
        )),
    };
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state,
        )
        .expect("strlen's quantified one-element range must be spellable")
    };
    let lowered = relower_written_proposition(&synthesized, &state)
        .expect("the quantified range must lower through the have path");
    assert!(
        crate::kernel::proof::propositions_are_alpha_equal(&lowered, &requirement),
        "quantified strlen spelling changed its proposition:\n  lowered: {lowered:?}\n  requirement: {requirement:?}"
    );
}

fn external_element_range_context(
    parameter_type: crate::languages::interface::InterfaceType,
    pointer_type: ProgramType,
    width: u32,
) -> (
    Vec<crate::languages::interface::ImportedParameter>,
    Vec<ProgramExpression>,
    ExecutionState,
) {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(
            MachineTerm::Variable(Variable(100_000)),
            i64::from(width),
        ),
    };
    let pointer = ProgramValue::typed_pointer(pointer, pointer_type);
    let parameters = vec![crate::languages::interface::ImportedParameter::new(
        parameter_type,
        "elements".to_string(),
        None,
    )]
    .into_iter()
    .chain([
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32,
            "start".to_string(),
            None,
        ),
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32,
            "end".to_string(),
            None,
        ),
    ])
    .collect();
    let arguments = vec![
        ProgramExpression::Value(pointer.clone()),
        ProgramExpression::Value(ProgramValue::Int32(MachineTerm::Variable(Variable(
            100_001,
        )))),
        ProgramExpression::Value(ProgramValue::Int32(MachineTerm::Variable(Variable(
            100_002,
        )))),
    ];
    let state = ExecutionState::new()
        .with_local("elements", pointer)
        .with_local(
            "start",
            ProgramValue::Int32(MachineTerm::Variable(Variable(100_001))),
        )
        .with_local(
            "end",
            ProgramValue::Int32(MachineTerm::Variable(Variable(100_002))),
        );
    (parameters, arguments, state)
}

fn external_element_range_requirement(
    width: u32,
    start: MachineTerm,
    end: MachineTerm,
) -> Proposition {
    Proposition::MemoryLoadable {
        memory: Memory::new(),
        base: Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::scaled_int32_node(
                    MachineTerm::Variable(Variable(100_000)),
                    i64::from(width),
                )),
                Box::new(PointerOffsetTerm::scaled_int32_node(
                    start.clone(),
                    i64::from(width),
                )),
            ),
        },
        bytes: binary_node!(
            Int32,
            Multiply,
            Box::new(binary_node!(
                Int32,
                Subtract,
                Box::new(end),
                Box::new(start)
            )),
            Box::new(MachineTerm::constant(width)),
        ),
        wide: false,
    }
}

/// A `loadable` range over an external argument is spelled as the
/// `loadable(p[a..b])` range form over the caller's own pointer name, and
/// that spelling lowers back to exactly the requirement.
///
/// The zero-based form cannot state this one: folding the start index into
/// the base loses the written ends, and the byte count `(k + 1) - k` the
/// requirement carries is not the `1` a zero-based range re-lowers to.
///
/// Re-lowering allocates its own quantifier variable, as any fresh `have`
/// does, so the goal is compared under the binder that lowering chose. Every
/// other part of the proposition, including the unfolded byte count, must be
/// identical.
#[test]
fn external_argument_range_loadability_round_trips_through_the_range_form() {
    let (parameters, arguments, state) = external_byte_range_caller();
    let length = MachineTerm::Variable(Variable(1));
    let requirement = external_byte_range_requirement(Variable(3_100_000), &length);
    let spelled = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state,
        )
        .expect("a range over an external argument must be spellable")
    };

    // The spelling is the written range form over the parameter's own name,
    // not a zero-based range over a displaced base.
    let ClickProposition::ForAll { body, .. } = &spelled else {
        panic!("the requirement is one universal: {spelled:?}");
    };
    let ClickProposition::Implies(_, consequent) = body.as_ref() else {
        panic!("the universal's body is one implication: {spelled:?}");
    };
    let ClickProposition::Loadable { segment } = consequent.as_ref() else {
        panic!("the consequent is one viewability: {spelled:?}");
    };
    assert_eq!(segment.base, ProgramExpression::Variable("bytes".into()));
    assert_ne!(segment.start, ProgramExpression::Value(int32(0)));

    let lowered = relower_written_proposition(&spelled, &state)
        .expect("the synthesized range lowers at the calling state");
    let Proposition::ForAll { var, .. } = &lowered else {
        panic!("re-lowering keeps the universal: {lowered:?}");
    };
    assert_eq!(lowered, external_byte_range_requirement(*var, &length));
}

#[test]
fn quantified_loadability_uses_saved_state() {
    let (parameters, arguments, retained_state) = external_byte_range_caller();
    let length = MachineTerm::Variable(Variable(1));
    let requirement = external_byte_range_requirement(Variable(3_100_000), &length);
    let post = retained_state.clone().with_memory(
        retained_state
            .memory()
            .clone()
            .with_block("later-unrelated-write", 1),
    );
    let selector = ProgramPointSelector::Mark("quantified_viewability_head".into());
    let spelled = synthesize_surface_proposition_at_entry_post_and_state(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &post,
        &post,
        Some((&retained_state, &selector)),
    )
    .expect("the quantified loadability goal must retain its saved state");

    let ClickProposition::ForAll { body, .. } = &spelled else {
        panic!("the saved requirement is one universal: {spelled:?}");
    };
    let ClickProposition::Implies(_, consequent) = body.as_ref() else {
        panic!("the saved universal has one guarded body: {spelled:?}");
    };
    assert!(
        matches!(
            consequent.as_ref(),
            ClickProposition::At {
                selector: actual,
                proposition,
            } if actual == &selector
                && matches!(proposition.as_ref(), ClickProposition::Loadable { .. })
        ),
        "the loadability leaf must be read at the saved loop state: {spelled:?}"
    );

    let mut retained_states = RecordedStates::new();
    retained_states.insert(selector, retained_state);
    let lowered = relower_written_proposition_with_states(&spelled, &post, &post, &retained_states)
        .expect("the saved quantified spelling must lower at the later state");
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&lowered),
        crate::kernel::proof::proposition_identity_key(&requirement),
    );
}

#[test]
fn named_element_ranges_preserve_nonzero_starts_and_folded_byte_counts() {
    for (parameter_type, pointer_type, width, spelling) in [
        (
            crate::languages::interface::InterfaceType::UInt16Pointer,
            ProgramType::UInt16Pointer,
            2,
            "uint16",
        ),
        (
            crate::languages::interface::InterfaceType::Int32Pointer,
            ProgramType::Int32Pointer,
            4,
            "int32",
        ),
    ] {
        let (parameters, arguments, state) =
            external_element_range_context(parameter_type, pointer_type, width);
        let requirement = external_element_range_requirement(
            width,
            MachineTerm::Variable(Variable(100_001)),
            MachineTerm::Variable(Variable(100_002)),
        );
        let synthesized = {
            let _budget = SurfaceSynthesisScope::enter();
            synthesize_surface_proposition(
                &requirement,
                ParameterBinding::new(&parameters, &arguments),
                &state,
            )
            .expect("a named element range must be spellable")
        };
        let ClickProposition::Loadable { segment } = &synthesized else {
            panic!("the requirement should synthesize as one viewable range: {synthesized:?}");
        };
        assert_eq!(segment.base, ProgramExpression::Variable("elements".into()));
        assert_eq!(segment.start, ProgramExpression::Variable("start".into()));
        assert_eq!(segment.end, ProgramExpression::Variable("end".into()));

        let source = format!(
            "int32 range_{width}({spelling}* elements, int32 start, int32 end) {{ requires viewable(elements[start..end]); ensures result == 0; }}"
        );
        let parsed = crate::surface::parse(&source).expect("the range spelling must parse");
        let Requirement::LoadableSegment { segment } = &parsed.function_blocks()[0].requires()[0]
        else {
            panic!("the parsed requirement should remain a viewable range");
        };
        assert_eq!(
            synthesized,
            ClickProposition::Loadable {
                segment: segment.clone(),
            }
        );
        let lowered = relower_written_proposition(&synthesized, &state)
            .expect("the parsed range spelling must re-lower");
        assert_eq!(lowered, requirement);
    }

    let (parameters, arguments, state) =
        external_element_range_context(InterfaceType::Int32Pointer, ProgramType::Int32Pointer, 4);
    let requirement =
        external_element_range_requirement(4, MachineTerm::constant(3), MachineTerm::constant(8));
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state,
        )
        .expect("a folded byte count must retain its nonzero named range")
    };
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the folded requirement should synthesize as one range");
    };
    assert_eq!(segment.base, ProgramExpression::Variable("elements".into()));
    assert_eq!(segment.start, ProgramExpression::Value(int32(3)));
    assert_eq!(segment.end, ProgramExpression::Value(int32(8)));
    let Proposition::MemoryLoadable { base, bytes, .. } =
        relower_written_proposition(&synthesized, &state)
            .expect("the folded named range must re-lower")
    else {
        panic!("the folded range must remain a memory-viewability requirement");
    };
    assert_eq!(bytes, MachineTerm::constant(20));
    assert_eq!(
        base.offset,
        PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::scaled_int32_node(
                MachineTerm::Variable(Variable(100_000)),
                4
            )),
            Box::new(PointerOffsetTerm::Constant(12)),
        )
    );
}

#[test]
fn named_element_range_does_not_infer_start_from_an_unrelated_index() {
    let (parameters, arguments, state) = external_element_range_context(
        crate::languages::interface::InterfaceType::Int32Pointer,
        ProgramType::Int32Pointer,
        4,
    );
    let mut requirement = external_element_range_requirement(
        4,
        MachineTerm::Variable(Variable(100_001)),
        MachineTerm::Variable(Variable(100_002)),
    );
    let Proposition::MemoryLoadable { base, .. } = &mut requirement else {
        unreachable!();
    };
    base.offset = PointerOffsetTerm::Add(
        Box::new(PointerOffsetTerm::scaled_int32_node(
            MachineTerm::Variable(Variable(100_000)),
            4,
        )),
        Box::new(PointerOffsetTerm::scaled_int32_node(
            MachineTerm::Variable(Variable(100_003)),
            4,
        )),
    );
    let _budget = SurfaceSynthesisScope::enter();
    let synthesized = synthesize_surface_proposition(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
    );
    assert!(
        synthesized.is_none(),
        "a range start must come from the named pointer's exact offset, not an unrelated index: {synthesized:?}"
    );
}

/// `forall_loadable_range` calls `need_cells`, whose precondition ranges
/// over every in-range byte of the caller's own external-argument pointer.
#[test]
fn forall_loadable_range_call_requirement_is_spellable() {
    let (parameters, arguments, state) = external_byte_range_caller();
    let length = MachineTerm::Variable(Variable(1));
    let requirement = external_byte_range_requirement(Variable(3_100_000), &length);
    let _budget = SurfaceSynthesisScope::enter();
    assert!(
        synthesize_surface_proposition(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state
        )
        .is_some(),
        "the call requirement must be spellable"
    );
}

/// `exists_loadable_range` calls `need_cells`, whose precondition wraps the
/// same range in an existential over the length. The witness name and the
/// binder identities a fresh lowering allocates are its own, so only
/// spellability is asserted here; the range shape itself round-trips in the
/// universal test above.
#[test]
fn exists_loadable_range_call_requirement_is_spellable() {
    let (parameters, arguments, state) = external_byte_range_caller();
    let witness = Variable(3_100_000);
    let requirement = Proposition::Exists {
        name: "len".to_string(),
        var: witness,
        sort: Sort::ProgramInt32,
        body: Box::new(external_byte_range_requirement(
            Variable(3_100_001),
            &MachineTerm::Variable(witness),
        )),
    };
    let _budget = SurfaceSynthesisScope::enter();
    let spelled = synthesize_surface_proposition(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
    )
    .expect("the call requirement must be spellable");
    assert!(
        matches!(spelled, ClickProposition::Exists { .. }),
        "the existential is spelled as one: {spelled:?}"
    );
}

#[test]
fn function_call_synthesis_scales_with_named_arguments() {
    let state = ExecutionState::new();
    let mut previous = None;
    for size in [16, 32, 64, 128] {
        let values = vec![crate::kernel::PureFunctionArgument::Value(int32(7)); size];
        let _scope = SurfaceSynthesisScope::enter();
        let call = synthesize_surface_call(
            "selected",
            &values,
            ParameterBinding::default(),
            &state,
            &BTreeMap::new(),
        )
        .unwrap();
        assert!(
            matches!(call, ContractExpression::Call { arguments, .. } if arguments.len() == size)
        );
        let work = SURFACE_SYNTHESIS_BUDGET.with(|budget| {
            SURFACE_SYNTHESIS_WORK_LIMIT - budget.borrow().as_ref().unwrap().remaining_work
        });
        assert!(work >= size);
        if let Some(previous) = previous {
            assert!(work <= previous * 3);
        }
        previous = Some(work);
    }
}

#[test]
fn function_array_synthesis_requires_the_exact_named_state() {
    let pointer = ProgramValue::pointer(Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Constant(0),
    });
    let entry = ExecutionState::new().with_local("p", pointer.clone());
    let post = entry
        .clone()
        .with_memory(Memory::new().with_block("other", 4));
    let values = [crate::kernel::PureFunctionArgument::ArrayRef {
        memory: entry.memory().clone(),
        pointer,
        element_type: ProgramType::Int32,
    }];
    let bindings = BTreeMap::new();
    // An unnamed historical memory cannot be silently printed as current.
    assert!(
        synthesize_surface_call(
            "selected",
            &values,
            ParameterBinding::default(),
            &post,
            &bindings
        )
        .is_none()
    );
    let _entry =
        SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(entry.clone()))));
    let call = synthesize_surface_call(
        "selected",
        &values,
        ParameterBinding::default(),
        &post,
        &bindings,
    )
    .unwrap();
    assert!(
        matches!(&call, ContractExpression::Call { arguments, .. } if matches!(arguments.as_slice(), [ContractExpression::Old(_)]))
    );
    // An unresolved historical pointer re-enters entry-state synthesis. The
    // entry slot must be free for that nested scope to clear and restore it.
    let unnamed = [crate::kernel::PureFunctionArgument::ArrayRef {
        memory: entry.memory().clone(),
        pointer: ProgramValue::pointer(Pointer::symbolic(Variable(9_830_001))),
        element_type: ProgramType::Int32,
    }];
    assert!(
        synthesize_surface_call(
            "selected",
            &unnamed,
            ParameterBinding::default(),
            &post,
            &bindings,
        )
        .is_none()
    );
    assert_eq!(
        synthesize_surface_call(
            "selected",
            &values,
            ParameterBinding::default(),
            &post,
            &bindings,
        ),
        Some(call)
    );
}

#[test]
fn function_array_argument_keeps_its_recorded_memory_after_other_writes() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = ProgramValue::pointer(Pointer::symbolic(Variable(981_300)));
    let historical = ExecutionState::new()
        .with_local("p", pointer.clone())
        .with_memory(Memory::new().with_block("historical-array", 4));
    let current = historical
        .clone()
        .with_memory(historical.memory().clone().with_block("later-write", 4));
    let values = [crate::kernel::PureFunctionArgument::ArrayRef {
        memory: historical.memory().clone(),
        pointer,
        element_type: ProgramType::Int32,
    }];
    let selector = ProgramPointSelector::from(ProgramPointRef {
        region: CodeRegionRef::Region(0),
        kind: ProgramPointKind::Exit,
    });
    let mut points = RecordedStates::new();
    points.insert(selector.clone(), historical);
    let _points = SynthesisRecordedPointsScope::enter(&points);
    let _entry =
        SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(current.clone()))));
    let call = synthesize_surface_call(
        "selected",
        &values,
        ParameterBinding::default(),
        &current,
        &BTreeMap::new(),
    )
    .expect("an explicitly recorded memory has a source selector");
    let SurfaceTerm::Call { arguments, .. } = call else {
        panic!("call")
    };
    assert!(
        matches!(&arguments[0], SurfaceTerm::At { selector: selected, expression }
        if *selected == selector && matches!(expression.as_ref(), SurfaceTerm::ProgramExpression(ProgramExpression::Variable(name)) if name == "p"))
    );
}

#[test]
fn nested_propositions_synthesize_with_small_frames_and_linear_work() {
    std::thread::Builder::new()
        .name("small-stack-proposition-synthesis".into())
        .stack_size(1024 * 1024)
        .spawn(|| {
            let state = ExecutionState::new();
            let atom = || {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::constant(7)),
                        right: Box::new(MachineTerm::constant(7)),
                    },
                    true,
                )
            };
            let samples = [4, 8, 16, 32].map(|depth| {
                let mut proposition = atom();
                for level in 0..depth {
                    let left = Box::new(atom());
                    let right = Box::new(proposition);
                    proposition = match level % 3 {
                        0 => Proposition::And(left, right),
                        1 => Proposition::Or(left, right),
                        _ => Proposition::Implies(left, right),
                    };
                }
                let _scope = SurfaceSynthesisScope::enter();
                let surface = synthesize_surface_proposition_with_bound_variables(
                    &proposition,
                    ParameterBinding::default(),
                    &state,
                    &BTreeMap::new(),
                )
                .expect("connective synthesis must fit the small stack");
                let work = SURFACE_SYNTHESIS_BUDGET.with(|budget| {
                    let budget = budget.borrow();
                    let budget = budget.as_ref().unwrap();
                    assert_eq!(budget.depth, 0);
                    assert_eq!(budget.exhausted_category, None);
                    SURFACE_SYNTHESIS_WORK_LIMIT - budget.remaining_work
                });
                let mut pending = vec![&surface];
                let mut leaves = 0;
                while let Some(node) = pending.pop() {
                    match node {
                        ClickProposition::And(left, right)
                        | ClickProposition::Or(left, right)
                        | ClickProposition::Implies(left, right) => {
                            pending.push(left);
                            pending.push(right);
                        }
                        ClickProposition::Comparison {
                            operator: ComparisonOperator::Equal,
                            ..
                        } => leaves += 1,
                        _ => panic!("synthesis changed the proposition shape"),
                    }
                }
                assert_eq!(leaves, depth + 1);
                work
            });
            assert!(samples[0] > 0);
            for pair in samples.windows(2) {
                assert!(pair[1] > pair[0] && pair[1] <= 2 * pair[0], "{samples:?}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn load_defining_equation_round_trips() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("load-definition".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block("load-definition", 4);
    let state = ExecutionState::new().with_memory(memory).with_local(
        "p",
        ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
    );
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(state.memory()),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let MachineTerm::MemoryLoad(memory, address, kind) = load else {
        unreachable!()
    };
    let defining_load = crate::kernel::canonical_form_of_load(memory, *address, kind);
    let requirement = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(defining_load.clone()),
            right: Box::new(defining_load),
        },
        true,
    );
    let spelled = synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
        .expect("load-defining equation must be spellable");
    assert_eq!(
        relower_written_proposition(&spelled, &state)
            .map(|fact| crate::kernel::canonical_condition_fact(&fact)),
        Ok(crate::kernel::canonical_condition_fact(&requirement)),
    );
}

#[test]
fn load_defining_equation_uses_entry_state() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("load-definition-entry".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let entry = ExecutionState::new()
        .with_memory(Memory::new().with_block("load-definition-entry", 4))
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        );
    let post = entry.clone().with_memory(
        Memory::new()
            .with_block("load-definition-entry", 4)
            .store(pointer.clone(), int32(7)),
    );
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(entry.memory()),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let entry = entry.with_local(
        "result",
        ProgramValue::Int32(MachineTerm::Variable(variable)),
    );
    let requirement = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(variable)),
            right: Box::new(defining_load),
        },
        true,
    );
    let spelled = synthesize_surface_proposition_at_entry_and_post(
        &requirement,
        ParameterBinding::default(),
        &entry,
        &post,
    )
    .expect("entry load-defining equation must be spellable");
    let ClickProposition::At {
        selector: ProgramPointSelector::ProgramPoint(point),
        proposition,
    } = &spelled
    else {
        panic!("a changed post-state must retain the entry state: {spelled:?}");
    };
    assert_eq!(point.region, CodeRegionRef::Function);
    assert_eq!(point.kind, ProgramPointKind::Entry);
    let ClickProposition::Comparison { left, right, .. } = proposition.as_ref() else {
        panic!("the entry state must contain the defining equality: {spelled:?}");
    };
    assert_ne!(left, right, "the entry spelling must not be tautological");
    let lowered = relower_written_proposition(&spelled, &entry).unwrap();
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&lowered),
        crate::kernel::proof::proposition_identity_key(&requirement),
    );
}

#[test]
fn load_defining_equation_uses_saved_state() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("load-definition-saved".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let base = ExecutionState::new()
        .with_memory(Memory::new().with_block("load-definition-saved", 4))
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        );
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(base.memory()),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let retained_state = base.with_local(
        "result",
        ProgramValue::Int32(MachineTerm::Variable(variable)),
    );
    let entry = retained_state.clone().with_memory(
        Memory::new()
            .with_block("load-definition-saved", 4)
            .store(pointer.clone(), int32(1)),
    );
    let post = retained_state.clone().with_memory(
        Memory::new()
            .with_block("load-definition-saved", 4)
            .store(pointer, int32(2)),
    );
    let requirement = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(variable)),
            right: Box::new(defining_load),
        },
        true,
    );
    let selector = ProgramPointSelector::Mark("saved_load_epoch".into());
    let spelled = synthesize_surface_proposition_at_entry_post_and_state(
        &requirement,
        ParameterBinding::default(),
        &entry,
        &post,
        Some((&retained_state, &selector)),
    )
    .expect("the explicitly saved load state must be spellable");
    let ClickProposition::At {
        selector: actual,
        proposition,
    } = &spelled
    else {
        panic!("a changed entry and post-state must use the saved state: {spelled:?}");
    };
    assert_eq!(actual, &selector);
    let ClickProposition::Comparison { left, right, .. } = proposition.as_ref() else {
        panic!("the saved state must contain the defining equality: {spelled:?}");
    };
    assert_ne!(left, right, "the saved spelling must not be tautological");
    let mut recorded_states = RecordedStates::new();
    recorded_states.insert(selector, retained_state);
    let lowered = relower_written_proposition_with_states(&spelled, &post, &post, &recorded_states)
        .expect("the saved mark must lower through its recorded state");
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&lowered),
        crate::kernel::proof::proposition_identity_key(&requirement),
        "the saved state spelling must retain the shared load identity"
    );
}

/// Build the load equation emitted by a call whose contract reads one
/// structure field.  The bounded-pool and owned-string examples exercise this
/// shape for `pool->capacity` and `owner->len`, respectively.
fn example_load_defining_requirement(
    block: &str,
    local: &str,
    offset: i64,
) -> (ExecutionState, Proposition, Variable) {
    let pointer = Pointer {
        block: PointerBlock::Concrete(block.into()),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let state = ExecutionState::new()
        .with_memory(Memory::new().with_block(block, 16))
        .with_local(
            local,
            ProgramValue::typed_pointer(
                Pointer {
                    block: PointerBlock::Concrete(block.into()),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramType::Int32Pointer,
            ),
        );
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(state.memory()),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    (
        state,
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Variable(variable)),
                right: Box::new(defining_load),
            },
            true,
        ),
        variable,
    )
}

#[test]
fn bounded_pool_load_equation_round_trips_without_internal_names() {
    let (state, requirement, variable) =
        example_load_defining_requirement("bounded-pool:pool", "pool", 4);
    let state = state.with_local(
        "result",
        ProgramValue::Int32(MachineTerm::Variable(variable)),
    );
    let spelled = synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
        .expect("bounded-pool call load equation must be spellable");
    let ClickProposition::Comparison { left, right, .. } = &spelled else {
        panic!("load equation must remain an equality: {spelled:?}");
    };
    assert_ne!(left, right, "the source spelling must not be tautological");
    let lowered = relower_written_proposition(&spelled, &state).unwrap();
    assert_eq!(
        crate::kernel::canonical_condition_fact(&lowered),
        crate::kernel::canonical_condition_fact(&requirement)
    );
    assert!(!format!("{spelled:?}").contains(&variable.0.to_string()));
}

#[test]
fn owned_string_load_equation_round_trips_without_internal_names() {
    let (state, requirement, variable) =
        example_load_defining_requirement("owned-string:owner", "owner", 0);
    let state = state.with_local(
        "result",
        ProgramValue::Int32(MachineTerm::Variable(variable)),
    );
    let spelled = synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
        .expect("owned-string call load equation must be spellable");
    let ClickProposition::Comparison { left, right, .. } = &spelled else {
        panic!("load equation must remain an equality: {spelled:?}");
    };
    assert_ne!(left, right, "the source spelling must not be tautological");
    let lowered = relower_written_proposition(&spelled, &state).unwrap();
    assert_eq!(
        crate::kernel::canonical_condition_fact(&lowered),
        crate::kernel::canonical_condition_fact(&requirement)
    );
    assert!(!format!("{spelled:?}").contains(&variable.0.to_string()));
}

#[test]
fn load_equation_rejects_wrong_state_and_unresolvable_variable() {
    let (state, requirement, variable) =
        example_load_defining_requirement("owned-string:wrong-retained_state", "owner", 0);
    let wrong_memory = Memory::new().with_block("owned-string:other-epoch", 16);
    let wrong_pointer = Pointer {
        block: PointerBlock::Concrete("owned-string:wrong-retained_state".into()),
        offset: PointerOffsetTerm::Constant(4),
    };
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left,
            right: _,
        },
        true,
    ) = &requirement
    else {
        unreachable!()
    };
    let wrong_pointer_requirement = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: left.clone(),
            right: Box::new(MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(state.memory()),
                Box::new(wrong_pointer.clone()),
                crate::kernel::LoadKind::Int32,
            )),
        },
        true,
    );
    assert!(
        synthesize_surface_proposition(
            &wrong_pointer_requirement,
            ParameterBinding::default(),
            &state
        )
        .is_none()
    );

    let wrong_epoch = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: left.clone(),
            right: Box::new(MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(&wrong_memory),
                Box::new(Pointer {
                    block: PointerBlock::Concrete("owned-string:wrong-retained_state".into()),
                    offset: PointerOffsetTerm::Constant(0),
                }),
                crate::kernel::LoadKind::Int32,
            )),
        },
        true,
    );
    assert!(
        synthesize_surface_proposition(&wrong_epoch, ParameterBinding::default(), &state).is_none()
    );

    let unresolvable = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(Variable(variable.0 + 1))),
            right: left.clone(),
        },
        true,
    );
    assert!(
        synthesize_surface_proposition(&unresolvable, ParameterBinding::default(), &state)
            .is_none()
    );
}

fn actual_struct_field_load_equation(
    c_source: &str,
    block: &str,
    field_name: &str,
    field_offset: i64,
) {
    let function = syntax::parse_function(c_source).expect("the example C must parse");
    let parameter = function
        .parameters()
        .first()
        .expect("the example function has a struct pointer parameter")
        .clone();
    let base = Pointer {
        block: PointerBlock::Concrete(block.into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer = base.offset_by_bytes(field_offset as u32);
    let memory = Memory::new().with_block(block, 16);
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&memory),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let requirement = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(variable)),
            right: Box::new(defining_load),
        },
        true,
    );
    let state = ExecutionState::new()
        .with_memory(memory)
        .with_local(
            parameter.name(),
            ProgramValue::typed_pointer(base.clone(), ProgramType::UInt8Pointer),
        )
        .with_local(
            "result",
            ProgramValue::Int32(MachineTerm::Variable(variable)),
        );
    let parameters = [parameter];
    let arguments = [ProgramExpression::Value(ProgramValue::typed_pointer(
        base,
        ProgramType::UInt8Pointer,
    ))];
    let spelled = synthesize_surface_proposition(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
    )
    .expect("the example-shaped load equation must be spellable");
    let ClickProposition::Comparison { left, right, .. } = &spelled else {
        panic!("load equation must remain an equality: {spelled:?}");
    };
    assert_ne!(left, right, "the source spelling must not be tautological");
    assert!(matches!(left, ContractExpression::CBinding(name) if name == "result"));
    assert!(matches!(right, ContractExpression::Field { field, .. } if field == field_name));
    let lowered = relower_written_proposition(&spelled, &state).unwrap();
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&lowered),
        crate::kernel::proof::proposition_identity_key(&requirement),
        "the field spelling must retain the shared load identity"
    );
}

#[test]
fn bounded_pool_actual_capacity_load_equation_round_trips() {
    actual_struct_field_load_equation(
        include_str!("../../../../examples/bounded-pool/pool_checkout.c"),
        "bounded-pool:actual-pool",
        "capacity",
        4,
    );
}

#[test]
fn owned_string_actual_len_load_equation_round_trips() {
    actual_struct_field_load_equation(
        include_str!("../../../../examples/owned-string/owned_string_len.c"),
        "owned-string:actual-owner",
        "len",
        0,
    );
}

#[test]
fn signed_division_domain_propositions_round_trip_at_both_widths() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
        let left = MachineTerm::Variable(Variable(972_001));
        let right = MachineTerm::Variable(Variable(972_002));
        let wrap = |word| {
            if format == MachineIntegerType::Int32 {
                ProgramValue::Int32(word)
            } else {
                ProgramValue::Int64(word)
            }
        };
        let state = ExecutionState::new()
            .with_local("a", wrap(left.clone()))
            .with_local("b", wrap(right.clone()));
        let domain = Proposition::signed_division_defined(format, &left, &right);
        let surface = synthesize_surface_proposition(&domain, ParameterBinding::default(), &state)
            .expect("ordinary division domain spelling");
        assert_eq!(
            relower_written_proposition(&surface, &state).unwrap(),
            domain
        );
    }
}

#[test]
fn arithmetic_definedness_requirements_round_trip_at_both_machine_widths() {
    for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
        for op in [
            OverflowOperation::Add,
            OverflowOperation::Subtract,
            OverflowOperation::Multiply,
        ] {
            let left = MachineTerm::Variable(Variable(1));
            let right = MachineTerm::Variable(Variable(2));
            let value = |term| match format {
                MachineIntegerType::Int32 => ProgramValue::Int32(term),
                MachineIntegerType::Int64 => ProgramValue::Int64(term),
                _ => unreachable!(),
            };
            let state = ExecutionState::new()
                .with_local("left", value(left.clone()))
                .with_local("right", value(right.clone()))
                .with_local(
                    "result",
                    value(MachineTerm::machine_binary(
                        format,
                        match op {
                            OverflowOperation::Add => MachineBinaryOp::Add,
                            OverflowOperation::Subtract => MachineBinaryOp::Subtract,
                            OverflowOperation::Multiply => MachineBinaryOp::Multiply,
                            _ => unreachable!(),
                        },
                        left.clone(),
                        right.clone(),
                    )),
                );
            for truth in [false, true] {
                let domain = Proposition::signed_arithmetic_domain(
                    format,
                    match op {
                        OverflowOperation::Add => MachineBinaryOp::Add,
                        OverflowOperation::Subtract => MachineBinaryOp::Subtract,
                        OverflowOperation::Multiply => MachineBinaryOp::Multiply,
                        _ => unreachable!(),
                    },
                    &left,
                    &right,
                );
                let requirement = if truth {
                    Proposition::Not(Box::new(domain))
                } else {
                    domain
                };
                let surface = synthesize_surface_proposition(
                    &requirement,
                    ParameterBinding::default(),
                    &state,
                )
                .expect("arithmetic definedness must have a spelling");
                let lowered = relower_written_proposition(&surface, &state).unwrap();
                assert_eq!(
                    lowered, requirement,
                    "{format:?} {op:?} {truth}: {surface:?}"
                );
            }
        }
    }
}

#[test]
fn constant_integer_domain_requirements_round_trip() {
    for (condition, truth) in [(false, false), (false, true), (true, false), (true, true)] {
        let requirement = Proposition::ConditionIs(ConditionTerm::Constant(condition), truth);
        let state = ExecutionState::new();
        let surface =
            synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
                .expect("constant domain requirement must have a spelling");
        assert_eq!(
            relower_written_proposition(&surface, &state).unwrap(),
            requirement
        );
    }
}

#[test]
fn strlen_existential_guard_round_trips_without_duplicate_guard() {
    let variable = Variable(1);
    let increment = binary_node!(
        Int32,
        Add,
        Box::new(MachineTerm::Variable(variable)),
        Box::new(MachineTerm::constant(1)),
    );
    let requirement = Proposition::Exists {
        name: "len".to_string(),
        var: variable,
        sort: Sort::ProgramInt32,
        body: Box::new(Proposition::And(
            Box::new(Proposition::signed_arithmetic_domain(
                MachineIntegerType::Int32,
                crate::kernel::MachineBinaryOp::Add,
                &MachineTerm::Variable(variable),
                &MachineTerm::constant(1),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(MachineTerm::constant(0)),
                    right: Box::new(increment),
                },
                true,
            )),
        )),
    };
    let state = ExecutionState::new();
    let spelled = synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
        .expect("strlen requirement should synthesize");
    assert!(matches!(
        &spelled,
        ClickProposition::Exists {
            body,
            ..
        } if matches!(body.as_ref(), ClickProposition::Comparison { .. })
    ));
    let lowered = relower_written_proposition(&spelled, &state)
        .expect("the omitted guard must be regenerated by ordinary lowering");
    assert!(
        crate::kernel::proof::propositions_are_alpha_equal(&lowered, &requirement),
        "strlen spelling changed its proposition:\n  lowered: {lowered:?}\n  requirement: {requirement:?}"
    );
}

#[test]
fn strlen_guard_is_retained_when_the_sibling_does_not_regenerate_it() {
    let variable = Variable(1);
    let requirement = Proposition::Exists {
        name: "len".to_string(),
        var: variable,
        sort: Sort::ProgramInt32,
        body: Box::new(Proposition::And(
            Box::new(Proposition::signed_arithmetic_domain(
                MachineIntegerType::Int32,
                crate::kernel::MachineBinaryOp::Add,
                &MachineTerm::Variable(variable),
                &MachineTerm::constant(1),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: Box::new(MachineTerm::Variable(variable)),
                    right: Box::new(MachineTerm::constant(0)),
                },
                true,
            )),
        )),
    };
    let state = ExecutionState::new();
    let spelled = synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
        .expect("the negative shape should remain spellable");
    assert!(matches!(
        &spelled,
        ClickProposition::Exists {
            body,
            ..
        } if matches!(body.as_ref(), ClickProposition::And(left, _) if matches!(left.as_ref(), ClickProposition::And(..)))
    ));
    let lowered = relower_written_proposition(&spelled, &state)
        .expect("the retained guard and comparison should lower");
    assert!(
        crate::kernel::proof::propositions_are_alpha_equal(&lowered, &requirement),
        "retained guard changed its proposition:\n  lowered: {lowered:?}\n  requirement: {requirement:?}"
    );
}

#[test]
fn strlen_guard_prefix_synthesis_scales_linearly_and_fails_closed() {
    fn requirement(guard_count: usize) -> Proposition {
        let variable = Variable(1);
        let guard = Proposition::ConditionIs(
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: Box::new(MachineTerm::Variable(variable)),
                right: Box::new(MachineTerm::constant(1)),
            },
            false,
        );
        let comparison = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(MachineTerm::constant(0)),
                right: Box::new(binary_node!(
                    Int32,
                    Add,
                    Box::new(MachineTerm::Variable(variable)),
                    Box::new(MachineTerm::constant(1)),
                )),
            },
            true,
        );
        let mut body = comparison;
        for _ in 0..guard_count {
            body = Proposition::And(Box::new(guard.clone()), Box::new(body));
        }
        Proposition::Exists {
            name: "len".to_string(),
            var: variable,
            sort: Sort::ProgramInt32,
            body: Box::new(body),
        }
    }

    let samples = [1, 2, 4, 8].map(|guard_count| {
        let proposition = requirement(guard_count);
        let _scope = SurfaceSynthesisScope::enter();
        let surface = synthesize_surface_proposition_with_guard_fallback(
            &proposition,
            ParameterBinding::default(),
            &ExecutionState::new(),
            &BTreeMap::new(),
        )
        .expect("guard prefix should remain structurally spellable");
        if guard_count > 1 {
            assert!(matches!(
                surface,
                ClickProposition::Exists { body, .. }
                    if matches!(body.as_ref(), ClickProposition::And(left, _) if matches!(left.as_ref(), ClickProposition::Defined { .. }))
            ));
        }
        SURFACE_SYNTHESIS_BUDGET.with(|budget| {
            let budget = budget.borrow();
            let budget = budget.as_ref().expect("synthesis scope");
            assert_eq!(budget.depth, 0);
            SURFACE_SYNTHESIS_WORK_LIMIT - budget.remaining_work
        })
    });
    for pair in samples.windows(2) {
        assert!(
            pair[1] > pair[0] && pair[1] <= 3 * pair[0],
            "guard-prefix synthesis work is not linear: {samples:?}"
        );
    }
}

/// A borrowed pointer field can contain a fresh symbolic value, with no
/// registered load to recover its source spelling from. Both cast parameters
/// and locals must select its actual field, not a nearby pointer or old value.
#[test]
fn pointer_field_synthesis_through_cast_and_local_selects_current_value() {
    let function = syntax::parse_function(
        "struct job { int *decoy; int *selected; }; \
         void worker(void *argument) { struct job *job = argument; }",
    )
    .unwrap();
    let layout = function.structs().get("job").unwrap().clone();
    let base = Pointer {
        block: PointerBlock::Concrete("job".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owner = ProgramValue::typed_pointer(base.clone(), ProgramType::VoidPointer);
    let field_pointer = base.offset_by_bytes(layout.fields()["selected"].offset_bytes());
    let selected = PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(711)), 4);
    let decoy = PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(712)), 4);
    let value = |offset| {
        ProgramValue::typed_pointer(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset,
            },
            ProgramType::Int32Pointer,
        )
    };
    let memory = Memory::new()
        .with_block("job", 16)
        .store(base, value(decoy.clone()))
        .store(field_pointer.clone(), value(selected.clone()));
    let arguments = [ProgramExpression::Value(owner.clone())];
    for cast in [true, false] {
        let mut owners = SynthesisStructOwners::default();
        let state = if cast {
            owners
                .cast_parameters
                .insert("argument".into(), ("job".into(), layout.clone()));
            ExecutionState::new()
                .with_memory(memory.clone())
                .with_local("argument", owner.clone())
        } else {
            owners.locals.insert("job".into(), layout.clone());
            ExecutionState::new()
                .with_memory(memory.clone())
                .with_local("job", owner.clone())
        };
        let _scope = LocalStructLayoutScope(
            SYNTHESIS_STRUCT_OWNERS.with(|slot| slot.replace(Some(std::sync::Arc::new(owners)))),
        );
        let spelled = synthesize_parameter_field_pointer_value(
            &selected,
            ParameterBinding::new(function.parameters(), &arguments),
            &state,
        )
        .expect("the actual pointer field must have a spelling");
        assert!(matches!(&spelled, ContractExpression::Field { field, .. } if field == "selected"));
        let equality = ClickProposition::Comparison {
            left: spelled,
            operator: ComparisonOperator::Equal,
            right: ContractExpression::ProgramExpression(ProgramExpression::Value(value(
                selected.clone(),
            ))),
        };
        let lowered = relower_written_proposition(&equality, &state).unwrap();
        assert!(
            crate::kernel::search::ProofSearch::proves(&(PureFactContext::new()), &lowered),
            "{lowered:?}"
        );
        let changed = state.with_memory(
            memory
                .clone()
                .store(field_pointer.clone(), value(decoy.clone())),
        );
        assert!(
            synthesize_parameter_field_pointer_value(
                &selected,
                ParameterBinding::new(function.parameters(), &arguments),
                &changed,
            )
            .is_none(),
            "a previous field value must not be spelled as its current value"
        );
    }
}

/// A struct-pointer local and the array one of its fields points to are two
/// external pointers in one symbolic block. The array cell `occupied + k`
/// has a numeric element offset from the local, but `arena[occupied + k -
/// arena]` is not how the C names it: it reads the local as an `int32` array,
/// and it lowers to a different address term, so a bundle rendered that way
/// no longer lowers back to its goal. Reduced from the arena prefix free's
/// occupancy-clearing loop, whose invariant closer `both` refused.
#[test]
fn a_local_indexes_only_addresses_formed_from_it() {
    let scaled = |variable: u64| {
        PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(variable)), 4)
    };
    let external = |offset: PointerOffsetTerm| Pointer {
        block: PointerBlock::ExternalArgument,
        offset,
    };
    let (arena, occupied, index) = (200_000, 200_001, 200_002);
    let state = ExecutionState::new().with_local(
        "arena",
        ProgramValue::typed_pointer(external(scaled(arena)), ProgramType::Int32Pointer),
    );
    let unrelated_cell = external(PointerOffsetTerm::Add(
        Box::new(scaled(occupied)),
        Box::new(scaled(index)),
    ));
    assert_eq!(
        synthesize_local_indexed_load(
            &unrelated_cell,
            crate::kernel::LoadKind::Int32,
            ParameterBinding::default(),
            &state,
            &BTreeMap::new()
        ),
        None,
        "a cell addressed from another pointer is not an index of the local"
    );
    let own_cell = external(PointerOffsetTerm::Add(
        Box::new(scaled(arena)),
        Box::new(scaled(index)),
    ));
    let bound = BTreeMap::from([(Variable(index), "k".to_string())]);
    let Some(ContractExpression::Index(base, _)) = synthesize_local_indexed_load(
        &own_cell,
        crate::kernel::LoadKind::Int32,
        ParameterBinding::default(),
        &state,
        &bound,
    ) else {
        panic!("a cell addressed from the local is its index");
    };
    assert_eq!(
        *base,
        ContractExpression::ProgramExpression(ProgramExpression::Variable("arena".to_string()))
    );
}

/// A `uint32` order is spelled as the unsigned comparison over the `uint32`
/// local, and it lowers back to the condition it was spelled from. A signed
/// local needs an explicit uint32 cast to preserve the unsigned
/// interpretation.
#[test]
fn unsigned_comparison_is_spelled_over_uint32_operands() {
    let x = MachineTerm::Variable(Variable(300_000));
    let state = ExecutionState::new().with_local("x", ProgramValue::UInt32(x.clone()));
    for (condition, spelling) in [
        (
            ConditionTerm::unsigned_less_than(x.clone(), MachineTerm::constant(4)),
            "x < 4",
        ),
        (
            ConditionTerm::unsigned_greater_equal(x.clone(), MachineTerm::constant(4)),
            "x >= 4",
        ),
    ] {
        for value in [true, false] {
            let fact = Proposition::ConditionIs(condition.clone(), value);
            let synthesized =
                synthesize_surface_proposition(&fact, ParameterBinding::default(), &state)
                    .expect("an unsigned comparison over a uint32 local is spellable");
            let written = crate::surface::diagnostics::describe_click_proposition(&synthesized);
            assert!(
                written.contains(spelling) && !written.contains('^'),
                "{written}"
            );
            assert_eq!(
                relower_written_proposition(&synthesized, &state),
                Ok(fact.clone()),
                "{written}"
            );
        }
    }
    let signed = ExecutionState::new().with_local("y", ProgramValue::Int32(x.clone()));
    // The signed local's unsigned reading is σ, a node of its own.
    let fact = Proposition::ConditionIs(
        ConditionTerm::unsigned_less_than(
            MachineTerm::sign_cast32(MachineIntegerType::Int32, MachineIntegerType::UInt32, x),
            MachineTerm::constant(4),
        ),
        true,
    );
    let synthesized = synthesize_surface_proposition(&fact, ParameterBinding::default(), &signed)
        .expect("a signed local can be explicitly cast");
    assert!(
        crate::surface::printing::source_click_proposition(&synthesized).contains("uint32"),
        "a signed local needs an explicit unsigned cast"
    );
    assert_eq!(relower_written_proposition(&synthesized, &signed), Ok(fact));
}

#[test]
fn synthesized_unsigned_operations_and_computed_orders_relower_exactly() {
    let [x, divisor, result] =
        [300_010, 300_011, 300_012].map(|id| MachineTerm::Variable(Variable(id)));
    let state = ExecutionState::new()
        .with_local("x", ProgramValue::Int32(x.clone()))
        .with_local("divisor", ProgramValue::Int32(divisor.clone()))
        .with_local("result", ProgramValue::Int32(result.clone()));
    // The signed locals' unsigned readings are σ, a node of its own.
    let unsigned = |value| {
        MachineTerm::sign_cast32(MachineIntegerType::Int32, MachineIntegerType::UInt32, value)
    };
    let quotient = binary_node!(
        UInt32,
        Divide,
        Box::new(MachineTerm::uint32_constant(u32::MAX)),
        Box::new(unsigned(divisor.clone())),
    );
    let remainder = binary_node!(
        UInt32,
        Remainder,
        Box::new(unsigned(x.clone())),
        Box::new(unsigned(divisor))
    );
    for condition in [
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left: Box::new(quotient.clone()),
            right: Box::new(unsigned(result.clone())),
        },
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left: Box::new(remainder),
            right: Box::new(unsigned(result)),
        },
        ConditionTerm::unsigned_less_equal(unsigned(x), quotient),
    ] {
        for polarity in [true, false] {
            let fact = Proposition::ConditionIs(condition.clone(), polarity);
            let surface =
                synthesize_surface_proposition(&fact, ParameterBinding::default(), &state).unwrap();
            let lowered = relower_written_proposition(&surface, &state).unwrap();
            let Proposition::ConditionIs(lowered, lowered_truth) = lowered else {
                panic!("comparison")
            };
            let expected =
                crate::kernel::machine_integer::comparison::comparison_view(&condition, polarity)
                    .unwrap();
            let actual = crate::kernel::machine_integer::comparison::comparison_view(
                &lowered,
                lowered_truth,
            )
            .unwrap();
            assert_eq!(actual.format, expected.format);
            assert_eq!(actual.relation, expected.relation);
            let format = expected.format;
            for (actual, expected) in actual.operands.iter().zip(&expected.operands) {
                assert_eq!(
                    actual
                        .operand_view()
                        .observe(format)
                        .map(|value| value.value_read().clone()),
                    expected
                        .operand_view()
                        .observe(format)
                        .map(|value| value.value_read().clone()),
                    "condition={condition:?} surface={surface:?} actual={:?} expected={:?}",
                    actual.operand_view().retain(format).structural_value(),
                    expected.operand_view().retain(format).structural_value(),
                );
            }
        }
    }
}

#[test]
fn synthesized_uint32_cast_preserves_its_state() {
    let selector = ProgramPointSelector::Mark("before".into());
    let expression = synthesize_uint32_operand(ContractExpression::At {
        selector: selector.clone(),
        expression: Box::new(ContractExpression::ProgramExpression(
            ProgramExpression::Variable("x".into()),
        )),
    })
    .unwrap();
    assert!(
        matches!(&expression, ContractExpression::At { selector: actual, .. } if actual == &selector)
    );
    let surface = ClickProposition::Comparison {
        left: expression,
        operator: ComparisonOperator::Equal,
        right: ContractExpression::ProgramExpression(ProgramExpression::Value(
            ProgramValue::UInt32(MachineTerm::constant(u32::MAX)),
        )),
    };
    let before = ExecutionState::new().with_local("x", int32(u32::MAX));
    let after = ExecutionState::new().with_local("x", int32(0));
    let mut retained_states = RecordedStates::new();
    retained_states.insert(selector, before.clone());
    let lowered =
        relower_written_proposition_with_states(&surface, &before, &after, &retained_states)
            .unwrap();
    assert!(crate::kernel::planning_api::solve_builtin_prop(&lowered));
}

#[test]
fn wide_memory_selectors_preserve_width_and_signedness() {
    for (spelling, value_type, pointer_type, constant) in [
        (
            "int64",
            ProgramType::Int64,
            ProgramType::Int64Pointer,
            ProgramValue::Int64(MachineTerm::int64_constant(8589934592)),
        ),
        (
            "uint64",
            ProgramType::UInt64,
            ProgramType::UInt64Pointer,
            ProgramValue::UInt64(MachineTerm::uint64_constant(8589934592)),
        ),
    ] {
        let function = syntax::parse_function(&format!("void read({spelling} *p) {{ }}")).unwrap();
        let base = Pointer {
            block: PointerBlock::Concrete("wide".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let argument = ProgramValue::typed_pointer(base.clone(), pointer_type);
        let state = ExecutionState::new()
            .with_memory(Memory::new().with_block("wide", 32))
            .with_local("p", argument.clone());
        for offset in [0, 8, 24] {
            let address = ProgramExpression::Value(ProgramValue::typed_pointer(
                base.offset_by_bytes(offset),
                pointer_type,
            ));
            let written = ClickProposition::Comparison {
                left: ContractExpression::ProgramExpression(ProgramExpression::TypedLoad {
                    pointer: Box::new(address),
                    value_type,
                    volatile: false,
                    pointee_constant: false,
                    access_class: None,
                    source: Default::default(),
                }),
                operator: ComparisonOperator::LessThan,
                right: ContractExpression::ProgramExpression(ProgramExpression::Value(
                    constant.clone(),
                )),
            };
            let fact = relower_written_proposition(&written, &state).unwrap();
            let Proposition::ConditionIs(condition, _) = fact else {
                panic!("native order")
            };
            for truth in [true, false] {
                let fact = Proposition::ConditionIs(condition.clone(), truth);
                let surface = synthesize_surface_proposition(
                    &fact,
                    ParameterBinding::new(
                        function.parameters(),
                        &[ProgramExpression::Value(argument.clone())],
                    ),
                    &state,
                )
                .expect("a typed wide selector is spellable");
                assert_eq!(relower_written_proposition(&surface, &state), Ok(fact));
            }
        }
    }
}

#[test]
fn struct_loadable_spans_relower_without_widening_over_padding() {
    let function = syntax::parse_function(
        "struct item { int32 first; int32 last; }; int32 read(struct item *p) { return p->last; }",
    )
    .unwrap();
    let parameter = function.parameters()[0].clone();
    let pointer = Pointer {
        block: PointerBlock::Concrete("item".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer);
    let state = ExecutionState::new().with_local("p", value.clone());
    let arguments = [ProgramExpression::Value(value)];
    let plain = synthesize_struct_loadable_segment(
        &pointer.offset_by_bytes(4),
        &MachineTerm::constant(4),
        ParameterBinding::new(&[parameter], &arguments),
        &state,
    )
    .unwrap();
    assert_eq!(
        crate::surface::diagnostics::describe_click_proposition(&plain),
        "viewable(p->last)"
    );
    let plain_fact = relower_written_proposition(&plain, &state).unwrap();
    let padded = crate::languages::interface::RecordLayout::from_explicit_fields(
        vec![
            ("first".into(), InterfaceType::Int32, 0, 4),
            ("last".into(), InterfaceType::Int32, 4, 4),
        ],
        16,
        8,
    )
    .unwrap();
    let parameter = crate::languages::interface::ImportedParameter::new(
        InterfaceType::Int32Pointer,
        "p".into(),
        None,
    )
    .with_pointee_struct_layout("item".into(), padded);
    let clipped = synthesize_struct_loadable_segment(
        &pointer.offset_by_bytes(4),
        &MachineTerm::constant(4),
        ParameterBinding::new(&[parameter], &arguments),
        &state,
    )
    .unwrap();
    assert!(matches!(
        &clipped,
        ClickProposition::Loadable {
            segment: ContractSegment {
                surface: ContractSegmentSurface::Range { .. },
                ..
            }
        }
    ));
    assert_eq!(
        relower_written_proposition(&clipped, &state).unwrap(),
        plain_fact,
        "the byte spelling must preserve the exact four bytes, excluding padding"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../../scaling_tests/surface/proof/surface_synthesis/tests.rs");
}

#[test]
fn a_load_made_between_recorded_points_is_read_at_the_next_one() {
    // A call's region makes memories no point records: the load its contract
    // reads is registered in one of them. The first recorded memory after it
    // still reads the same bytes there, so the load is spelled at that point.
    let cell = Pointer {
        block: PointerBlock::Concrete("between-points".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let other = Pointer {
        block: PointerBlock::Concrete("between-points-other".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let with_memory = |memory: Memory| {
        ExecutionState::new().with_memory(memory).with_local(
            "p",
            ProgramValue::typed_pointer(cell.clone(), ProgramType::Int32Pointer),
        )
    };
    let blocks = || {
        Memory::new()
            .with_block("between-points", 4)
            .with_block("between-points-other", 4)
    };
    let before = with_memory(blocks().store(cell.clone(), int32(1)));
    crate::kernel::intern_memory_ref(before.memory());
    // The call leaves the cell's contents unknown; its contract says 5.
    let middle = blocks();
    let load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&middle),
        Box::new(cell.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let (variable, _) = crate::kernel::load_variable_for_term(&load).unwrap();
    let after = with_memory(middle.store(other, int32(1)));
    crate::kernel::intern_memory_ref(after.memory());
    let now = with_memory(after.memory().clone().store(cell.clone(), int32(9)));
    crate::kernel::intern_memory_ref(now.memory());
    let exit = ProgramPointSelector::from(ProgramPointRef {
        region: CodeRegionRef::Region(0),
        kind: ProgramPointKind::Exit,
    });
    let mut recorded_states = RecordedStates::new();
    recorded_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Entry,
        },
        before,
    );
    recorded_states.insert(exit.clone(), after);
    let fact = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(variable)),
            right: Box::new(MachineTerm::constant(5)),
        },
        true,
    );
    let spelled = {
        let _points = SynthesisRecordedPointsScope::enter(&recorded_states);
        synthesize_surface_proposition_at_entry_and_post(
            &fact,
            ParameterBinding::default(),
            &now,
            &now,
        )
    }
    .expect("the load must be spelled at the point after the memory it was made in");
    assert!(
        format!("{spelled:?}").contains(&format!("{exit:?}")),
        "the load must be read at the next recorded point: {spelled:?}"
    );
    let lowered = relower_written_proposition_with_states(&spelled, &now, &now, &recorded_states)
        .expect("the spelling must lower through its recorded state");
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&lowered),
        crate::kernel::proof::proposition_identity_key(&fact),
        "the spelling must name the load made between the points"
    );
}

#[test]
fn a_pointer_a_local_no_longer_holds_is_spelled_where_it_was_introduced() {
    // `q = view(p); q = r;` leaves the value `view` returned in no local, so
    // the current state cannot name it; the point after the first call held
    // it in `q`, so `at(that point, q) != NULL` spells the fact `view`'s
    // contract gave about it.
    let returned = Pointer {
        block: PointerBlock::Symbolic(Variable(910_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let other = Pointer {
        block: PointerBlock::Concrete("pointer-introduced-other".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block("pointer-introduced-other", 4);
    let entry = ExecutionState::new()
        .with_memory(memory.clone())
        .with_local(
            "r",
            ProgramValue::typed_pointer(other.clone(), ProgramType::Int32Pointer),
        );
    let introduced = entry.clone().with_local(
        "q",
        ProgramValue::typed_pointer(returned.clone(), ProgramType::Int32Pointer),
    );
    let now = introduced.clone().with_local(
        "q",
        ProgramValue::typed_pointer(other.clone(), ProgramType::Int32Pointer),
    );
    let exit = ProgramPointSelector::from(ProgramPointRef {
        region: CodeRegionRef::Region(0),
        kind: ProgramPointKind::Exit,
    });
    let mut recorded_states = RecordedStates::new();
    recorded_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Entry,
        },
        entry,
    );
    recorded_states.insert(exit.clone(), introduced);
    recorded_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(1),
            kind: ProgramPointKind::Exit,
        },
        now.clone(),
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::PointerEqual(Box::new(returned), Box::new(Pointer::null())),
        false,
    );
    let spelled = {
        let _points = SynthesisRecordedPointsScope::enter(&recorded_states);
        synthesize_surface_proposition_at_entry_and_post(
            &fact,
            ParameterBinding::default(),
            &now,
            &now,
        )
    }
    .expect("the returned pointer must be spelled where `q` held it");
    assert!(
        format!("{spelled:?}").contains(&format!("{exit:?}")),
        "the pointer must be read at the point that introduced it: {spelled:?}"
    );
    let lowered = relower_written_proposition_with_states(&spelled, &now, &now, &recorded_states)
        .expect("the spelling must lower through its recorded state");
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&lowered),
        crate::kernel::proof::proposition_identity_key(&fact),
        "the spelling must name the pointer `q` held"
    );
}

#[test]
fn recorded_memories_near_a_read_are_offered_after_it_then_before_it() {
    // Memories interned in program order: `first` and `second` are recorded,
    // `between` is made between them and `last` after both. A read in
    // `between` is next recorded at `second`; a read in `last` was last
    // recorded at `second`, then `first`.
    let memory = |block: &str| {
        // Give each point distinct bytes; a declaration alone preserves
        // read identity and intentionally selects its newest recorded point.
        let memory = Memory::new().with_block(block, 4).store(
            Pointer {
                block: block.into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramValue::Int32(MachineTerm::constant(0)),
        );
        crate::kernel::intern_memory_ref(&memory)
    };
    let point = |index| {
        ProgramPointSelector::from(ProgramPointRef {
            region: CodeRegionRef::Region(index),
            kind: ProgramPointKind::Exit,
        })
    };
    let first = memory("near-first");
    let between = memory("near-between");
    let second = memory("near-second");
    let last = memory("near-last");
    let mut recorded_states = RecordedStates::new();
    recorded_states.insert(
        point(0),
        ExecutionState::new().with_memory(first.memory().clone()),
    );
    recorded_states.insert(
        point(1),
        ExecutionState::new().with_memory(second.memory().clone()),
    );
    let near = |memory| {
        recorded_states
            .points_near_memory(memory)
            .map(|(selector, _)| selector.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(near(&between), vec![point(1), point(0)]);
    assert_eq!(near(&last), vec![point(1), point(0)]);
    assert_eq!(near(&first), vec![point(0), point(1)]);
}

#[test]
fn a_model_field_value_its_instance_no_longer_holds_is_spelled_where_it_was_introduced() {
    // A call replaces `o`'s model, so the earlier `o.size` value is held by
    // no current instance; the point after the first call held it.
    use crate::kernel::{
        AlgebraicValue, Resource, ResourceContext, ResourceFact, ResourceFieldSchema,
        ResourceFieldType, ResourceInstance,
    };
    let identity = Variable(930_001);
    let (earlier, later) = (Variable(930_002), Variable(930_003));
    let schema = ResourceFieldSchema::new(vec![(
        "size".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let holding = |value: Variable| {
        let instance = ResourceInstance::new(
            identity,
            "object".into(),
            vec![].into(),
            schema.clone(),
            vec![AlgebraicValue::Program(ProgramValue::Int32(
                MachineTerm::Variable(value),
            ))]
            .into(),
        )
        .unwrap();
        ExecutionState::new().with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance))),
        )
    };
    crate::kernel::model_fields::register_instance_spelling(identity, "o");
    for value in [earlier, later] {
        crate::kernel::model_fields::register_model_field_variable(
            value,
            crate::kernel::model_fields::ModelFieldOrigin {
                identity,
                field: "size".into(),
                field_index: 0,
                minted_by: crate::kernel::model_fields::ModelMint::LoopHead,
            },
        );
    }
    let point = |index| {
        ProgramPointSelector::from(ProgramPointRef {
            region: CodeRegionRef::Region(index),
            kind: ProgramPointKind::Exit,
        })
    };
    let now = holding(later);
    let mut recorded_states = RecordedStates::new();
    recorded_states.insert(point(0), holding(earlier));
    recorded_states.insert(point(1), now.clone());
    let fact = Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(MachineTerm::Variable(earlier)),
            right: Box::new(MachineTerm::constant(5)),
        },
        true,
    );
    let spelled = {
        let _points = SynthesisRecordedPointsScope::enter(&recorded_states);
        synthesize_surface_proposition_at_entry_and_post(
            &fact,
            ParameterBinding::default(),
            &now,
            &now,
        )
    }
    .expect("the earlier field value must be spelled where its instance held it");
    let ClickProposition::Comparison { left, .. } = &spelled else {
        panic!("the fact must be spelled as a comparison: {spelled:?}");
    };
    let ContractExpression::At {
        selector,
        expression,
    } = left
    else {
        panic!("the earlier field value must be read at a recorded point: {spelled:?}");
    };
    assert_eq!(selector, &point(0));
    assert!(
        matches!(expression.as_ref(), ContractExpression::ResourceField(field) if field.field == "size"),
        "the value must be spelled as the instance's field: {spelled:?}"
    );
}

#[test]
fn recorded_cells_offer_the_points_that_held_a_value_newest_first() {
    // A value two stores put in a cell, between which a store overwrote
    // it, is offered at both points that recorded it there, newest first;
    // a value no cell held is offered nowhere.
    let cell = Pointer {
        block: PointerBlock::Concrete("cell-introduced".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = MachineTerm::Variable(Variable(940_001));
    let point = |index| {
        ProgramPointSelector::from(ProgramPointRef {
            region: CodeRegionRef::Region(index),
            kind: ProgramPointKind::Exit,
        })
    };
    let entry = Memory::new()
        .with_block("cell-introduced", 4)
        .store(cell.clone(), int32(1));
    let first = entry
        .clone()
        .store(cell.clone(), ProgramValue::Int32(value.clone()));
    let overwritten = first.clone().store(cell.clone(), int32(9));
    let again = overwritten
        .clone()
        .store(cell, ProgramValue::Int32(value.clone()));
    let mut recorded_states = RecordedStates::new();
    for (index, memory) in [entry, first, overwritten, again].into_iter().enumerate() {
        recorded_states.insert(point(index), ExecutionState::new().with_memory(memory));
    }
    let offered = |term: &MachineTerm| {
        recorded_states
            .points_holding_cell_integer(term)
            .map(|(selector, _)| selector.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(offered(&value), vec![point(3), point(1)]);
    assert!(offered(&MachineTerm::Variable(Variable(940_002))).is_empty());
}

#[test]
fn allocation_result_names_survive_reassignment_and_follow_state_scope() {
    let function =
        crate::languages::c::syntax::parse_function("void f() { int32* p; p = malloc(4); p = 0; }")
            .unwrap();
    let layout = crate::surface::lowering::SourceExecutionLayout::for_function(&function).unwrap();
    let region = layout
        .source_path_region(&[SourcePathStep::Statement(1)], ProgramPointKind::Exit)
        .unwrap();
    let point = ProgramPointRef {
        region: CodeRegionRef::Region(region),
        kind: ProgramPointKind::Exit,
    };
    let first = Pointer {
        block: PointerBlock::Heap(989_030),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block: PointerBlock::Heap(989_031),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = |pointer: &Pointer| {
        ExecutionState::new().with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        )
    };
    let mut retained_states = RecordedStates::new().with_source_layout(layout);
    assert!(retained_states.region_allocation(&point.region).is_err());
    retained_states.insert(point.clone(), state(&first));
    let sibling = retained_states.clone();
    assert_eq!(
        retained_states.allocation_result(&first),
        Some(point.region.clone())
    );
    let current = state(&Pointer::null());
    let raised = {
        let _points = SynthesisRecordedPointsScope::enter(&retained_states);
        synthesize_surface_pointer_expression(
            &first,
            ParameterBinding::default(),
            &current,
            &BTreeMap::new(),
        )
    };
    assert_eq!(
        raised,
        Some(ContractExpression::RegionAllocation(point.region.clone()))
    );
    let surface = ClickProposition::Comparison {
        left: ContractExpression::RegionAllocation(point.region.clone()),
        operator: ComparisonOperator::Equal,
        right: ContractExpression::QualifiedC {
            name: "allocation_under_test".to_owned(),
            lowered: ProgramExpression::Value(ProgramValue::typed_pointer(
                first.clone(),
                ProgramType::Int32Pointer,
            )),
        },
    };
    let lowered =
        relower_written_proposition_with_states(&surface, &current, &current, &retained_states)
            .unwrap();
    assert_eq!(
        lowered,
        Proposition::ConditionIs(ConditionTerm::Constant(true), true)
    );
    retained_states.insert(point.clone(), state(&second));
    assert!(retained_states.allocation_result(&first).is_none());
    assert_eq!(
        retained_states.allocation_result(&second),
        Some(point.region.clone())
    );
    assert_eq!(
        sibling.allocation_result(&first),
        Some(point.region.clone())
    );
    retained_states.remove(&point);
    assert!(retained_states.allocation_result(&second).is_none());
}

#[test]
fn global_array_entry_value_keeps_its_exact_spelling_after_a_write() {
    let function = crate::kernel::ProgramFunction::new(
        ProgramType::Void,
        "array_entry",
        vec![],
        crate::kernel::ProgramStatement::Skip,
    )
    .with_global_arrays(vec![crate::kernel::GlobalArray::new_with_kernel_name(
        "g",
        "g",
        ProgramType::Int32,
        4,
        vec![int32(0); 4],
    )]);
    let entry = crate::kernel::program_function_entry_state(&ExecutionState::new(), &function, &[])
        .unwrap();
    let pointer = Memory::global_pointer("g").offset_by_bytes(12);
    let term = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_memory_ref(entry.memory()),
        pointer.clone(),
        crate::kernel::LoadKind::Int32,
    );
    let post = entry
        .clone()
        .with_memory(entry.memory().clone().store(pointer, int32(7)));
    let requirement = Proposition::signed_arithmetic_domain(
        MachineIntegerType::Int32,
        crate::kernel::MachineBinaryOp::Add,
        &term,
        &MachineTerm::constant(1),
    );
    let mut owners = SynthesisStructOwners::default();
    owners
        .storage_arrays
        .insert("g".into(), ("g".into(), vec![2, 2]));
    let _scope = LocalStructLayoutScope(
        SYNTHESIS_STRUCT_OWNERS.with(|slot| slot.replace(Some(std::sync::Arc::new(owners)))),
    );
    let spelled = synthesize_surface_proposition_at_entry_and_post(
        &requirement,
        ParameterBinding::default(),
        &entry,
        &post,
    )
    .expect("an overwritten global array element keeps its entry spelling");
    assert!(format!("{spelled:?}").contains("Old("), "{spelled:?}");
    assert!(format!("{spelled:?}").contains("ArrayIndex"), "{spelled:?}");
    let (values, arrays) = crate::surface::lowering::contract_environment_for_names(
        ParameterBinding::default(),
        &BTreeSet::from(["g".to_string()]),
        &post,
    )
    .unwrap();
    let lowered = crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
        &spelled,
        &PureFactContext::new(),
        ContractEnvironment::new(&values, &arrays),
        FixedStateFrame::new(&entry, &post, None, &RecordedStates::new()),
        SpecDefinitions::new(
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
        ),
        FixedStateLoweringOptions::default(),
    ).map(|(proposition, _, _, _)| proposition);
    assert_eq!(lowered, Ok(requirement));
}

#[test]
fn array_index_spelling_keeps_the_source_index_at_each_integer_width() {
    let _session = crate::kernel::VerificationSession::enter();
    let i = MachineTerm::Variable(Variable(989_971));
    for (format, source_type) in [
        (MachineIntegerType::Int32, "int32"),
        (MachineIntegerType::UInt32, "uint32"),
        (MachineIntegerType::UInt64, "usize"),
    ] {
        for (pointer_type, element_format, width, load_kind, zero) in [
            (
                ProgramType::Int32Pointer,
                MachineIntegerType::Int32,
                4,
                crate::kernel::LoadKind::Int32,
                MachineTerm::constant(0),
            ),
            (
                ProgramType::Int64Pointer,
                MachineIntegerType::Int64,
                8,
                crate::kernel::LoadKind::Bits64,
                MachineTerm::int64_constant(0),
            ),
        ] {
            for increment in [false, true] {
                let value = match format {
                    MachineIntegerType::Int32 => ProgramValue::Int32(i.clone()),
                    MachineIntegerType::UInt32 => ProgramValue::UInt32(i.clone()),
                    MachineIntegerType::UInt64 => ProgramValue::UInt64(i.clone()),
                    _ => unreachable!(),
                };
                let base = Pointer {
                    block: PointerBlock::Concrete("indexed-array".into()),
                    offset: PointerOffsetTerm::Constant(0),
                };
                let state = ExecutionState::new()
                    .with_memory(Memory::new().with_block("indexed-array", 128))
                    .with_local("a", ProgramValue::typed_pointer(base.clone(), pointer_type))
                    .with_local("i", value);
                let index = if increment {
                    let one = match format {
                        MachineIntegerType::Int32 => MachineTerm::constant(1),
                        MachineIntegerType::UInt32 => MachineTerm::uint32_constant(1),
                        _ => MachineTerm::uint64_constant(1),
                    };
                    MachineTerm::Binary {
                        format,
                        op: crate::kernel::MachineBinaryOp::Add,
                        left: Box::new(i.clone()),
                        right: Box::new(one),
                    }
                } else {
                    i.clone()
                };
                let offset = match format {
                    MachineIntegerType::Int32 => PointerOffsetTerm::scaled_int32_node(index, width),
                    MachineIntegerType::UInt32 => PointerOffsetTerm::scaled_int64_node(
                        MachineTerm::legacy_cast(
                            MachineCastSpelling::UInt64From32,
                            Box::new(index),
                        ),
                        width,
                        true,
                    ),
                    _ => PointerOffsetTerm::scaled_int64_node(index, width, true),
                };
                let load = MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory_ref(state.memory()),
                    Box::new(Pointer {
                        block: base.block.clone(),
                        offset,
                    }),
                    load_kind,
                );
                let exports = crate::kernel::KernelTermExport::machine_export_count();
                let spelled = synthesize_surface_bitvector(
                    &load,
                    ParameterBinding::default(),
                    &state,
                    &BTreeMap::new(),
                )
                .unwrap();
                assert_eq!(
                    crate::kernel::KernelTermExport::machine_export_count(),
                    exports
                );
                assert!(
                    matches!(&spelled, ContractExpression::Index(..)),
                    "{spelled:?}"
                );
                let text = crate::surface::diagnostics::describe_contract_expression(&spelled);
                assert!(!text.contains(" as "), "{text}");
                if !increment {
                    assert_eq!(text, "a[i]");
                }
                let right = ContractExpression::ProgramExpression(ProgramExpression::Value(
                    if width == 8 {
                        ProgramValue::Int64(zero.clone())
                    } else {
                        ProgramValue::Int32(zero.clone())
                    },
                ));
                let surface = ClickProposition::Comparison {
                    left: spelled,
                    operator: ComparisonOperator::Equal,
                    right: right.clone(),
                };
                let expected = Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: element_format,
                        relation: CompareRelation::Equal,
                        left: Box::new(load),
                        right: Box::new(zero.clone()),
                    },
                    true,
                );
                let lowered = relower_written_proposition(&surface, &state).unwrap();
                assert_eq!(
                    crate::kernel::canonical_condition_fact(&lowered),
                    crate::kernel::canonical_condition_fact(&expected)
                );
                // Reparse the written read in the source language as well.
                let (prefix, pointer_type, result_type) = if source_type == "usize" {
                    (
                        "verifying \"indices.rs\";",
                        if width == 8 {
                            "*const i64"
                        } else {
                            "*const i32"
                        },
                        if width == 8 { "i64" } else { "i32" },
                    )
                } else {
                    (
                        "",
                        if width == 8 { "int64*" } else { "int32*" },
                        if width == 8 { "int64" } else { "int32" },
                    )
                };
                let parsed = parser::parse(&format!("{prefix} function indexed(a: {pointer_type}, i: {source_type}) -> {result_type} {{ {text} }}")).unwrap();
                let reparsed = ClickProposition::Comparison {
                    left: parsed.click_function_definitions()[0]
                        .body()
                        .unwrap()
                        .clone(),
                    operator: ComparisonOperator::Equal,
                    right,
                };
                assert_eq!(
                    crate::kernel::canonical_condition_fact(
                        &relower_written_proposition(&reparsed, &state).unwrap()
                    ),
                    crate::kernel::canonical_condition_fact(&expected)
                );
            }
        }
    }
}

#[test]
fn boolean_calls_conditionals_and_equalities_round_trip_in_both_polarities() {
    let file = parser::parse("function positive(x: int32) -> Bool { x > 0 } function choose(flag: Bool, x: int32) -> Bool { if flag { positive(x) } else { false } }").unwrap();
    let flag = ConditionTerm::Variable(Variable(9001));
    let x = MachineTerm::Variable(Variable(9002));
    let state = ExecutionState::new()
        .with_local("flag", ProgramValue::of_bool(flag.clone()))
        .with_local("x", ProgramValue::Int32(x.clone()));
    let positive = ConditionTerm::bool_application(
        "positive",
        vec![crate::kernel::PureFunctionArgument::Value(
            ProgramValue::Int32(x.clone()),
        )],
    );
    let chosen = ConditionTerm::bool_application(
        "choose",
        vec![
            crate::kernel::PureFunctionArgument::Value(ProgramValue::of_bool(flag.clone())),
            crate::kernel::PureFunctionArgument::Value(ProgramValue::Int32(x)),
        ],
    );
    for condition in [
        flag.clone(),
        positive.clone(),
        chosen,
        ConditionTerm::bool_if(flag, positive.clone(), ConditionTerm::Constant(false)),
        ConditionTerm::bool_equal(positive.clone(), ConditionTerm::bool_not(positive)),
    ] {
        for truth in [false, true] {
            let fact = condition.truth_claim(truth);
            let surface =
                synthesize_surface_proposition(&fact, ParameterBinding::default(), &state)
                    .expect("Bool fact spelling");
            let lowered = crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
                &surface, &PureFactContext::new(), ContractEnvironment::new(&BTreeMap::new(), &BTreeMap::new()),
                FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::new(file.click_function_definitions())),
                FixedStateLoweringOptions::default(),
            ).unwrap().0;
            assert_eq!(lowered, fact, "{surface:?}");
        }
    }
}

#[test]
fn generic_call_spelling_reparses_to_the_same_concrete_and_nested_instance() {
    let declarations = "spec enum Wrapped<T> { Value(T) } function holds<T>(wrapped: Wrapped<T>, value: T) -> Bool { true }";
    for arguments in [
        "Wrapped<int32>::Value(x), x",
        "Wrapped<Wrapped<int32>>::Value(Wrapped<int32>::Value(x)), Wrapped<int32>::Value(x)",
    ] {
        let source = format!(
            "{declarations} theorem probe(x: int32) {{ requires holds({arguments}); ensures true; }}"
        );
        let file = parser::parse(&source).unwrap();
        let state = ExecutionState::new().with_local(
            "x",
            ProgramValue::Int32(MachineTerm::Variable(Variable(99001))),
        );
        let values = BTreeMap::from([(
            "x".to_string(),
            ProgramValue::Int32(MachineTerm::Variable(Variable(99001))),
        )]);
        let lower = |proposition: &ClickProposition| {
            crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
                proposition, &PureFactContext::new(), ContractEnvironment::new(&values, &BTreeMap::new()),
                FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::with_algebraic_types(file.click_function_definitions(), file.algebraic_type_definitions())),
                FixedStateLoweringOptions::default(),
            ).unwrap().0
        };
        let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
            panic!("requirement");
        };
        let original = lower(written);
        let spelled =
            synthesize_surface_proposition(&original, ParameterBinding::default(), &state)
                .expect("generic instance spelling");
        let text = crate::surface::printing::source_click_proposition(&spelled);
        assert!(!text.contains("::<"), "{text}");
        let reparsed = parser::parse(&format!(
            "{declarations} theorem probe(x: int32) {{ requires {text}; ensures true; }}"
        ))
        .unwrap();
        let Requirement::Proposition(written_again) =
            &reparsed.theorem_definitions()[0].requires()[0]
        else {
            panic!("requirement");
        };
        assert_eq!(lower(written_again), original, "{text}");
    }
}

#[test]
fn pointee_layout_spells_a_field_load_at_its_byte_offset() {
    // A C++ receiver uses a byte pointer internally, with its 16-byte
    // nominal object layout retained separately. `p + 8` is not its field.
    let layout = crate::languages::interface::RecordLayout::from_explicit_fields(
        vec![
            (
                "header".into(),
                InterfaceType::UInt64(crate::languages::c::target::LongRank::LongLong),
                0,
                8,
            ),
            ("side".into(), InterfaceType::Int32, 8, 4),
        ],
        16,
        8,
    )
    .unwrap();
    let parameter = crate::languages::interface::ImportedParameter::new(
        InterfaceType::UInt8Pointer,
        "p".into(),
        None,
    )
    .with_pointee_struct_layout("Square".into(), layout);
    assert!(parameter.struct_layout().is_none());
    let pointer = Pointer {
        block: PointerBlock::Concrete("square".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt8Pointer);
    let state = ExecutionState::new().with_local("p", value.clone());
    let arguments = [ProgramExpression::Value(value)];
    let parameters = [parameter];
    let load = synthesize_parameter_field_load(
        &pointer.offset_by_bytes(8),
        ProgramType::Int32,
        ParameterBinding::new(&parameters, &arguments),
    )
    .expect("a pointer parameter's nominal layout names its field");
    let expected = ClickProposition::Defined {
        expression: ContractExpression::ProgramExpression(ProgramExpression::TypedLoad {
            pointer: Box::new(ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(ProgramExpression::Variable("p".into())),
                bytes: 8,
            }),
            value_type: ProgramType::Int32,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        }),
    };
    let surface = ClickProposition::Defined { expression: load };
    assert_eq!(
        crate::surface::printing::source_click_proposition(&surface),
        "defined(p->side)"
    );
    assert_eq!(
        relower_written_proposition(&surface, &state),
        relower_written_proposition(&expected, &state)
    );
    assert!(relower_written_proposition(&surface, &state).is_ok());
}

#[test]
fn mathematical_constant_goals_keep_structure_and_type() {
    use crate::kernel::IntegerTerm;
    let c = IntegerTerm::constant_i64;
    let pairs = [
        (c(1), c(1)),
        (IntegerTerm::Add(c(1).into(), c(1).into()), c(2)),
        (IntegerTerm::Add(c(1).into(), c(1).into()), c(3)),
        (
            IntegerTerm::Add(c(2147483647).into(), c(1).into()),
            c(2147483648),
        ),
        (IntegerTerm::Subtract(c(1).into(), c(1).into()), c(0)),
        (IntegerTerm::Multiply(c(3).into(), c(2).into()), c(6)),
        (IntegerTerm::Negate(c(1).into()), c(-1)),
        (
            IntegerTerm::Negate(IntegerTerm::Negate(c(1).into()).into()),
            c(1),
        ),
        (
            IntegerTerm::TruncatingQuotient(c(-7).into(), c(3).into()),
            c(-2),
        ),
        (
            IntegerTerm::TruncatingRemainder(c(-7).into(), c(3).into()),
            c(-1),
        ),
    ];
    for (left, right) in pairs {
        for constructor in [
            ConditionTerm::IntegerEqual,
            ConditionTerm::IntegerNotEqual,
            ConditionTerm::IntegerLessThan,
            ConditionTerm::IntegerLessEqual,
            ConditionTerm::IntegerGreaterThan,
            ConditionTerm::IntegerGreaterEqual,
        ] {
            for truth in [false, true] {
                let goal = Proposition::ConditionIs(
                    constructor(left.clone().into(), right.clone().into()),
                    truth,
                );
                let state = ExecutionState::new();
                let surface =
                    synthesize_surface_proposition(&goal, ParameterBinding::default(), &state)
                        .unwrap();
                let text = crate::surface::printing::source_click_proposition(&surface);
                assert_eq!(
                    relower_written_proposition(&surface, &state).unwrap(),
                    goal,
                    "{text}"
                );
                let file = parser::parse(&format!(
                    "theorem probe() {{ requires {text}; ensures true; }}"
                ))
                .unwrap();
                let Requirement::Proposition(parsed) = &file.theorem_definitions()[0].requires()[0]
                else {
                    panic!()
                };
                assert_eq!(
                    relower_written_proposition(parsed, &state).unwrap(),
                    goal,
                    "{text}"
                );
            }
        }
    }
}

#[test]
fn unified_terms_round_trip_nested_calls_and_mixed_integer_arguments() {
    let declarations = "function positive(x: int32) -> Bool { x > 0 } function foo(x: int32) -> Integer { to_integer(x) } function foo_wide(x: int64) -> Integer { to_integer(x) } function bar(x: Integer) -> Integer { x + 1 }";
    for expression in [
        "to_integer(x) + foo(x)",
        "foo(positive(x) as int32)",
        "foo((if foo(x) + 1 < foo(x) { true } else { false }) as int32)",
        "foo((if foo(x) + 1 <= foo(x) { true } else { false }) as int32)",
        "foo((if foo(x) + 1 > foo(x) { true } else { false }) as int32)",
        "foo((if foo(x) + 1 >= foo(x) { true } else { false }) as int32)",
        "foo((if foo(x) + 1 == foo(x) { true } else { false }) as int32)",
        "foo((if foo(x) + 1 != foo(x) { true } else { false }) as int32)",
        "foo_wide(positive(x) as int64)",
        "to_integer(positive(x) as uint64) + foo(x)",
        "foo((if x > 0 { true } else { false }) as int32)",
        "foo((if x > 0 { positive(x) } else { false }) as int32)",
        "to_integer(positive(x) as uint8) + foo(x)",
        "to_integer(positive(x) as int16) + foo(x)",
        "foo(to_int32(foo(x)))",
        "foo_wide(to_int64(foo(x) + 1))",
        "to_integer(to_uint64(foo(x))) + foo(x)",
        "to_integer(x as uint32) + foo(x)",
        "to_integer(x as int8) + foo(x)",
        "to_integer(x as uint8) + foo(x)",
        "to_integer(x as int64) + foo(x)",
        "to_integer(x as uint64) + foo(x)",
        "bar(foo(x) + 1) * (foo(x) - 2)",
        "-foo(x)",
        "foo(x + 1)",
        "foo(if x > 0 { x + 1 } else { x - 1 })",
        "foo(if positive(x) { x } else { 0 })",
        "foo_wide(if x > 0 { x as int64 } else { 0i64 })",
        "foo(x * 2)",
        "foo(x / 2)",
        "foo((x / 2) % 3)",
        "if foo(x) < 0 { foo(x) + 1 } else { foo(x) - 1 }",
        "foo(x ^ 1)",
        "foo(x << 1)",
        "foo(x >> 1)",
        "foo(x << (x as int64))",
        "foo(x >> (x as uint64))",
        "foo_wide((x as int64) << x)",
        "foo_wide((x as int64) >> (x as uint32))",
        "foo(~x)",
        "foo_wide(x as int64)",
        "foo_wide((x as uint32) as int64)",
        "foo_wide((x as int64) + 1i64)",
        "foo_wide((x as int128) as int64)",
    ] {
        let source = format!(
            "{declarations} theorem probe(x: int32) {{ requires {expression} == 0; ensures true; }}"
        );
        let file = parser::parse(&source).unwrap();
        let value = ProgramValue::Int32(MachineTerm::Variable(Variable(99002)));
        let state = ExecutionState::new().with_local("x", value.clone());
        let values = BTreeMap::from([("x".to_string(), value)]);
        let lower = |proposition: &ClickProposition| {
            crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
                proposition, &PureFactContext::new(), ContractEnvironment::new(&values, &BTreeMap::new()),
                FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::new(file.click_function_definitions())),
                FixedStateLoweringOptions::default(),
            ).unwrap().0
        };
        let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
            panic!("requirement")
        };
        let original = lower(written);
        let raised = synthesize_surface_proposition(&original, ParameterBinding::default(), &state)
            .unwrap_or_else(|| panic!("shared term spelling: {expression}"));
        let text = crate::surface::printing::source_click_proposition(&raised);
        let call_name = if expression.contains("foo_wide(") {
            "foo_wide("
        } else {
            "foo("
        };
        assert!(text.contains(call_name), "opaque call must survive: {text}");
        let reparsed = parser::parse(&format!(
            "{declarations} theorem probe(x: int32) {{ requires {text}; ensures true; }}"
        ))
        .unwrap();
        let Requirement::Proposition(written) = &reparsed.theorem_definitions()[0].requires()[0]
        else {
            panic!("requirement")
        };
        let restored = lower(written);
        assert_eq!(restored, original, "{expression} => {text}");
    }
}

#[test]
fn unified_certificate_terms_raise_and_lower_by_identity() {
    use crate::kernel::{KernelIntegerOperator as Op, KernelTerm, KernelType};
    use crate::surface::lowering::lower_surface_integer_term;
    let variable = Variable(99003);
    let a = KernelTerm::variable(KernelType::Integer, variable);
    let names = BTreeMap::from([(variable, "a".into())]);
    let bindings = crate::persistent::PersistentMap::default().with_inserted(
        "a".into(),
        crate::kernel::SpecIntegerExpression::Term(crate::kernel::IntegerTerm::Variable(variable)),
    );
    let one = KernelTerm::integer_literal(1.into());
    for op in [Op::Add, Op::Subtract, Op::Multiply, Op::Negate] {
        let children = if op == Op::Negate {
            vec![a.clone()]
        } else {
            vec![a.clone(), one.clone()]
        };
        let term = KernelTerm::integer_operation(op, children).unwrap();
        let surface = raise_kernel_term(
            &term,
            ParameterBinding::default(),
            &ExecutionState::new(),
            &names,
        )
        .unwrap();
        assert_eq!(
            lower_surface_integer_term(&surface, &bindings).unwrap(),
            term
        );
    }
}

#[test]
fn shared_scalar_load_raises_and_relowers_to_the_same_read_node() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer {
        block: PointerBlock::Concrete("shared-read-round-trip".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_memory(Memory::new().with_block("shared-read-round-trip", 4))
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        );
    let raw = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(state.memory()),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let (_, descriptor) = crate::kernel::load_variable_for_term(&raw).unwrap();
    let root =
        crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, &descriptor);
    assert!(matches!(
        root.node(),
        crate::kernel::KernelTermNode::MemoryLoad { .. }
    ));
    let surface = raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new())
        .expect("read spelling");
    let claim = ClickProposition::Comparison {
        left: surface,
        operator: ComparisonOperator::LessEqual,
        right: ContractExpression::IntegerLiteral("20".into()),
    };
    let lowered = relower_written_proposition(&claim, &state).unwrap();
    let Proposition::ConditionIs(ConditionTerm::Compare { left, .. }, true) = lowered else {
        panic!("read comparison")
    };
    // Both native lowering and checker observations enter the same structural
    // boundary; the test needs no special registered-name conversion.
    assert_eq!(
        crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, &left),
        root
    );
    assert_eq!(
        crate::kernel::KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, &left),
        Some(root)
    );
}

#[test]
fn volatile_read_event_results_raise_and_lower_exactly() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new();
    let values = [
        ProgramValue::Int32(MachineTerm::Variable(Variable(762001))),
        ProgramValue::typed_pointer(
            Pointer::symbolic(Variable(762002)),
            ProgramType::Int32Pointer,
        ),
    ];
    let mut points = RecordedStates::new();
    points.record_read_event_values(3, values.iter());
    let _points = SynthesisRecordedPointsScope::enter(&points);
    for (event, value) in values.iter().enumerate() {
        let expression = synthesize_surface_value(value, ParameterBinding::default(), &state)
            .expect("event result spelling");
        let expected = ContractExpression::RegionResult(CodeRegionRef::Path(vec![
            SourcePathStep::Region(3),
            SourcePathStep::ReadEvent(event),
        ]));
        assert_eq!(expression, expected);
        let text = diagnostics::describe_contract_expression(&expression);
        assert_eq!(text, format!("region(3).read_event({event}).result"));
        let parsed = parser::parse(&format!(
            "theorem observed() {{ requires {text} == {text}; ensures true; }}"
        ))
        .unwrap();
        let Requirement::Proposition(claim) = &parsed.theorem_definitions()[0].requires()[0] else {
            panic!("parsed comparison");
        };
        assert_eq!(
            claim,
            &ClickProposition::Comparison {
                left: expected.clone(),
                operator: ComparisonOperator::Equal,
                right: expected,
            }
        );
        let lowered = relower_written_proposition_with_states(claim, &state, &state, &points)
            .expect("event result lowers");
        assert_eq!(
            points
                .region_result_value(&CodeRegionRef::Path(vec![
                    SourcePathStep::Region(3),
                    SourcePathStep::ReadEvent(event)
                ]))
                .unwrap(),
            *value
        );
        let expected = match value {
            ProgramValue::Int32(term) => Proposition::ConditionIs(
                ConditionTerm::Compare {
                    format: crate::kernel::MachineIntegerType::Int32,
                    relation: crate::kernel::CompareRelation::Equal,
                    left: Box::new(term.clone()),
                    right: Box::new(term.clone()),
                },
                true,
            ),
            ProgramValue::Pointer(pointer) => Proposition::ConditionIs(
                ConditionTerm::pointer_equal(pointer.pointer().clone(), pointer.pointer().clone()),
                true,
            ),
            _ => unreachable!(),
        };
        assert_eq!(lowered, expected);
    }
}

#[test]
fn volatile_read_event_results_follow_state_branches() {
    let point = ProgramPointRef {
        region: CodeRegionRef::Region(3),
        kind: ProgramPointKind::Exit,
    };
    let old = ProgramValue::Int32(MachineTerm::Variable(Variable(762010)));
    let next = ProgramValue::Int32(MachineTerm::Variable(Variable(762011)));
    let mut ancestor = RecordedStates::new();
    ancestor.insert(point.clone(), ExecutionState::new());
    ancestor.record_read_event_values(3, std::iter::once(&old));
    let mut left = ancestor.clone();
    left.insert(point.clone(), ExecutionState::new());
    left.record_read_event_values(3, std::iter::once(&next));
    let mut right = ancestor.clone();
    right.insert(point, ExecutionState::new());
    right.record_read_event_values(3, std::iter::once(&next));
    let joined = left.common_descendant(&right, &ancestor).unwrap();
    assert_eq!(
        joined
            .region_result_value(&CodeRegionRef::Region(3))
            .unwrap(),
        next
    );
    assert!(joined.read_event_naming_value(&old).is_none());
    right.record_read_event_values(3, std::iter::once(&old));
    let disagreed = left.common_descendant(&right, &ancestor).unwrap();
    assert!(
        disagreed
            .region_result_value(&CodeRegionRef::Region(3))
            .is_err()
    );
    left.retain(|_, _| true);
    assert_eq!(
        left.region_result_value(&CodeRegionRef::Region(3)).unwrap(),
        next
    );
    left.retain(|_, _| false);
    assert!(left.region_result_value(&CodeRegionRef::Region(3)).is_err());
    assert_eq!(
        ancestor
            .region_result_value(&CodeRegionRef::Region(3))
            .unwrap(),
        old
    );
}

#[test]
fn shared_arithmetic_raising_does_not_export_operand_trees() {
    use crate::kernel::{KernelTermExport, KernelTermImport};
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(993401);
    let native = MachineTerm::logical_machine_binary(
        MachineIntegerType::Int32,
        MachineBinaryOp::Add,
        MachineTerm::Variable(variable),
        MachineTerm::constant(1),
    );
    let root = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
    let state =
        ExecutionState::new().with_local("x", ProgramValue::Int32(MachineTerm::Variable(variable)));
    let named_state = state
        .clone()
        .with_local("current", ProgramValue::Int32(native.clone()));
    let named_exports = KernelTermExport::machine_export_count();
    assert_eq!(
        raise_kernel_term(
            &root,
            ParameterBinding::default(),
            &named_state,
            &BTreeMap::new()
        )
        .unwrap(),
        SurfaceTerm::ProgramExpression(ProgramExpression::Variable("current".into())),
        "a current local must be named before spelling its historical operands",
    );
    assert_eq!(KernelTermExport::machine_export_count(), named_exports);
    // Both roots and immediate child tags collide in the local-name index.
    // Exact matching must reject the earlier name before using the true holder.
    let outer = |value| {
        MachineTerm::logical_machine_binary(
            MachineIntegerType::Int32,
            MachineBinaryOp::Add,
            value,
            MachineTerm::constant(1),
        )
    };
    let nested = outer(native.clone());
    let nested_root = KernelTermImport::default().machine(MachineIntegerType::Int32, &nested);
    let collision_state = named_state
        .with_local(
            "a_collision",
            ProgramValue::Int32(outer(outer(MachineTerm::Variable(Variable(993499))))),
        )
        .with_local("current_nested", ProgramValue::Int32(nested));
    assert_eq!(
        raise_kernel_term(
            &nested_root,
            ParameterBinding::default(),
            &collision_state,
            &BTreeMap::new()
        )
        .unwrap(),
        SurfaceTerm::ProgramExpression(ProgramExpression::Variable("current_nested".into())),
    );
    assert_eq!(KernelTermExport::machine_export_count(), named_exports);
    let exports = KernelTermExport::machine_export_count();
    let surface =
        raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new()).unwrap();
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    let written = ClickProposition::Comparison {
        left: surface,
        operator: ComparisonOperator::LessEqual,
        right: SurfaceTerm::ProgramExpression(ProgramExpression::Value(int32(20))),
    };
    let lowered = relower_written_proposition(&written, &state).unwrap();
    let Proposition::ConditionIs(condition, true) = lowered else {
        panic!("comparison")
    };
    let view =
        crate::kernel::machine_integer::comparison::structural_comparison_view(&condition).unwrap();
    assert_eq!(view.format, MachineIntegerType::Int32);
    assert_eq!(view.relation, crate::kernel::CompareRelation::LessEqual);
    assert_eq!(
        crate::kernel::KernelTerm::retained_machine_operand(
            view.format,
            view.operands[0].operand_view()
        ),
        root
    );
    assert_eq!(KernelTermExport::machine_export_count(), exports);
}

#[test]
fn common_machine_calls_round_trip_source_with_nested_arguments_and_casts() {
    check_common_machine_call_formats(&[
        (MachineIntegerType::Int32, "int32"),
        (MachineIntegerType::UInt32, "uint32"),
        (MachineIntegerType::Int64, "int64"),
        (MachineIntegerType::UInt64, "uint64"),
    ]);
}

#[test]
#[ignore = "nightly: complete ten-format call reconstruction sweep"]
fn common_machine_calls_round_trip_source_with_all_native_formats() {
    check_common_machine_call_formats(&[
        (MachineIntegerType::Int8, "int8"),
        (MachineIntegerType::UInt8, "uint8"),
        (MachineIntegerType::Int16, "int16"),
        (MachineIntegerType::UInt16, "uint16"),
        (MachineIntegerType::Int32, "int32"),
        (MachineIntegerType::UInt32, "uint32"),
        (MachineIntegerType::Int64, "int64"),
        (MachineIntegerType::UInt64, "uint64"),
        (MachineIntegerType::Int128, "int128"),
        (MachineIntegerType::UInt128, "uint128"),
    ]);
}

fn check_common_machine_call_formats(formats: &[(MachineIntegerType, &str)]) {
    use crate::kernel::{KernelTermExport, KernelTermImport, KernelTermNode, PureFunctionArgument};
    for &(format, spelling) in formats {
        let _session = crate::kernel::VerificationSession::enter();
        let declarations = format!(
            "function inner(x: int32) -> int32 {{ x }} function outer(x: int32) -> {spelling} {{ x as {spelling} }}"
        );
        let file = parser::parse(&declarations).unwrap();
        let variable = ProgramValue::Int32(MachineTerm::Variable(Variable(995900)));
        let state = ExecutionState::new().with_local("x", variable.clone());
        let values = BTreeMap::from([("x".to_string(), variable)]);
        let parse_expression = |text: &str, result_type: &str| {
            let parsed = parser::parse(&format!(
                "{declarations} function probe(x: int32) -> {result_type} {{ {text} }}"
            ))
            .unwrap();
            parsed
                .click_function_definitions()
                .last()
                .unwrap()
                .body()
                .unwrap()
                .clone()
        };
        let lower = |expression: &SurfaceTerm| {
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                expression,
                BTreeMap::new(),
                &state,
                values.clone(),
                values.clone(),
                None,
                &RecordedStates::new(),
                SpecDefinitions::new(
                    &PredicateEnvironment::new(&[]),
                    &ClickFunctionEnvironment::new(file.click_function_definitions()),
                ),
                BTreeSet::new(),
                BTreeMap::new(),
            )
            .unwrap_or_else(|error| {
                panic!(
                    "{spelling}: {}: {error}",
                    diagnostics::describe_contract_expression(expression)
                )
            });
            let (value, _) =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &spec,
                    Some(&state),
                    &PureFactContext::new(),
                )
                .unwrap();
            KernelTermImport::default().argument(&PureFunctionArgument::Value(value))
        };
        let mut expressions = vec![
            ("outer(x)", spelling),
            ("outer(inner(x))", spelling),
            ("outer(inner(x + 1))", spelling),
        ];
        if format.format().bits() <= 64 {
            expressions.push(("outer(x) as int64", "int64"));
            expressions.push(("(outer(inner(x)) as uint64) + 1u64", "uint64"));
        }
        for (expression, result_type) in expressions {
            let root = lower(&parse_expression(expression, result_type));
            let mut pending = vec![&root];
            let mut calls = 0;
            while let Some(node) = pending.pop() {
                if matches!(node.node(), KernelTermNode::Call { .. }) {
                    calls += 1;
                }
                pending.extend(node.children());
            }
            assert!(calls > 0, "{spelling}: {expression}");
            let exports = KernelTermExport::machine_export_count();
            let surface =
                raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new())
                    .unwrap();
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            let text = diagnostics::describe_contract_expression(&surface);
            let restored = lower(&parse_expression(&text, result_type));
            assert_eq!(restored, root, "{spelling}: {expression} => {text}");
            if format.format().bits() == 32 && expression.contains(" as ") {
                let legacy = KernelTermExport::machine(&root).unwrap();
                let surface = synthesize_surface_bitvector(
                    &legacy,
                    ParameterBinding::default(),
                    &state,
                    &BTreeMap::new(),
                )
                .unwrap_or_else(|| panic!("legacy cast: {expression}"));
                let text = diagnostics::describe_contract_expression(&surface);
                let restored = lower(&parse_expression(&text, result_type));
                assert_eq!(restored, root, "legacy cast: {expression} => {text}");
            }
        }
    }
}

#[test]
fn range_fold_surface_preserves_scope_and_alpha_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new()
        .with_local(
            "n",
            ProgramValue::Int32(MachineTerm::Variable(Variable(710003))),
        )
        .with_local(
            "__click_binder_0",
            ProgramValue::Int32(MachineTerm::Variable(Variable(710004))),
        );
    for expression in [
        "(0..n).fold(0, |acc, item| { acc })",
        "(0..n).fold(__click_binder_0, |acc, item| { item })",
        "(0..n).fold(0, |acc, item| { (0..item).fold(acc, |a, i| { a }) })",
        "(0..n).fold(to_integer(0), |acc, item| { acc })",
        "(0u64..(n as uint64)).fold(to_integer(0), |acc, item| { acc })",
        "(let lo: Integer = 0; let hi: Integer = to_integer(n); (lo..hi).fold(to_integer(0), |acc, item| { acc }))",
    ] {
        let source = format!(
            "theorem probe(n: int32, __click_binder_0: int32) {{ requires {expression} == 0; ensures true; }}"
        );
        let parsed = parser::parse(&source).unwrap();
        let Requirement::Proposition(written) = &parsed.theorem_definitions()[0].requires()[0]
        else {
            panic!()
        };
        let lowered = relower_written_proposition(written, &state)
            .unwrap_or_else(|error| panic!("{expression}: {error}"));
        let spelled = synthesize_surface_proposition(&lowered, ParameterBinding::default(), &state)
            .unwrap_or_else(|| panic!("cannot spell {expression}"));
        let text = crate::surface::printing::source_click_proposition(&spelled);
        assert!(!text.contains('\0'));
        let reparsed = parser::parse(&format!(
            "theorem probe(n: int32, __click_binder_0: int32) {{ requires {text}; ensures true; }}"
        ))
        .unwrap();
        let Requirement::Proposition(spelled) = &reparsed.theorem_definitions()[0].requires()[0]
        else {
            panic!()
        };
        assert!(
            synthesized_surface_matches_proposition(
                &spelled,
                &lowered,
                ParameterBinding::default(),
                &state
            ),
            "{expression}: {spelled:?}"
        );
    }
}

#[test]
fn range_fold_surface_separates_integer_and_machine_binder_ids() {
    use crate::kernel::{IntegerRangeFoldIndex, IntegerTerm, SharedIntegerRangeEndpoint};
    let _session = crate::kernel::VerificationSession::enter();
    let id = Variable(710005);
    let n = MachineTerm::Variable(Variable(710006));
    let state = ExecutionState::new().with_local("n", ProgramValue::Int32(n.clone()));
    let fold = IntegerTerm::RangeFold {
        index: IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
            end: SharedIntegerRangeEndpoint::intern(n),
        },
        initial: IntegerTerm::constant_i64(0).into(),
        accumulator: id,
        item: id,
        body: IntegerTerm::Add(
            IntegerTerm::Variable(id).into(),
            IntegerTerm::from_machine(MachineIntegerType::Int32, MachineTerm::Variable(id))
                .unwrap()
                .into(),
        )
        .into(),
    };
    let proposition = Proposition::ConditionIs(
        ConditionTerm::integer_equal(fold, IntegerTerm::constant_i64(0)),
        true,
    );
    let spelled =
        synthesize_surface_proposition(&proposition, ParameterBinding::default(), &state).unwrap();
    assert!(
        synthesized_surface_matches_proposition(
            &spelled,
            &proposition,
            ParameterBinding::default(),
            &state
        ),
        "{spelled:?}"
    );
    assert!(folds::binder_name(true, id).is_none());
    assert!(folds::binder_name(false, id).is_none());
}

#[test]
fn common_match_surface_preserves_written_binders_and_relowers_nested_results() {
    use crate::kernel::{AlgebraicValueType, KernelMatch};
    let _session = crate::kernel::VerificationSession::enter();
    let scrutinee =
        KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(ProgramType::Int32)]);
    let algebraic_values = BTreeMap::from([(
        "payload".to_string(),
        crate::kernel::SpecAlgebraicExpression {
            algebraic_type: scrutinee.algebraic_type.clone(),
            node: crate::kernel::SpecAlgebraicExpressionNode::Variable(Variable(991900)),
        },
    )]);
    let values = BTreeMap::from([
        (
            "payload".to_string(),
            ProgramValue::Parameter(Box::new(scrutinee.clone())),
        ),
        (
            "n".to_string(),
            ProgramValue::Int32(MachineTerm::Variable(Variable(991951))),
        ),
    ]);
    let state = ExecutionState::new()
        .with_local("payload", ProgramValue::Parameter(Box::new(scrutinee)))
        .with_local(
            "n",
            ProgramValue::Int32(MachineTerm::Variable(Variable(991951))),
        );
    let declarations = "spec enum MatchScope { Arm(int32) }
        function wrapped(x: int32) -> int32 { x }
        function keep(x: MatchScope) -> MatchScope { x }";
    for requirement in [
        "(match payload { MatchScope::Arm(item) => item }) == 0",
        "(match payload { MatchScope::Arm(item) => to_integer(item) }) == to_integer(0)",
        "(match payload { MatchScope::Arm(item) => MatchScope::Arm(item ^ 1) }) == payload",
        "(match payload { MatchScope::Arm(item) => MatchScope::Arm(item) }) == payload",
        "(match payload { MatchScope::Arm(item) => (0..n).fold(item, |acc, index| { acc }) }) == 0",
        "(0..n).fold(0, |acc, index| { match payload { MatchScope::Arm(item) => acc } }) == 0",
        "(match payload { MatchScope::Arm(item) => wrapped((0..n).fold(item, |acc, index| { wrapped(acc) })) }) == 0",
        "(0..n).fold(0, |acc, index| { wrapped(match payload { MatchScope::Arm(item) => acc ^ item }) }) == 0",
        "(match (match payload { MatchScope::Arm(item) => MatchScope::Arm(item ^ 1) }) { MatchScope::Arm(item) => MatchScope::Arm(item ^ 2) }) == payload",
        "keep(match payload { MatchScope::Arm(item) => MatchScope::Arm(wrapped(item)) }) == payload",
    ] {
        let source = format!(
            "{declarations} theorem probe(payload: MatchScope, n: int32) {{ requires {requirement}; ensures true; }}"
        );
        let file = parser::parse(&source).unwrap();
        let lower = |proposition: &ClickProposition| {
            crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
            proposition, &PureFactContext::new(), ContractEnvironment::new(&values, &BTreeMap::new()),
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::with_algebraic_types(file.click_function_definitions(), file.algebraic_type_definitions())),
            FixedStateLoweringOptions { algebraic_values: Some(&algebraic_values), ..Default::default() },
        ).unwrap().0
        };
        let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
            panic!()
        };
        let original = lower(written);
        let spelled =
            synthesize_surface_proposition(&original, ParameterBinding::default(), &state)
                .unwrap_or_else(|| panic!("match spelling: {original:?}"));
        let text = crate::surface::printing::source_click_proposition(&spelled);
        if text.contains("match ") {
            assert!(text.contains("Arm(item)"), "{requirement}: {text}");
        }
        assert!(!text.contains('\0'));
        let parsed = parser::parse(&format!(
        "{declarations} theorem probe(payload: MatchScope, n: int32) {{ requires {text}; ensures true; }}"
    ))
    .unwrap();
        let Requirement::Proposition(written) = &parsed.theorem_definitions()[0].requires()[0]
        else {
            panic!()
        };
        let repeated = lower(written);
        assert!(
            crate::kernel::proof::propositions_are_alpha_equal(&original, &repeated),
            "{original:?} vs {repeated:?}"
        );
    }
}

#[test]
fn common_pointer_calls_round_trip_nested_source_calls() {
    use crate::kernel::{
        KernelTerm, KernelTermImport, PointerBlock, PointerValue, PureFunctionArgument,
        SharedPointerValue,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let declarations = "function select(p: int32*) -> int32* { p }";
    let file = parser::parse(declarations).unwrap();
    let input = ProgramValue::Pointer(PointerValue::new(
        Pointer::symbolic(Variable(1025900)),
        ProgramType::Int32Pointer,
    ));
    let state = ExecutionState::new().with_local("p", input.clone());
    let values = BTreeMap::from([("p".to_string(), input)]);
    let lower = |expression: &SurfaceTerm| {
        let spec = crate::surface::lowering::elaborate_fixed_state_expression(
            expression,
            BTreeMap::new(),
            &state,
            values.clone(),
            values.clone(),
            None,
            &RecordedStates::new(),
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(file.click_function_definitions()),
            ),
            BTreeSet::new(),
            BTreeMap::new(),
        )
        .unwrap();
        crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
            &state,
            &spec,
            Some(&state),
            &PureFactContext::new(),
        )
        .unwrap()
        .0
    };
    for text in ["select(p)", "select(select(p))"] {
        let source = parser::parse(&format!(
            "{declarations} function probe(p: int32*) -> int32* {{ {text} }}"
        ))
        .unwrap();
        let expression = source
            .click_function_definitions()
            .last()
            .unwrap()
            .body()
            .unwrap();
        let expected = lower(expression);
        let ProgramValue::Pointer(pointer) = &expected else {
            panic!("pointer")
        };
        // Reconstruct the same nested common roots that the producer test
        // checks, keeping inner calls as children rather than exporting them.
        fn common(pointer: &PointerValue) -> KernelTerm {
            let value = SharedPointerValue::import(pointer);
            let PointerBlock::PureFunctionApplication(application) = &pointer.block else {
                return KernelTerm::shared_pointer_value(value);
            };
            let arguments = application
                .arguments()
                .iter()
                .map(|argument| match argument {
                    PureFunctionArgument::Value(ProgramValue::Pointer(pointer)) => {
                        Some(common(pointer))
                    }
                    PureFunctionArgument::ArrayRef {
                        memory,
                        pointer: ProgramValue::Pointer(pointer),
                        element_type,
                    } => Some(KernelTerm::shared_array_reference(
                        crate::kernel::intern_memory_ref(memory),
                        common(pointer),
                        *element_type,
                    )),
                    _ => None,
                })
                .collect();
            KernelTermImport::default().pointer_call(application, arguments, value)
        }
        let root = common(pointer);
        let names = values
            .iter()
            .map(|(name, value)| (value.clone(), name.clone()))
            .collect();
        let raised = with_proof_local_value_names(names, || {
            raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new())
        })
        .unwrap_or_else(|| panic!("could not raise {text}"));
        assert_eq!(lower(&raised), expected, "{raised:?}");
    }
}

#[test]
fn typed_word_reads_round_trip_their_observation_without_a_sign_cast() {
    use crate::kernel::{IntegerTerm, PointerValue};
    for (format, name) in [
        (MachineIntegerType::Int64, "load_int64"),
        (MachineIntegerType::UInt64, "load_uint64"),
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(981_200));
        let memory = Memory::new().with_block("word-read-source", 8);
        let state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_local(
                "p",
                ProgramValue::Pointer(PointerValue::new(
                    pointer.clone(),
                    ProgramType::UInt64Pointer,
                )),
            );
        let read = crate::kernel::canonical_form_of_load(
            crate::kernel::intern_memory(memory),
            pointer,
            crate::kernel::LoadKind::Bits64,
        );
        let value = IntegerTerm::from_machine(format, read).unwrap();
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerLessThan(value.into(), IntegerTerm::constant_i64(1).into()),
            true,
        );
        let spelled =
            synthesize_surface_proposition(&goal, ParameterBinding::default(), &state).unwrap();
        let source = crate::surface::printing::source_click_proposition(&spelled);
        assert!(source.contains(name), "{source}");
        let lowered = relower_written_proposition(&spelled, &state).unwrap();
        assert!(
            crate::surface::proof::smart_closures::propositions_match_after_canonical_loads(
                &lowered, &goal
            ),
            "{source}\n{lowered:?}\n{goal:?}"
        );
    }
}

#[test]
fn float_bit_literals_round_trip_exact_native_values() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut values = Vec::new();
    for bits in [
        0, 0x80000000, 0x3f800000, 1, 0x007fffff, 0x7f800000, 0xff800000, 0x7fc00001, 0x7f800123,
        0xffc12345,
    ] {
        values.push(ProgramValue::Float32(MachineTerm::constant(bits)));
        values.push(ProgramValue::Float32(MachineTerm::uint32_constant(bits)));
    }
    for bits in [
        0,
        0x8000000000000000,
        0x3ff0000000000000,
        1,
        0x000fffffffffffff,
        0x7ff0000000000000,
        0xfff0000000000000,
        0x7ff8000000000001,
        0x7ff0000000000123,
        0xfff8123456789abc,
    ] {
        values.push(ProgramValue::Float64(MachineTerm::uint64_constant(bits)));
    }
    for value in values {
        let state = ExecutionState::new();
        let surface =
            synthesize_surface_value(&value, ParameterBinding::default(), &state).unwrap();
        let text = diagnostics::describe_contract_expression(&surface);
        assert!(text.starts_with("float32_from_bits(") || text.starts_with("float64_from_bits("));
        for rust in [false, true] {
            let prefix = if rust { "verifying \"bits.rs\";" } else { "" };
            let ty = match (&value, rust) {
                (ProgramValue::Float32(_), false) => "float",
                (ProgramValue::Float32(_), true) => "f32",
                (_, false) => "double",
                (_, true) => "f64",
            };
            let file =
                parser::parse(&format!("{prefix} function probe() -> {ty} {{ {text} }}")).unwrap();
            let expression = file.click_function_definitions()[0].body().unwrap();
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                expression,
                BTreeMap::new(),
                &state,
                BTreeMap::new(),
                BTreeMap::new(),
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
            let (restored, obligations) =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &spec,
                    Some(&state),
                    &PureFactContext::new(),
                )
                .unwrap();
            assert_eq!(restored, value, "{text}, rust={rust}");
            assert!(obligations.is_empty());
        }
    }
}

#[test]
fn float_bit_literals_refuse_wrong_widths_expressions_and_arity() {
    for expression in [
        "float32_from_bits()",
        "float32_from_bits(1, 2)",
        "float32_from_bits(x)",
        "float32_from_bits(1 + 2)",
        "float32_from_bits(-1)",
        "float32_from_bits(4294967296)",
        "float32_from_bits(1u64)",
        "float32_from_bits(1u8)",
        "float64_from_bits(1u32)",
        "float64_from_bits(18446744073709551616)",
    ] {
        let error = parser::parse(&format!("function probe() -> float {{ {expression} }}"))
            .expect_err(expression);
        assert!(
            error.message().contains("from_bits"),
            "{expression}: {error:?}"
        );
    }
    // The local allowance for hexadecimal bit patterns must not change the
    // ordinary literal grammar of a C/default Click file.
    assert!(parser::parse("function probe() -> uint32 { 0xffu32 }").is_err());
}

#[test]
fn common_float_atoms_round_trip_printed_surface_bits() {
    let _session = crate::kernel::VerificationSession::enter();
    let values = [
        ProgramValue::Float32(MachineTerm::Variable(Variable(999804))),
        ProgramValue::Float64(MachineTerm::Variable(Variable(999805))),
        ProgramValue::Float32(MachineTerm::constant(0x80000000)),
        ProgramValue::Float32(MachineTerm::uint32_constant(0x7f800123)),
        ProgramValue::Float64(MachineTerm::uint64_constant(0x8000000000000000)),
        ProgramValue::Float64(MachineTerm::uint64_constant(0x7ff8000000000123)),
    ];
    for value in values {
        let named = matches!(
            &value,
            ProgramValue::Float32(MachineTerm::Variable(_))
                | ProgramValue::Float64(MachineTerm::Variable(_))
        );
        let values = if named {
            BTreeMap::from([("value".to_string(), value.clone())])
        } else {
            BTreeMap::new()
        };
        let state = ExecutionState::new();
        // Scoped float binders already have their source names. Execution-local
        // name/storage handoffs are the later 8aa boundary.
        let bindings = match &value {
            ProgramValue::Float32(MachineTerm::Variable(variable))
            | ProgramValue::Float64(MachineTerm::Variable(variable)) => {
                BTreeMap::from([(*variable, "value".to_string())])
            }
            _ => BTreeMap::new(),
        };
        let root = crate::kernel::KernelTermImport::default()
            .argument(&crate::kernel::PureFunctionArgument::Value(value.clone()));
        let surface =
            raise_kernel_term(&root, ParameterBinding::default(), &state, &bindings).unwrap();
        let text = diagnostics::describe_contract_expression(&surface);
        assert!(
            text == "value"
                || text.starts_with("float32_from_bits(")
                || text.starts_with("float64_from_bits(")
        );
        for rust in [false, true] {
            let prefix = if rust { "verifying \"bits.rs\";" } else { "" };
            let ty = match (&value, rust) {
                (ProgramValue::Float32(_), false) => "float",
                (ProgramValue::Float32(_), true) => "f32",
                (_, false) => "double",
                (_, true) => "f64",
            };
            let file = parser::parse(&format!(
                "{prefix} function probe(value: {ty}) -> {ty} {{ {text} }}"
            ))
            .unwrap();
            let expression = file.click_function_definitions()[0].body().unwrap();
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                expression,
                BTreeMap::new(),
                &state,
                values.clone(),
                values.clone(),
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
            let (restored, obligations) =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &spec,
                    Some(&state),
                    &PureFactContext::new(),
                )
                .unwrap();
            assert_eq!(restored, value, "{text}, rust={rust}");
            assert_eq!(
                crate::kernel::KernelTermImport::default()
                    .argument(&crate::kernel::PureFunctionArgument::Value(restored)),
                root
            );
            assert!(obligations.is_empty());
        }
    }
}
