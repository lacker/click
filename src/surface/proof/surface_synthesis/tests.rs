use super::*;

/// Lowers a written proposition exactly as a `have` in a fixed-state proof
/// does, so a synthesized spelling is accepted only when it re-lowers to the
/// proposition it was synthesized from.
fn relower_written_proposition(
    surface: &ClickProposition,
    state: &CState,
) -> Result<Proposition, String> {
    relower_written_proposition_with_snapshots(surface, state, state, &RecordedSnapshots::default())
}

fn relower_written_proposition_with_snapshots(
    surface: &ClickProposition,
    pre_state: &CState,
    state: &CState,
    recorded_snapshots: &RecordedSnapshots,
) -> Result<Proposition, String> {
    crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_through_kernel_with_opaque_calls(
        surface,
        &PureFactContext::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        pre_state,
        state,
        None,
        recorded_snapshots,
        &PredicateEnvironment::new(&[]),
        &ClickFunctionEnvironment::new(&[]),
        &std::collections::BTreeSet::new(),
    )
}

/// One cell of a foreign static or file-scope object, spelled the way a
/// caller's own contract writes it: the qualified name under the source
/// alias, then the flat cell index used by the caller-side resource range.
fn qualified_cell(name: &str, base: &CValue, index: i32) -> ContractExpression {
    ContractExpression::Index(
        Box::new(ContractExpression::QualifiedC {
            name: name.to_string(),
            lowered: CExpression::Value(base.clone()),
        }),
        Box::new(ContractExpression::IntegerLiteral(index.to_string())),
    )
}

fn qualified_multidimensional_cell(
    name: &str,
    base: &CValue,
    row: i32,
    column: i32,
    columns: i32,
) -> ContractExpression {
    let flat_index = row * columns + column;
    ContractExpression::ArrayIndex {
        base: Box::new(ContractExpression::QualifiedC {
            name: name.to_string(),
            lowered: CExpression::Value(base.clone()),
        }),
        indexes: vec![
            CExpression::Value(int32(row as u32)),
            CExpression::Value(int32(column as u32)),
        ],
        lowered: CExpression::Index(
            Box::new(CExpression::Value(base.clone())),
            Box::new(CExpression::Value(int32(flat_index as u32))),
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
) -> (CState, SurfacePropositionMap, Vec<Bitvector32Term>) {
    let state = CState::new()
        .with_memory(CMemory::new().with_block(block, 4 * u32::try_from(cells).unwrap()));
    let base = CValue::typed_pointer(
        Pointer {
            block: PointerBlock::Concrete(block.into()),
            offset: PointerOffsetTerm::Constant(0),
        },
        CType::Int32Pointer,
    );
    let mut sources = SurfacePropositionMap::default();
    let loads = (0..cells)
        .map(|index| {
            let written = ClickProposition::Comparison {
                left: qualified_cell(name, &base, index),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(5))),
            };
            let lowered = relower_written_proposition(&written, &state)
                .expect("a qualified cell comparison lowers at a state holding the object");
            sources
                .record_lowering(&written, &lowered)
                .expect("the comparison lowers to matching logical structure");
            // The load term as lowering produced it: a registered load
            // variable, one of the two forms an emitted requirement carries.
            let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(load, _), _) = lowered
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
fn cells_within_bounds(loads: &[Bitvector32Term]) -> Proposition {
    let clauses = loads.iter().flat_map(|load| {
        [
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterThan(
                    Box::new(load.clone()),
                    Box::new(Bitvector32Term::Constant((-1000i32) as u32)),
                ),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(load.clone()),
                    Box::new(Bitvector32Term::Constant(1000)),
                ),
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
    state: &CState,
) -> Option<ClickProposition> {
    let _sources = QualifiedSynthesisScope::enter(sources);
    let _budget = SurfaceSynthesisScope::enter();
    synthesize_surface_proposition(proposition, &[], &[], state)
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
    let state = CState::new().with_memory(CMemory::new().with_block(block, 12));
    let base = CValue::typed_pointer(
        Pointer {
            block: PointerBlock::Concrete(block.into()),
            offset: PointerOffsetTerm::Constant(0),
        },
        CType::Int32Pointer,
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
        right: ContractExpression::CFragment(CExpression::Value(int32(5))),
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
    let lowered = CExpression::Index(
        Box::new(CExpression::Variable("grid".into())),
        Box::new(CExpression::Variable("column".into())),
    );
    let local = ContractExpression::ArrayIndex {
        base: Box::new(ContractExpression::CFragment(CExpression::Variable(
            "grid".into(),
        ))),
        indexes: vec![CExpression::Variable("row".into())],
        lowered: lowered.clone(),
    };
    assert!(contract_expression_mentions_c_local(
        &local,
        &BTreeSet::from(["grid", "column"]),
    ));
    assert!(contract_expression_mentions_c_local(
        &local,
        &BTreeSet::from(["row", "column"]),
    ));

    let qualified = ContractExpression::ArrayIndex {
        base: Box::new(ContractExpression::QualifiedC {
            name: "static_local::f::grid".into(),
            lowered: CExpression::Value(int32(0)),
        }),
        indexes: vec![CExpression::Value(int32(0))],
        lowered: CExpression::Index(
            Box::new(CExpression::Variable("global_grid".into())),
            Box::new(CExpression::Value(int32(0))),
        ),
    };
    assert!(!contract_expression_mentions_c_local(
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

/// `static_array_parity_scalar`, `static_array_parity_multidimensional`,
/// `static_array_parity_fixed_multidimensional`, and `static_local_arrays`
/// all call `increment_twice`, whose precondition bounds the three cells of
/// its own `static int32 values[3]`. The three array declarations differ
/// only in the C shape; the object, the emitted requirement, and the
/// caller's flattened qualified spelling are the same.
#[test]
fn static_local_array_call_requirements_are_spellable() {
    assert_foreign_object_requirement_is_spellable(
        "static:increment_twice:values#static0",
        "static_local::increment_twice::values",
        3,
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
fn external_byte_range_caller() -> (Vec<syntax::C0Parameter>, Vec<CExpression>, CState) {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
            byte_width: 1,
        },
    };
    let pointer = CValue::typed_pointer(pointer, CType::UInt8Pointer);
    let length = CValue::Int32(Bitvector32Term::Variable(Variable(1)));
    let parameters = vec![
        syntax::C0Parameter::new(C0Type::UInt8Pointer, "bytes".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32, "len".to_string(), None),
    ];
    let arguments = vec![
        CExpression::Value(pointer.clone()),
        CExpression::Value(length.clone()),
    ];
    let state = CState::new()
        .with_local("bytes", pointer)
        .with_local("len", length);
    (parameters, arguments, state)
}

/// The `forall_loadable_range` call requirement as the kernel emits it:
/// every in-range byte of an external-argument pointer is loadable, its byte
/// count left as the written `(k + 1) - k`.
fn external_byte_range_requirement(binder: Variable, length: &Bitvector32Term) -> Proposition {
    let index = Bitvector32Term::Variable(binder);
    Proposition::ForAll {
        var: binder,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessEqual(
                        Box::new(Bitvector32Term::Constant(0)),
                        Box::new(index.clone()),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(
                        Box::new(index.clone()),
                        Box::new(length.clone()),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::CMemoryLoadable {
                memory: CMemory::new(),
                base: Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::Add(
                        Box::new(PointerOffsetTerm::Int32Scaled {
                            value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                            byte_width: 1,
                        }),
                        Box::new(PointerOffsetTerm::Int32Scaled {
                            value: Box::new(index.clone()),
                            byte_width: 1,
                        }),
                    ),
                },
                bytes: Bitvector32Term::Subtract(
                    Box::new(Bitvector32Term::Add(
                        Box::new(index.clone()),
                        Box::new(Bitvector32Term::Constant(1)),
                    )),
                    Box::new(index),
                ),
            }),
        )),
    }
}

fn external_symbolic_element_context(
    memory: CMemory,
) -> (Vec<syntax::C0Parameter>, Vec<CExpression>, CState) {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
            byte_width: 1,
        },
    };
    let pointer = CValue::typed_pointer(pointer, CType::UInt8Pointer);
    let index = CValue::Int32(Bitvector32Term::Variable(Variable(100_001)));
    let parameters = vec![
        syntax::C0Parameter::new(C0Type::UInt8Pointer, "bytes".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32, "index".to_string(), None),
    ];
    let arguments = vec![
        CExpression::Value(pointer.clone()),
        CExpression::Value(index.clone()),
    ];
    let state = CState::new()
        .with_memory(memory)
        .with_local("bytes", pointer)
        .with_local("index", index);
    (parameters, arguments, state)
}

fn external_symbolic_element_requirement(memory: CMemory, index: Variable) -> Proposition {
    external_symbolic_element_requirement_term(memory, Bitvector32Term::Variable(index))
}

fn external_symbolic_element_requirement_term(
    memory: CMemory,
    index: Bitvector32Term,
) -> Proposition {
    Proposition::CMemoryLoadable {
        memory,
        base: Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                    byte_width: 1,
                }),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(index.clone()),
                    byte_width: 1,
                }),
            ),
        },
        bytes: Bitvector32Term::Subtract(
            Box::new(Bitvector32Term::Add(
                Box::new(index.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            )),
            Box::new(index),
        ),
    }
}

fn external_symbolic_element_constant_byte_requirement(
    memory: CMemory,
    index: Variable,
) -> Proposition {
    let mut requirement = external_symbolic_element_requirement(memory, index);
    let Proposition::CMemoryLoadable { bytes, .. } = &mut requirement else {
        unreachable!();
    };
    *bytes = Bitvector32Term::Constant(1);
    requirement
}

/// The unresolved `strlen` carrier: an existential length whose successor is
/// defined, followed by a guarded universal one-byte loadability range. The
/// caller's outer `loadable(bytes[0..len + 1])` fact is a separate premise;
/// this regression targets the quantified `k` carrier that retains `1`.
fn full_external_guarded_range_surface() -> ClickProposition {
    let length = ContractExpression::CFragment(CExpression::Variable("__click_q0".into()));
    let index = ContractExpression::CFragment(CExpression::Variable("__click_q1".into()));
    let quantified_range = ClickProposition::Loadable {
        segment: ContractSegment {
            state: ContractSegmentState::Current,
            base: CExpression::Variable("bytes".into()),
            start: CExpression::Variable("__click_q1".into()),
            end: CExpression::Add(
                Box::new(CExpression::Variable("__click_q1".into())),
                Box::new(CExpression::Value(int32(1))),
            ),
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::CFragment(CExpression::Variable("bytes".into())),
                start: index.clone(),
                end: ContractExpression::Add(
                    Box::new(index.clone()),
                    Box::new(ContractExpression::CFragment(CExpression::Value(int32(1)))),
                ),
            },
        },
    };
    let all_before_loadable = ClickProposition::ForAll {
        click_type: ClickType::C(C0Type::Int32),
        name: "__click_q1".into(),
        body: Box::new(ClickProposition::Implies(
            Box::new(ClickProposition::And(
                Box::new(ClickProposition::Comparison {
                    left: index.clone(),
                    operator: ComparisonOperator::GreaterEqual,
                    right: ContractExpression::CFragment(CExpression::Value(int32(0))),
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
        click_type: ClickType::C(C0Type::Int32),
        name: "__click_q0".into(),
        body: Box::new(ClickProposition::And(
            Box::new(ClickProposition::Defined {
                expression: ContractExpression::CFragment(CExpression::Add(
                    Box::new(CExpression::Variable("__click_q0".into())),
                    Box::new(CExpression::Value(int32(1))),
                )),
            }),
            Box::new(all_before_loadable),
        )),
    }
}

fn replace_full_external_cstr_range_with_constant_byte_count(requirement: &mut Proposition) {
    fn replace(proposition: &mut Proposition, inside_forall: bool) -> bool {
        match proposition {
            Proposition::CMemoryLoadable { bytes, .. } if inside_forall => {
                *bytes = Bitvector32Term::Constant(1);
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
    let memory = CMemory::new().with_block("strlen:production-bytes", 16);
    let (parameters, concrete_arguments, state) = external_symbolic_element_context(memory.clone());
    let pointer = match &concrete_arguments[0] {
        CExpression::Value(CValue::Pointer(pointer)) => pointer.clone(),
        _ => panic!("the production-shaped argument must be a pointer"),
    };
    let arguments = vec![
        CExpression::Variable("bytes".to_string()),
        concrete_arguments[1].clone(),
    ];
    let requirement_surface = full_external_guarded_range_surface();
    let requirement = relower_written_proposition(&requirement_surface, &state)
        .expect("the production-shaped strlen requirement must lower");
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
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
    assert_eq!(state.locals().get("bytes"), Some(&CValue::Pointer(pointer)));
}

#[test]
fn full_guarded_constant_byte_requirement_with_variable_argument_round_trips() {
    let memory = CMemory::new().with_block("strlen:production-constant-bytes", 16);
    let (parameters, concrete_arguments, state) = external_symbolic_element_context(memory.clone());
    let pointer = match &concrete_arguments[0] {
        CExpression::Value(CValue::Pointer(pointer)) => pointer.clone(),
        _ => panic!("the production-shaped argument must be a pointer"),
    };
    let arguments = vec![
        CExpression::Variable("bytes".to_string()),
        concrete_arguments[1].clone(),
    ];
    let requirement_surface = full_external_guarded_range_surface();
    let mut requirement = relower_written_proposition(&requirement_surface, &state)
        .expect("the production-shaped strlen requirement must lower");
    replace_full_external_cstr_range_with_constant_byte_count(&mut requirement);
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
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
    assert_eq!(state.locals().get("bytes"), Some(&CValue::Pointer(pointer)));
}

#[test]
fn strlen_symbolic_element_range_round_trips_exactly() {
    let memory = CMemory::new().with_block("strlen:bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let requirement = external_symbolic_element_requirement(memory, Variable(100_001));
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
            .expect("strlen's reduced one-element range must be spellable")
    };
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement must remain one loadability: {synthesized:?}");
    };
    assert_eq!(segment.base, CExpression::Variable("bytes".into()));
    assert_eq!(segment.start, CExpression::Variable("index".into()));
    assert_eq!(
        segment.end,
        CExpression::Add(
            Box::new(CExpression::Variable("index".into())),
            Box::new(CExpression::Value(int32(1))),
        )
    );
    let lowered = relower_written_proposition(&synthesized, &state)
        .expect("the synthesized range must lower through the have path");
    assert_eq!(lowered, requirement);
}

#[test]
fn strlen_symbolic_element_constant_byte_range_round_trips_exactly() {
    let memory = CMemory::new().with_block("strlen:constant-symbolic-bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let requirement =
        external_symbolic_element_constant_byte_requirement(memory, Variable(100_001));
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
            .expect("a constant one-byte symbolic range must be spellable")
    };
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement must remain one loadability: {synthesized:?}");
    };
    assert_eq!(
        segment.base,
        CExpression::Add(
            Box::new(CExpression::Variable("bytes".into())),
            Box::new(CExpression::Variable("index".into())),
        )
    );
    assert_eq!(segment.start, CExpression::Value(int32(0)));
    assert_eq!(segment.end, CExpression::Value(int32(1)));
    assert_eq!(
        relower_written_proposition(&synthesized, &state),
        Ok(requirement)
    );
}

#[test]
fn strlen_symbolic_element_range_rejects_wrong_identity() {
    let memory = CMemory::new().with_block("strlen:bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());

    let wrong_base = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(Variable(100_002))),
                    byte_width: 1,
                }),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(Variable(100_001))),
                    byte_width: 1,
                }),
            ),
        },
        bytes: Bitvector32Term::Subtract(
            Box::new(Bitvector32Term::Add(
                Box::new(Bitvector32Term::Variable(Variable(100_001))),
                Box::new(Bitvector32Term::Constant(1)),
            )),
            Box::new(Bitvector32Term::Variable(Variable(100_001))),
        ),
    };
    assert!(synthesize_surface_proposition(&wrong_base, &parameters, &arguments, &state).is_none());

    let wrong_index = external_symbolic_element_requirement(memory.clone(), Variable(100_002));
    assert!(
        synthesize_surface_proposition(&wrong_index, &parameters, &arguments, &state).is_none(),
        "an index with no source binding must not be inferred from the ambient state"
    );

    let wrong_width = {
        let mut requirement =
            external_symbolic_element_requirement(memory.clone(), Variable(100_001));
        let Proposition::CMemoryLoadable { base, .. } = &mut requirement else {
            unreachable!();
        };
        base.offset = PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                byte_width: 2,
            }),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100_001))),
                byte_width: 2,
            }),
        );
        requirement
    };
    assert!(
        synthesize_surface_proposition(&wrong_width, &parameters, &arguments, &state).is_none(),
        "the element width must be the declared one-byte parameter width"
    );

    let ambient_only = external_symbolic_element_requirement(memory, Variable(100_001));
    assert!(
        synthesize_surface_proposition(&ambient_only, &[], &[], &state).is_none(),
        "a local pointer must not substitute for the producer's external parameter"
    );
}

#[test]
fn strlen_constant_element_range_falls_back_to_general_synthesis() {
    let memory = CMemory::new().with_block("strlen:constant-bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let requirement =
        external_symbolic_element_requirement_term(memory, Bitvector32Term::Constant(3));
    let synthesized = synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
        .expect("a constant reduced element must retain the historical range fallback");
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement must remain one loadability: {synthesized:?}");
    };
    assert_eq!(segment.base, CExpression::Variable("bytes".into()));
    assert_eq!(segment.start, CExpression::Value(int32(3)));
    assert_eq!(segment.end, CExpression::Value(int32(4)));
    let lowered = relower_written_proposition(&synthesized, &state)
        .expect("the historical fallback must still lower the constant range");
    let Proposition::CMemoryLoadable { base, bytes, .. } = lowered else {
        panic!("the lowered fallback must remain one loadability");
    };
    assert_eq!(bytes, Bitvector32Term::Constant(1));
    assert_eq!(
        base.offset,
        PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                byte_width: 1,
            }),
            Box::new(PointerOffsetTerm::Constant(3)),
        )
    );
}

#[test]
fn strlen_zero_based_element_range_round_trips_exactly() {
    let memory = CMemory::new().with_block("strlen:zero-based-bytes", 16);
    let (parameters, mut arguments, state) = external_symbolic_element_context(memory.clone());
    let pointer = CValue::typed_pointer(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        CType::UInt8Pointer,
    );
    arguments[0] = CExpression::Value(pointer.clone());
    let state = state.with_local("bytes", pointer);
    let mut requirement = external_symbolic_element_requirement(memory, Variable(100_001));
    let Proposition::CMemoryLoadable { base, .. } = &mut requirement else {
        unreachable!();
    };
    base.offset = PointerOffsetTerm::Int32Scaled {
        value: Box::new(Bitvector32Term::Variable(Variable(100_001))),
        byte_width: 1,
    };
    let synthesized = synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
        .expect("the canonical zero-based strlen element must be spellable");
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement must remain one loadability: {synthesized:?}");
    };
    assert_eq!(segment.base, CExpression::Variable("bytes".into()));
    assert_eq!(segment.start, CExpression::Variable("index".into()));
    assert_eq!(
        segment.end,
        CExpression::Add(
            Box::new(CExpression::Variable("index".into())),
            Box::new(CExpression::Value(int32(1))),
        )
    );
    assert_eq!(
        relower_written_proposition(&synthesized, &state),
        Ok(requirement)
    );
}

#[test]
fn non_external_named_range_still_uses_general_synthesis() {
    let memory = CMemory::new().with_block("local:elements", 8);
    let pointer = CValue::typed_pointer(
        Pointer {
            block: PointerBlock::Concrete("local:elements".into()),
            offset: PointerOffsetTerm::Constant(0),
        },
        CType::UInt8Pointer,
    );
    let start = CValue::Int32(Bitvector32Term::Variable(Variable(100_001)));
    let state = CState::new()
        .with_memory(memory.clone())
        .with_local("elements", pointer)
        .with_local("start", start);
    let requirement = Proposition::CMemoryLoadable {
        memory,
        base: Pointer {
            block: PointerBlock::Concrete("local:elements".into()),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100_001))),
                byte_width: 1,
            },
        },
        bytes: Bitvector32Term::Subtract(
            Box::new(Bitvector32Term::Add(
                Box::new(Bitvector32Term::Variable(Variable(100_001))),
                Box::new(Bitvector32Term::Constant(1)),
            )),
            Box::new(Bitvector32Term::Variable(Variable(100_001))),
        ),
    };
    let synthesized = synthesize_surface_proposition(&requirement, &[], &[], &state)
        .expect("the general named-range path must remain available for local pointers");
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the requirement should remain one loadability: {synthesized:?}");
    };
    assert_eq!(segment.base, CExpression::Variable("elements".into()));
    assert_eq!(segment.start, CExpression::Variable("start".into()));
    assert_eq!(
        segment.end,
        CExpression::Add(
            Box::new(CExpression::Variable("start".into())),
            Box::new(CExpression::Value(int32(1))),
        )
    );
    let lowered = relower_written_proposition(&synthesized, &state)
        .expect("the local named range must lower through the existing path");
    assert_eq!(lowered, requirement);
}

#[test]
fn strlen_quantified_element_range_requirement_round_trips() {
    let memory = CMemory::new().with_block("strlen:quantified-bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let binder = Variable(100_002);
    let requirement = Proposition::ForAll {
        var: binder,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedGreaterEqual(
                        Box::new(Bitvector32Term::Variable(binder)),
                        Box::new(Bitvector32Term::Constant(0)),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(
                        Box::new(Bitvector32Term::Variable(binder)),
                        Box::new(Bitvector32Term::Variable(Variable(100_001))),
                    ),
                    true,
                )),
            )),
            Box::new(external_symbolic_element_requirement(memory, binder)),
        )),
    };
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
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
    parameter_type: syntax::C0Type,
    pointer_type: CType,
    width: u32,
) -> (Vec<syntax::C0Parameter>, Vec<CExpression>, CState) {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
            byte_width: i64::from(width),
        },
    };
    let pointer = CValue::typed_pointer(pointer, pointer_type);
    let parameters = vec![syntax::C0Parameter::new(
        parameter_type,
        "elements".to_string(),
        None,
    )]
    .into_iter()
    .chain([
        syntax::C0Parameter::new(C0Type::Int32, "start".to_string(), None),
        syntax::C0Parameter::new(C0Type::Int32, "end".to_string(), None),
    ])
    .collect();
    let arguments = vec![
        CExpression::Value(pointer.clone()),
        CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(100_001)))),
        CExpression::Value(CValue::Int32(Bitvector32Term::Variable(Variable(100_002)))),
    ];
    let state = CState::new()
        .with_local("elements", pointer)
        .with_local(
            "start",
            CValue::Int32(Bitvector32Term::Variable(Variable(100_001))),
        )
        .with_local(
            "end",
            CValue::Int32(Bitvector32Term::Variable(Variable(100_002))),
        );
    (parameters, arguments, state)
}

fn external_element_range_requirement(
    width: u32,
    start: Bitvector32Term,
    end: Bitvector32Term,
) -> Proposition {
    Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                    byte_width: i64::from(width),
                }),
                Box::new(PointerOffsetTerm::Int32Scaled {
                    value: Box::new(start.clone()),
                    byte_width: i64::from(width),
                }),
            ),
        },
        bytes: Bitvector32Term::Multiply(
            Box::new(Bitvector32Term::Subtract(Box::new(end), Box::new(start))),
            Box::new(Bitvector32Term::Constant(width)),
        ),
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
    let length = Bitvector32Term::Variable(Variable(1));
    let requirement = external_byte_range_requirement(Variable(3_100_000), &length);
    let spelled = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
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
        panic!("the consequent is one loadability: {spelled:?}");
    };
    assert_eq!(segment.base, CExpression::Variable("bytes".into()));
    assert_ne!(segment.start, CExpression::Value(int32(0)));

    let lowered = relower_written_proposition(&spelled, &state)
        .expect("the synthesized range lowers at the calling state");
    let Proposition::ForAll { var, .. } = &lowered else {
        panic!("re-lowering keeps the universal: {lowered:?}");
    };
    assert_eq!(lowered, external_byte_range_requirement(*var, &length));
}

#[test]
fn named_element_ranges_preserve_nonzero_starts_and_folded_byte_counts() {
    for (parameter_type, pointer_type, width, spelling) in [
        (
            syntax::C0Type::UInt16Pointer,
            CType::UInt16Pointer,
            2,
            "uint16",
        ),
        (
            syntax::C0Type::Int32Pointer,
            CType::Int32Pointer,
            4,
            "int32",
        ),
    ] {
        let (parameters, arguments, state) =
            external_element_range_context(parameter_type, pointer_type, width);
        let requirement = external_element_range_requirement(
            width,
            Bitvector32Term::Variable(Variable(100_001)),
            Bitvector32Term::Variable(Variable(100_002)),
        );
        let synthesized = {
            let _budget = SurfaceSynthesisScope::enter();
            synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
                .expect("a named element range must be spellable")
        };
        let ClickProposition::Loadable { segment } = &synthesized else {
            panic!("the requirement should synthesize as one loadable range: {synthesized:?}");
        };
        assert_eq!(segment.base, CExpression::Variable("elements".into()));
        assert_eq!(segment.start, CExpression::Variable("start".into()));
        assert_eq!(segment.end, CExpression::Variable("end".into()));

        let source = format!(
            "int32 range_{width}({spelling}* elements, int32 start, int32 end) {{ requires loadable(elements[start..end]); ensures result == 0; }}"
        );
        let parsed = crate::surface::parse(&source).expect("the range spelling must parse");
        let Requirement::LoadableSegment { segment } = &parsed.function_blocks()[0].requires()[0]
        else {
            panic!("the parsed requirement should remain a loadable range");
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
        external_element_range_context(C0Type::Int32Pointer, CType::Int32Pointer, 4);
    let requirement = external_element_range_requirement(
        4,
        Bitvector32Term::Constant(3),
        Bitvector32Term::Constant(8),
    );
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
            .expect("a folded byte count must retain its nonzero named range")
    };
    let ClickProposition::Loadable { segment } = &synthesized else {
        panic!("the folded requirement should synthesize as one range");
    };
    assert_eq!(segment.base, CExpression::Variable("elements".into()));
    assert_eq!(segment.start, CExpression::Value(int32(3)));
    assert_eq!(segment.end, CExpression::Value(int32(8)));
    let Proposition::CMemoryLoadable { base, bytes, .. } =
        relower_written_proposition(&synthesized, &state)
            .expect("the folded named range must re-lower")
    else {
        panic!("the folded range must remain a memory-loadability requirement");
    };
    assert_eq!(bytes, Bitvector32Term::Constant(20));
    assert_eq!(
        base.offset,
        PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                byte_width: 4,
            }),
            Box::new(PointerOffsetTerm::Constant(12)),
        )
    );
}

#[test]
fn named_element_range_does_not_infer_start_from_an_unrelated_index() {
    let (parameters, arguments, state) =
        external_element_range_context(syntax::C0Type::Int32Pointer, CType::Int32Pointer, 4);
    let mut requirement = external_element_range_requirement(
        4,
        Bitvector32Term::Variable(Variable(100_001)),
        Bitvector32Term::Variable(Variable(100_002)),
    );
    let Proposition::CMemoryLoadable { base, .. } = &mut requirement else {
        unreachable!();
    };
    base.offset = PointerOffsetTerm::Add(
        Box::new(PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
            byte_width: 4,
        }),
        Box::new(PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100_003))),
            byte_width: 4,
        }),
    );
    let _budget = SurfaceSynthesisScope::enter();
    let synthesized = synthesize_surface_proposition(&requirement, &parameters, &arguments, &state);
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
    let length = Bitvector32Term::Variable(Variable(1));
    let requirement = external_byte_range_requirement(Variable(3_100_000), &length);
    let _budget = SurfaceSynthesisScope::enter();
    assert!(
        synthesize_surface_proposition(&requirement, &parameters, &arguments, &state).is_some(),
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
        sort: Sort::CInt32,
        body: Box::new(external_byte_range_requirement(
            Variable(3_100_001),
            &Bitvector32Term::Variable(witness),
        )),
    };
    let _budget = SurfaceSynthesisScope::enter();
    let spelled = synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
        .expect("the call requirement must be spellable");
    assert!(
        matches!(spelled, ClickProposition::Exists { .. }),
        "the existential is spelled as one: {spelled:?}"
    );
}

#[test]
fn function_call_synthesis_scales_with_named_arguments() {
    let state = CState::new();
    let mut previous = None;
    for size in [16, 32, 64, 128] {
        let values = vec![crate::kernel::PureFunctionArgument::Value(int32(7)); size];
        let _scope = SurfaceSynthesisScope::enter();
        let call = synthesize_surface_call("selected", &values, &[], &[], &state, &BTreeMap::new())
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
fn function_array_synthesis_requires_the_exact_named_snapshot() {
    let pointer = CValue::pointer(Pointer {
        block: PointerBlock::Concrete("array".into()),
        offset: PointerOffsetTerm::Constant(0),
    });
    let entry = CState::new().with_local("p", pointer.clone());
    let post = entry
        .clone()
        .with_memory(CMemory::new().with_block("other", 4));
    let values = [crate::kernel::PureFunctionArgument::ArrayRef {
        memory: entry.memory().clone(),
        pointer,
        element_type: CType::Int32,
    }];
    let bindings = BTreeMap::new();
    // An unnamed historical memory cannot be silently printed as current.
    assert!(synthesize_surface_call("selected", &values, &[], &[], &post, &bindings).is_none());
    let _entry = SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(entry))));
    let call = synthesize_surface_call("selected", &values, &[], &[], &post, &bindings).unwrap();
    assert!(
        matches!(call, ContractExpression::Call { arguments, .. } if matches!(arguments.as_slice(), [ContractExpression::Old(_)]))
    );
}

#[test]
fn nested_propositions_synthesize_with_small_frames_and_linear_work() {
    std::thread::Builder::new()
        .name("small-stack-proposition-synthesis".into())
        .stack_size(1024 * 1024)
        .spawn(|| {
            let state = CState::new();
            let atom = || {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Constant(7)),
                        Box::new(Bitvector32Term::Constant(7)),
                    ),
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
                    &[],
                    &[],
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
    let memory = CMemory::new().with_block("load-definition", 4);
    let state = CState::new().with_memory(memory).with_local(
        "p",
        CValue::typed_pointer(pointer.clone(), CType::Int32Pointer),
    );
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(state.memory()),
        Box::new(pointer),
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let requirement = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(variable)),
            Box::new(defining_load),
        ),
        true,
    );
    let spelled = synthesize_surface_proposition(&requirement, &[], &[], &state)
        .expect("load-defining equation must be spellable");
    assert_eq!(
        relower_written_proposition(&spelled, &state)
            .map(|fact| crate::kernel::canonical_condition_fact(&fact)),
        Ok(crate::kernel::canonical_condition_fact(&requirement)),
    );
}

#[test]
fn load_defining_equation_uses_entry_snapshot() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("load-definition-entry".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let entry = CState::new()
        .with_memory(CMemory::new().with_block("load-definition-entry", 4))
        .with_local(
            "p",
            CValue::typed_pointer(pointer.clone(), CType::Int32Pointer),
        );
    let post = entry.clone().with_memory(
        CMemory::new()
            .with_block("load-definition-entry", 4)
            .store(pointer.clone(), int32(7)),
    );
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(entry.memory()),
        Box::new(pointer),
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let entry = entry.with_local("result", CValue::Int32(Bitvector32Term::Variable(variable)));
    let requirement = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(variable)),
            Box::new(defining_load),
        ),
        true,
    );
    let spelled =
        synthesize_surface_proposition_at_entry_and_post(&requirement, &[], &[], &entry, &post)
            .expect("entry load-defining equation must be spellable");
    let ClickProposition::At {
        selector: SnapshotSelector::ProgramPoint(point),
        proposition,
    } = &spelled
    else {
        panic!("a changed post-state must retain the entry snapshot: {spelled:?}");
    };
    assert_eq!(point.region, CodeRegionRef::Function);
    assert_eq!(point.kind, ProgramPointKind::Entry);
    let ClickProposition::Comparison { left, right, .. } = proposition.as_ref() else {
        panic!("the entry snapshot must contain the defining equality: {spelled:?}");
    };
    assert_ne!(left, right, "the entry spelling must not be tautological");
    let lowered = relower_written_proposition(&spelled, &entry).unwrap();
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&lowered),
        crate::kernel::proof::proposition_identity_key(&requirement),
    );
}

#[test]
fn load_defining_equation_uses_saved_snapshot() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("load-definition-saved".into()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let base = CState::new()
        .with_memory(CMemory::new().with_block("load-definition-saved", 4))
        .with_local(
            "p",
            CValue::typed_pointer(pointer.clone(), CType::Int32Pointer),
        );
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(base.memory()),
        Box::new(pointer.clone()),
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let snapshot = base.with_local("result", CValue::Int32(Bitvector32Term::Variable(variable)));
    let entry = snapshot.clone().with_memory(
        CMemory::new()
            .with_block("load-definition-saved", 4)
            .store(pointer.clone(), int32(1)),
    );
    let post = snapshot.clone().with_memory(
        CMemory::new()
            .with_block("load-definition-saved", 4)
            .store(pointer, int32(2)),
    );
    let requirement = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(variable)),
            Box::new(defining_load),
        ),
        true,
    );
    let selector = SnapshotSelector::Mark("saved_load_epoch".into());
    let spelled = synthesize_surface_proposition_at_entry_post_and_snapshot(
        &requirement,
        &[],
        &[],
        &entry,
        &post,
        Some((&snapshot, &selector)),
    )
    .expect("the explicitly saved load snapshot must be spellable");
    let ClickProposition::At {
        selector: actual,
        proposition,
    } = &spelled
    else {
        panic!("a changed entry and post-state must use the saved snapshot: {spelled:?}");
    };
    assert_eq!(actual, &selector);
    let ClickProposition::Comparison { left, right, .. } = proposition.as_ref() else {
        panic!("the saved snapshot must contain the defining equality: {spelled:?}");
    };
    assert_ne!(left, right, "the saved spelling must not be tautological");
    let mut recorded_snapshots = RecordedSnapshots::new();
    recorded_snapshots.insert(selector, snapshot);
    let lowered =
        relower_written_proposition_with_snapshots(&spelled, &post, &post, &recorded_snapshots)
            .expect("the saved mark must lower through its recorded snapshot");
    assert_eq!(
        crate::kernel::proof::proposition_identity_key(&lowered),
        crate::kernel::proof::proposition_identity_key(&requirement),
        "the saved snapshot spelling must retain the shared load identity"
    );
}

/// Build the load equation emitted by a call whose contract reads one
/// structure field.  The bounded-pool and owned-string examples exercise this
/// shape for `pool->capacity` and `owner->len`, respectively.
fn example_load_defining_requirement(
    block: &str,
    local: &str,
    offset: i64,
) -> (CState, Proposition, Variable) {
    let pointer = Pointer {
        block: PointerBlock::Concrete(block.into()),
        offset: PointerOffsetTerm::Constant(offset),
    };
    let state = CState::new()
        .with_memory(CMemory::new().with_block(block, 16))
        .with_local(
            local,
            CValue::typed_pointer(
                Pointer {
                    block: PointerBlock::Concrete(block.into()),
                    offset: PointerOffsetTerm::Constant(0),
                },
                CType::Int32Pointer,
            ),
        );
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(state.memory()),
        Box::new(pointer),
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    (
        state,
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(defining_load),
            ),
            true,
        ),
        variable,
    )
}

#[test]
fn bounded_pool_load_equation_round_trips_without_internal_names() {
    let (state, requirement, variable) =
        example_load_defining_requirement("bounded-pool:pool", "pool", 4);
    let state = state.with_local("result", CValue::Int32(Bitvector32Term::Variable(variable)));
    let spelled = synthesize_surface_proposition(&requirement, &[], &[], &state)
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
    let state = state.with_local("result", CValue::Int32(Bitvector32Term::Variable(variable)));
    let spelled = synthesize_surface_proposition(&requirement, &[], &[], &state)
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
fn load_equation_rejects_wrong_snapshot_and_unresolvable_variable() {
    let (state, requirement, variable) =
        example_load_defining_requirement("owned-string:wrong-snapshot", "owner", 0);
    let wrong_memory = CMemory::new().with_block("owned-string:other-epoch", 16);
    let wrong_pointer = Pointer {
        block: PointerBlock::Concrete("owned-string:wrong-snapshot".into()),
        offset: PointerOffsetTerm::Constant(4),
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, _), true) = &requirement
    else {
        unreachable!()
    };
    let wrong_pointer_requirement = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            left.clone(),
            Box::new(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(state.memory()),
                Box::new(wrong_pointer.clone()),
            )),
        ),
        true,
    );
    assert!(synthesize_surface_proposition(&wrong_pointer_requirement, &[], &[], &state).is_none());

    let wrong_epoch = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            left.clone(),
            Box::new(Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory_ref(&wrong_memory),
                Box::new(Pointer {
                    block: PointerBlock::Concrete("owned-string:wrong-snapshot".into()),
                    offset: PointerOffsetTerm::Constant(0),
                }),
            )),
        ),
        true,
    );
    assert!(synthesize_surface_proposition(&wrong_epoch, &[], &[], &state).is_none());

    let unresolvable = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(variable.0 + 1))),
            left.clone(),
        ),
        true,
    );
    assert!(synthesize_surface_proposition(&unresolvable, &[], &[], &state).is_none());
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
    let memory = CMemory::new().with_block(block, 16);
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&memory),
        Box::new(pointer.clone()),
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let requirement = Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(variable)),
            Box::new(defining_load),
        ),
        true,
    );
    let state = CState::new()
        .with_memory(memory)
        .with_local(
            parameter.name(),
            CValue::typed_pointer(base.clone(), CType::UInt8Pointer),
        )
        .with_local("result", CValue::Int32(Bitvector32Term::Variable(variable)));
    let parameters = [parameter];
    let arguments = [CExpression::Value(CValue::typed_pointer(
        base,
        CType::UInt8Pointer,
    ))];
    let spelled = synthesize_surface_proposition(&requirement, &parameters, &arguments, &state)
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
fn strlen_existential_guard_round_trips_without_duplicate_guard() {
    let variable = Variable(1);
    let increment = Bitvector32Term::Add(
        Box::new(Bitvector32Term::Variable(variable)),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let requirement = Proposition::Exists {
        name: "len".to_string(),
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedAddOverflows(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::Constant(1)),
                ),
                false,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(Bitvector32Term::Constant(0)),
                    Box::new(increment),
                ),
                true,
            )),
        )),
    };
    let state = CState::new();
    let spelled = synthesize_surface_proposition(&requirement, &[], &[], &state)
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
        sort: Sort::CInt32,
        body: Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedAddOverflows(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::Constant(1)),
                ),
                false,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedGreaterEqual(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
                true,
            )),
        )),
    };
    let state = CState::new();
    let spelled = synthesize_surface_proposition(&requirement, &[], &[], &state)
        .expect("the negative shape should remain spellable");
    assert!(matches!(
        &spelled,
        ClickProposition::Exists {
            body,
            ..
        } if matches!(body.as_ref(), ClickProposition::And(left, _) if matches!(left.as_ref(), ClickProposition::Defined { .. }))
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
            ConditionTerm::Bitvector32SignedAddOverflows(
                Box::new(Bitvector32Term::Variable(variable)),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            false,
        );
        let comparison = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::Constant(0)),
                Box::new(Bitvector32Term::Add(
                    Box::new(Bitvector32Term::Variable(variable)),
                    Box::new(Bitvector32Term::Constant(1)),
                )),
            ),
            true,
        );
        let mut body = comparison;
        for _ in 0..guard_count {
            body = Proposition::And(Box::new(guard.clone()), Box::new(body));
        }
        Proposition::Exists {
            name: "len".to_string(),
            var: variable,
            sort: Sort::CInt32,
            body: Box::new(body),
        }
    }

    let samples = [1, 2, 4, 8].map(|guard_count| {
        let proposition = requirement(guard_count);
        let _scope = SurfaceSynthesisScope::enter();
        let surface = synthesize_surface_proposition_with_guard_fallback(
            &proposition,
            &[],
            &[],
            &CState::new(),
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
