use super::*;

/// Lowers a written proposition exactly as a `have` in a fixed-state proof
/// does, so a synthesized spelling is accepted only when it re-lowers to the
/// proposition it was synthesized from.
fn relower_written_proposition(
    surface: &ClickProposition,
    state: &CState,
) -> Result<Proposition, String> {
    crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_through_kernel_with_opaque_calls(
        surface,
        &PureFactContext::new(),
        &BTreeMap::new(),
        &BTreeMap::new(),
        state,
        state,
        None,
        &RecordedSnapshots::default(),
        &PredicateEnvironment::new(&[]),
        &ClickFunctionEnvironment::new(&[]),
        &std::collections::BTreeSet::new(),
    )
}

/// One cell of a foreign static or file-scope object, spelled the way a
/// caller's own contract writes it: the qualified name under the source
/// alias, then the index. The parser flattens a multidimensional qualified
/// array's indices into one, so `values[0]` and `values[0][2]` are the same
/// surface shape over the same object.
fn qualified_cell(name: &str, base: &CValue, index: i32) -> ContractExpression {
    ContractExpression::Index(
        Box::new(ContractExpression::QualifiedC {
            name: name.to_string(),
            lowered: CExpression::Value(base.clone()),
        }),
        Box::new(ContractExpression::IntegerLiteral(index.to_string())),
    )
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
                    | ContractExpression::Field { base: inner, .. } = base
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
