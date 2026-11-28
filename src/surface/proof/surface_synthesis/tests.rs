use super::*;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};
use crate::kernel::{MachineCastSpelling, OldMachineTerm};

#[test]
fn separation_names_loaded_pointer_fields_at_their_declared_type() {
    use crate::kernel::{MemoryRange, Pointer, Resource};
    for scalar in ["uint8", "uint16", "int32", "uint64"] {
        let _session = crate::kernel::VerificationSession::enter();
        let function = syntax::parse_function(&format!(
            "struct Cursor {{ const {scalar}* data; }}; void read(struct Cursor* cursor) {{}}"
        ))
        .unwrap();
        let parameters = [function.parameters()[0].clone()];
        let base = Address::symbolic(Variable(997101));
        let memory = SymbolicMemory::new();
        let loaded =
            Address::canonical_loaded_value(&crate::kernel::intern_memory_ref(&memory), &base);
        let other = Address::symbolic(Variable(997102));
        let arguments = [ProgramExpression::Value(ProgramValue::pointer(
            base.clone(),
        ))];
        let state = ExecutionState::new()
            .with_memory(memory)
            .with_local("cursor", ProgramValue::pointer(base))
            .with_local(
                "other",
                ProgramValue::typed_pointer(other.clone(), ProgramType::UInt8Pointer),
            );
        let range = |pointer| {
            Resource::Memory(MemoryRange::from_pointer_value(
                &Pointer::new(pointer, ProgramType::UInt8Pointer),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(4),
                1,
            ))
        };
        let expected = Proposition::ResourceSeparate {
            left: Box::new(range(loaded)),
            right: Box::new(range(other)),
        };
        let raised = synthesize_surface_proposition(
            &expected,
            ParameterBinding::new(&parameters, &arguments),
            &state,
        )
        .expect("a loaded pointer field has its declared source spelling");
        let lowered = relower_written_proposition(&raised, &state).unwrap();
        assert_eq!(
            crate::kernel::proof::proposition_identity_key(&lowered),
            crate::kernel::proof::proposition_identity_key(&expected),
            "{scalar}: {raised:?}"
        );
    }
}

#[test]
fn separate_round_trips_without_generating_span_obligations() {
    use crate::kernel::{MemoryRange, Pointer, Resource};
    for wide in [false, true] {
        let pointer = Pointer::new(
            Address::symbolic(Variable(997001)),
            ProgramType::Int32Pointer,
        );
        let end = OldMachineTerm::Variable(Variable(997002));
        let zero = if wide {
            OldMachineTerm::uint64_constant(0)
        } else {
            OldMachineTerm::constant(0)
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
                ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
                FixedStateFrame::new(&state, &state, None, &RecordedStates::default()),
                SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::new(&[])),
                FixedStateLoweringOptions::default(),
            ).unwrap();
        assert_eq!(lowered, expected, "{text}");
        assert!(
            obligations.is_empty(),
            "naming ranges must not owe physical spans: {obligations:?}"
        );
    }
}

/// Compare structural lowering separately from proving the use site's debts.
/// Ordinary proof operations still check those debts before admitting a fact.
fn relower_written_proposition(
    surface: &SyntaxProposition,
    state: &ExecutionState,
) -> Result<Proposition, String> {
    relower_written_proposition_with_states(surface, state, state, &RecordedStates::default())
}

#[test]
fn a_printed_void_pointer_coercion_round_trips_its_pointer_type() {
    let parse = |text: &str| {
        parser::parse(&format!(
            "void probe(int32* pointer, void* other) {{ requires {text}; ensures true; }}"
        ))
        .unwrap()
    };
    let file = parse("other == pointer");
    let function = &file.function_blocks()[0];
    let Requirement::Proposition(mut proposition) = function.requires()[0].clone() else {
        panic!("expected a comparison requirement");
    };
    let SyntaxProposition::Comparison { right, .. } = &mut proposition else {
        panic!("expected a comparison");
    };
    *right = crate::surface::lowering::pure_function_parameter_argument(
        &function.signature().parameters()[1],
        right,
    );
    let state = ExecutionState::new()
        .with_local(
            "pointer",
            ProgramValue::typed_pointer(
                Address::symbolic(Variable(910_001)),
                ProgramType::Int32Pointer,
            ),
        )
        .with_local(
            "other",
            ProgramValue::typed_pointer(
                Address::symbolic(Variable(910_002)),
                ProgramType::VoidPointer,
            ),
        );
    let written = crate::surface::printing::source_click_proposition(&proposition);
    let parsed = parse(&written);
    let Requirement::Proposition(reparsed) = &parsed.function_blocks()[0].requires()[0] else {
        panic!("expected a comparison requirement");
    };
    assert_eq!(
        relower_written_proposition(reparsed, &state).unwrap(),
        relower_written_proposition(&proposition, &state).unwrap(),
        "{written}"
    );
}

/// `(wide & 1u64) == narrow` compares a `uint64` word with an `int32` one,
/// which lowering widens. Raising must leave the widening to lowering: with
/// it written as a cast, both operands have one format and the comparison
/// lowers to a different node.
#[test]
fn a_wide_equality_with_a_narrow_operand_round_trips() {
    let file = parser::parse(
        "void probe(uint64 wide, int32 narrow) { requires (wide & 1u64) == narrow; ensures true; }",
    )
    .unwrap();
    let Requirement::Proposition(written) = file.function_blocks()[0].requires()[0].clone() else {
        panic!("expected a comparison requirement");
    };
    let state = ExecutionState::new()
        .with_local(
            "wide",
            ProgramValue::UInt64(OldMachineTerm::Variable(Variable(910_101))),
        )
        .with_local(
            "narrow",
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(910_102))),
        );
    let original = relower_written_proposition(&written, &state).unwrap();
    let raised = synthesize_surface_proposition(&original, ParameterBinding::default(), &state)
        .expect("the equality must be spellable");
    assert_eq!(
        relower_written_proposition(&raised, &state),
        Ok(original),
        "{}",
        crate::surface::printing::source_click_proposition(&raised)
    );
}

/// A pointer whose address is an integer word, as a tagged parent pointer
/// is read, raises as the conversion it was written as, with its word
/// unsigned. (Lowering the conversion needs a state that records the word's
/// address, so this checks the spelling.)
#[test]
fn an_integer_converted_pointer_is_spelled_as_its_conversion() {
    let word = OldMachineTerm::Variable(Variable(910_201));
    let other = Address::symbolic(Variable(910_202));
    let state = ExecutionState::new()
        .with_local("word", ProgramValue::UInt64(word.clone()))
        .with_local(
            "other",
            ProgramValue::typed_pointer(other.clone(), ProgramType::Int32Pointer),
        );
    let masked = OldMachineTerm::bitwise_and_at(
        MachineIntegerType::UInt64,
        word,
        OldMachineTerm::uint64_constant(!3),
    );
    let fact = Proposition::condition_is(
        OldConditionTerm::pointer_equal(
            crate::kernel::Pointer::new(
                Address::from_integer_address(masked),
                ProgramType::Int32Pointer,
            ),
            crate::kernel::Pointer::new(other, ProgramType::Int32Pointer),
        ),
        true,
    );
    let raised = synthesize_surface_proposition(&fact, ParameterBinding::default(), &state)
        .expect("the conversion must be spellable");
    assert_eq!(
        crate::surface::printing::source_click_proposition(&raised),
        "((word & 18446744073709551612u64) as (int32 *)) == other"
    );
}

fn relower_written_proposition_with_states(
    surface: &SyntaxProposition,
    pre_state: &ExecutionState,
    state: &ExecutionState,
    recorded_states: &RecordedStates,
) -> Result<Proposition, String> {
    crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
        surface,
        &PureFactContext::new(),
        ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
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
fn qualified_cell(name: &str, base: &ProgramValue, index: i32) -> SyntaxTerm {
    SyntaxTerm::Index(
        Box::new(SyntaxTerm::QualifiedC {
            name: name.to_string(),
            lowered: ProgramExpression::Value(base.clone()),
        }),
        Box::new(SyntaxTerm::IntegerLiteral(index.to_string())),
    )
}

fn qualified_multidimensional_cell(
    name: &str,
    base: &ProgramValue,
    row: i32,
    column: i32,
    columns: i32,
) -> SyntaxTerm {
    let flat_index = row * columns + column;
    SyntaxTerm::ArrayIndex {
        base: Box::new(SyntaxTerm::QualifiedC {
            name: name.to_string(),
            lowered: ProgramExpression::Value(base.clone()),
        }),
        indexes: vec![
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(row as u32))),
            SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(column as u32))),
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
) -> (ExecutionState, SurfacePropositionMap, Vec<OldMachineTerm>) {
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block(block, 4 * u32::try_from(cells).unwrap()));
    let base = ProgramValue::typed_pointer(
        Address::new(
            AddressBase::Concrete(block.into()),
            AddressOffset::constant(0),
        ),
        ProgramType::Int32Pointer,
    );
    let mut sources = SurfacePropositionMap::default();
    let loads = (0..cells)
        .map(|index| {
            let written = SyntaxProposition::Comparison {
                left: qualified_cell(name, &base, index),
                operator: ComparisonOperator::Equal,
                right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(5))),
            };
            let lowered = relower_written_proposition(&written, &state)
                .expect("a qualified cell comparison lowers at a state holding the object");
            sources
                .record_lowering(&written, &lowered)
                .expect("the comparison lowers to matching logical structure");
            // The load term as lowering produced it: a registered load
            // variable, one of the two forms an emitted requirement carries.
            let Some((
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: load,
                    right: _,
                },
                _,
            )) = lowered.old_condition()
            else {
                panic!("a qualified cell comparison lowers to one load equality");
            };
            load.as_ref().clone()
        })
        .collect();
    (state, sources, loads)
}

/// The precondition every `static_array_parity_*`, `static_local_arrays`, and
/// `file_scope_static_arrays` call carries: each cell of the callee's own
/// static array is strictly inside `(-1000, 1000)`, left-nested exactly as
/// the contract's `and` chain lowers.
fn cells_within_bounds(loads: &[OldMachineTerm]) -> Proposition {
    let clauses = loads.iter().flat_map(|load| {
        [
            Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterThan,
                    left: Box::new(load.clone()),
                    right: Box::new(OldMachineTerm::constant((-1000i32) as u32)),
                },
                true,
            ),
            Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(load.clone()),
                    right: Box::new(OldMachineTerm::constant(1000)),
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
) -> Option<SyntaxProposition> {
    let _sources = QualifiedSynthesisScope::enter(sources);
    let _budget = SurfaceSynthesisScope::enter();
    synthesize_surface_proposition(proposition, ParameterBinding::default(), state)
}

/// Every qualified name the spelling of a proposition reaches for.
fn qualified_names_in(proposition: &SyntaxProposition) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    let mut propositions = vec![proposition];
    while let Some(proposition) = propositions.pop() {
        match proposition {
            SyntaxProposition::And(left, right)
            | SyntaxProposition::Or(left, right)
            | SyntaxProposition::Implies(left, right) => {
                propositions.push(left);
                propositions.push(right);
            }
            SyntaxProposition::Comparison { left, right, .. } => {
                for expression in [left, right] {
                    let mut base = expression;
                    while let SyntaxTerm::Index(inner, _)
                    | SyntaxTerm::Field { base: inner, .. }
                    | SyntaxTerm::ArrayIndex { base: inner, .. } = base
                    {
                        base = inner;
                    }
                    if let SyntaxTerm::QualifiedC { name, .. } = base {
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
        ProgramValue::Int32(OldMachineTerm::Variable(Variable(894321))),
    );
    let candidate = SyntaxProposition::Comparison {
        left: SyntaxTerm::Call {
            name: "to_integer".into(),
            arguments: vec![SyntaxTerm::Add(
                Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                    "x".into(),
                ))),
                Box::new(SyntaxTerm::IntegerLiteral("1".into())),
            )],
        },
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::IntegerLiteral("0".into()),
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
fn definedness_round_trips_at_distinct_points_after_unfold_names_a_cell() {
    let _session = crate::kernel::VerificationSession::enter();
    let file = crate::surface::parse(
        "resource cell(p: int32*) { owns *p; fact defined(*p); }\n\
         int32 read(int32* p) { owns cell(p); ensures true; }",
    )
    .unwrap();
    let [Requirement::Resource(resource)] = file.function_blocks()[0].requires() else {
        panic!("expected the cell resource as the only requirement");
    };
    let parsed = syntax::parse_function("int32 read(int32* p) { return *p; }").unwrap();
    let resources = ResourceEnvironment::new(file.resource_definitions());
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let specs = SpecDefinitions::new(&predicates, &functions);
    let pointer = Address::symbolic(Variable(981_301));
    let value = ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer);
    let arguments = [ProgramExpression::Value(value.clone())];
    let parameters = ParameterBinding::new(parsed.parameters(), &arguments);
    let historical = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block(pointer.base.clone(), 4))
        .with_local("p", value.clone())
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own_composite("cell".into(), vec![value])),
        );
    let current = historical.clone().with_memory(historical.memory().clone());
    let unfold = |state: ExecutionState| {
        let point = state.observation_point_id().unwrap();
        assert!(!matches!(
            state.memory().load(&pointer),
            ExpressionOutcome::Value(_)
        ));
        let checked = super::super::resources::unfold_composite_resource_for_proof(
            &resources,
            resource,
            resource,
            parameters,
            state,
            crate::kernel::proof::PureFactStore::default(),
            &mut SurfacePropositionMap::default(),
            specs,
            "unfold before raising definedness",
            0,
            true,
        )
        .unwrap();
        assert!(matches!(
            checked.state.memory().load(&pointer),
            ExpressionOutcome::Value(_)
        ));
        let fact = Proposition::MemoryReadDefined {
            point: Default::default(),
            at: Some(point),
            memory: checked.state.memory().clone(),
            pointer: pointer.clone(),
            value_type: ProgramType::Int32,
        };
        assert!(checked.added_facts.contains(&fact));
        (checked.state, fact)
    };
    let (historical, historical_fact) = unfold(historical);
    let (current, current_fact) = unfold(current);
    assert_eq!(historical.memory(), current.memory());
    assert_ne!(
        historical.observation_point_id(),
        current.observation_point_id()
    );
    let selector = ProgramPointSelector::Mark("observed".into());
    let mut points = RecordedStates::new();
    points.insert(selector.clone(), historical);
    let _points = SynthesisRecordedPointsScope::enter(&points);
    let historical = synthesize_surface_proposition(&historical_fact, parameters, &current)
        .expect("the historical observation should have a spelling");
    assert!(
        matches!(&historical, SyntaxProposition::At { selector: selected, .. } if selected == &selector)
    );
    let present = synthesize_surface_proposition(&current_fact, parameters, &current)
        .expect("the current observation should have a spelling");
    assert!(matches!(&present, SyntaxProposition::Defined { .. }));
    for (spelled, fact) in [(historical, historical_fact), (present, current_fact)] {
        assert_eq!(
            relower_written_proposition_with_states(&spelled, &current, &current, &points),
            Ok(fact)
        );
    }
}

#[test]
fn ordinary_entry_cell_read_round_trips_after_overwrite() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(981_302)), 4),
    );
    let entry = ExecutionState::new()
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        )
        .begin_function_entry_memory();
    let post = entry.clone().with_memory(entry.memory().clone().store(
        pointer.clone(),
        ProgramValue::Int32(OldMachineTerm::constant(7)),
    ));
    let parsed =
        crate::surface::parse("theorem probe(p: int32*) { requires old(*p) < 6; ensures true; }")
            .unwrap();
    let Requirement::Proposition(written) = &parsed.theorem_definitions()[0].requires()[0] else {
        panic!("expected a proposition");
    };
    let points = RecordedStates::new();
    let original = relower_written_proposition_with_states(written, &entry, &post, &points)
        .expect("the historical read lowers");
    let read = OldMachineTerm::read_named(
        entry
            .program_point()
            .ordinary_typed_version(&pointer, ProgramType::Int32)
            .expect("the read has an entry version"),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let Proposition::ConditionIs(condition, true) = &original else {
        panic!("expected the read comparison");
    };
    let view = crate::kernel::machine_integer::comparison::structural_comparison_view(
        condition.old_form(),
    )
    .unwrap();
    assert_eq!(
        crate::kernel::KernelTerm::retained_machine_operand(
            view.format,
            view.operands[0].operand_view(),
        ),
        crate::kernel::KernelTerm::retained_machine_operand(
            view.format,
            crate::kernel::MachineOperandView::Old(&read),
        ),
    );
    let raised = synthesize_surface_proposition_at_entry_and_post(
        &original,
        ParameterBinding::default(),
        &entry,
        &post,
    )
    .expect("the entry version has a spelling");
    let spelling = crate::surface::printing::source_click_proposition(&raised);
    assert!(spelling.contains("old("), "{spelling}");
    assert_eq!(
        relower_written_proposition_with_states(&raised, &entry, &post, &points),
        Ok(original),
    );
}

#[test]
fn old_read_shortcut_identifies_points_instead_of_equal_snapshots() {
    let _session = crate::kernel::VerificationSession::enter();
    let entry = ExecutionState::new().with_memory(SymbolicMemory::new());
    let frame = ExecutionState::at_state(&entry);
    assert!(synthesis_states_share_program_point(&entry, &frame));
    let later = entry.clone().with_memory(entry.memory().clone());
    assert_eq!(entry.memory(), later.memory());
    assert!(!synthesis_states_share_program_point(&entry, &later));
    assert!(!synthesis_states_share_program_point(
        &ExecutionState::new(),
        &ExecutionState::new()
    ));
    let unnamed = ExecutionState::new();
    assert!(synthesis_states_share_program_point(&unnamed, &unnamed));
}

#[test]
fn qualified_static_read_spellings_retain_entry_and_current_epochs() {
    let _session = crate::kernel::VerificationSession::enter();
    let (entry, sources, loads) =
        recorded_qualified_cells("file-static:alpha.c:calls", "alpha::calls", 1);
    let address = Address::new(
        AddressBase::Concrete("file-static:alpha.c:calls".into()),
        AddressOffset::constant(0),
    );
    let post = entry
        .clone()
        .with_memory(entry.memory().clone().store(address.clone(), int32(7)));
    let current = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_memory_ref(post.memory()),
        address,
        crate::kernel::LoadKind::Int32,
    );
    let named = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(current.clone()),
            right: Box::new(loads[0].clone()),
        },
        true,
    );
    let resolve = crate::kernel::resolve_load_variables_from_registry;
    let shared = Proposition::condition_is(
        OldConditionTerm::integer_equal(
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
    let state = ExecutionState::new().with_memory(SymbolicMemory::new().with_block(block, 12));
    let base = ProgramValue::typed_pointer(
        Address::new(
            AddressBase::Concrete(block.into()),
            AddressOffset::constant(0),
        ),
        ProgramType::Int32Pointer,
    );
    let surface = SyntaxProposition::Comparison {
        left: qualified_multidimensional_cell(
            "static_local::increment_twice::values",
            &base,
            0,
            2,
            3,
        ),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(5))),
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
        SyntaxProposition::Comparison {
            left: SyntaxTerm::ArrayIndex { .. },
            ..
        }
    ));
    assert_eq!(
        relower_written_proposition(&spelled, &state),
        Ok(lowered),
        "the recovered spelling must lower to the exact cell"
    );
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
    let pointer = Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_000)), 1),
    );
    let pointer = ProgramValue::typed_pointer(pointer, ProgramType::UInt8Pointer);
    let length = ProgramValue::Int32(OldMachineTerm::Variable(Variable(1)));
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
        point: Default::default(),
        memory: state.memory().clone(),
        base: match &arguments[0] {
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.address().clone(),
            _ => unreachable!(),
        },
        bytes: (OldMachineTerm::add(
            OldMachineTerm::Variable(Variable(1)),
            OldMachineTerm::constant(1),
        ))
        .into(),
        wide: false,
    };
    let synthesized = synthesize_source_projection_proposition_with_bound_variable_names(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
        &BTreeMap::new(),
    )
    .expect("the exact external byte range must be spellable");
    let SyntaxProposition::Loadable { segment } = &synthesized else {
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
        ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.address().clone(),
        _ => unreachable!(),
    };
    arguments[0] = ProgramExpression::Variable("bytes".into());
    let requirement = Proposition::MemoryLoadable {
        point: Default::default(),
        memory: state.memory().clone(),
        base,
        bytes: (OldMachineTerm::add(
            OldMachineTerm::Variable(Variable(1)),
            OldMachineTerm::constant(1),
        ))
        .into(),
        wide: false,
    };
    let synthesized = synthesize_source_projection_proposition_with_bound_variable_names(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
        &BTreeMap::new(),
    )
    .expect("the exact named local argument must resolve to its declared byte parameter");
    let SyntaxProposition::Loadable { segment } = synthesized else {
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
        point: Default::default(),
        memory: state.memory().clone(),
        base: match &arguments[0] {
            ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.address().clone(),
            _ => unreachable!(),
        },
        bytes: (OldMachineTerm::constant(4)).into(),
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
fn external_byte_range_requirement(binder: Variable, length: &OldMachineTerm) -> Proposition {
    let index = OldMachineTerm::Variable(binder);
    crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::ProgramInt32,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessEqual,
                        left: Box::new(OldMachineTerm::constant(0)),
                        right: Box::new(index.clone()),
                    },
                    true,
                )),
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(index.clone()),
                        right: Box::new(length.clone()),
                    },
                    true,
                )),
            )),
            Box::new(Proposition::MemoryLoadable {
                point: Default::default(),
                memory: SymbolicMemory::new(),
                base: Address::new(
                    AddressBase::ExternalArgument,
                    AddressOffset::raw_add(
                        AddressOffset::scaled_int32_node(
                            OldMachineTerm::Variable(Variable(100_000)),
                            1,
                        ),
                        AddressOffset::scaled_int32_node(index.clone(), 1),
                    ),
                ),
                bytes: (binary_node!(
                    Int32,
                    Subtract,
                    Box::new(binary_node!(
                        Int32,
                        Add,
                        Box::new(index.clone()),
                        Box::new(OldMachineTerm::constant(1)),
                    )),
                    Box::new(index),
                ))
                .into(),
                wide: false,
            }),
        ),
    )
}

fn external_symbolic_element_context(
    memory: SymbolicMemory,
) -> (
    Vec<crate::languages::interface::ImportedParameter>,
    Vec<ProgramExpression>,
    ExecutionState,
) {
    let pointer = Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_000)), 1),
    );
    let pointer = ProgramValue::typed_pointer(pointer, ProgramType::UInt8Pointer);
    let index = ProgramValue::Int32(OldMachineTerm::Variable(Variable(100_001)));
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

fn external_symbolic_element_requirement(memory: SymbolicMemory, index: Variable) -> Proposition {
    external_symbolic_element_requirement_term(memory, OldMachineTerm::Variable(index))
}

fn external_symbolic_element_requirement_term(
    memory: SymbolicMemory,
    index: OldMachineTerm,
) -> Proposition {
    Proposition::MemoryLoadable {
        point: Default::default(),
        memory,
        base: Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::raw_add(
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_000)), 1),
                AddressOffset::scaled_int32_node(index.clone(), 1),
            ),
        ),
        bytes: (binary_node!(
            Int32,
            Subtract,
            Box::new(binary_node!(
                Int32,
                Add,
                Box::new(index.clone()),
                Box::new(OldMachineTerm::constant(1)),
            )),
            Box::new(index),
        ))
        .into(),
        wide: false,
    }
}

fn external_symbolic_element_constant_byte_requirement(
    memory: SymbolicMemory,
    index: Variable,
) -> Proposition {
    let mut requirement = external_symbolic_element_requirement(memory, index);
    let Proposition::MemoryLoadable { bytes, .. } = &mut requirement else {
        unreachable!();
    };
    *bytes = OldMachineTerm::constant(1).into();
    requirement
}

/// The unresolved `strlen` carrier: an existential length whose successor is
/// defined, followed by a guarded universal one-byte loadability range. The
/// caller's outer `loadable(bytes[0..len + 1])` fact is a separate premise;
/// this regression targets the quantified `k` carrier that retains `1`.
fn full_external_guarded_range_surface() -> SyntaxProposition {
    let length_binder = SurfaceBinder::fresh();
    let index_binder = SurfaceBinder::fresh();
    let length = length_binder.reference();
    let index = index_binder.reference();
    let quantified_range = SyntaxProposition::Loadable {
        segment: ContractSegment {
            uninitialized: false,
            state: ContractSegmentState::Current,
            base: ProgramExpression::Variable("bytes".into()),
            start: ProgramExpression::Variable(index_binder.kernel_name()),
            end: ProgramExpression::Add(
                Box::new(ProgramExpression::Variable(index_binder.kernel_name())),
                Box::new(ProgramExpression::Value(int32(1))),
            ),
            surface: ContractSegmentSurface::Range {
                base: SyntaxTerm::ProgramExpression(ProgramExpression::Variable("bytes".into())),
                start: index.clone(),
                end: SyntaxTerm::Add(
                    Box::new(index.clone()),
                    Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Value(
                        int32(1),
                    ))),
                ),
            },
        },
    };
    let all_before_loadable = SyntaxProposition::ForAll {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: index_binder,
        written_name: None,
        body: Box::new(SyntaxProposition::Implies(
            Box::new(SyntaxProposition::And(
                Box::new(SyntaxProposition::Comparison {
                    left: index.clone(),
                    operator: ComparisonOperator::GreaterEqual,
                    right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(0))),
                }),
                Box::new(SyntaxProposition::Comparison {
                    left: index.clone(),
                    operator: ComparisonOperator::LessThan,
                    right: length.clone(),
                }),
            )),
            Box::new(quantified_range),
        )),
    };
    SyntaxProposition::Exists {
        click_type: ClickType::Program(InterfaceType::Int32),
        name: length_binder.clone(),
        written_name: None,
        body: Box::new(SyntaxProposition::And(
            Box::new(SyntaxProposition::Defined {
                expression: SyntaxTerm::ProgramExpression(ProgramExpression::Add(
                    Box::new(ProgramExpression::Variable(length_binder.kernel_name())),
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
                *bytes = OldMachineTerm::constant(1).into();
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
    let memory = SymbolicMemory::new().with_block("strlen:production-bytes", 16);
    let (parameters, concrete_arguments, state) = external_symbolic_element_context(memory.clone());
    let pointer = match &concrete_arguments[0] {
        ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.clone(),
        _ => panic!("the production-shaped argument must be a pointer"),
    };
    let arguments = vec![
        ProgramExpression::Variable(("bytes".to_string()).into()),
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
    assert!(matches!(synthesized, SyntaxProposition::Exists { .. }));
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
    let memory = SymbolicMemory::new().with_block("strlen:production-constant-bytes", 16);
    let (parameters, concrete_arguments, state) = external_symbolic_element_context(memory.clone());
    let pointer = match &concrete_arguments[0] {
        ProgramExpression::Value(ProgramValue::Pointer(pointer)) => pointer.clone(),
        _ => panic!("the production-shaped argument must be a pointer"),
    };
    let arguments = vec![
        ProgramExpression::Variable(("bytes".to_string()).into()),
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
    assert!(matches!(synthesized, SyntaxProposition::Exists { .. }));
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
    let memory = SymbolicMemory::new().with_block("strlen:bytes", 16);
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
    let SyntaxProposition::Loadable { segment } = &synthesized else {
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
    let memory = SymbolicMemory::new().with_block("strlen:constant-symbolic-bytes", 16);
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
    let SyntaxProposition::Loadable { segment } = &synthesized else {
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
    let memory = SymbolicMemory::new().with_block("strlen:bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());

    let wrong_base = Proposition::MemoryLoadable {
        point: Default::default(),
        memory: memory.clone(),
        base: Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::raw_add(
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_002)), 1),
                AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_001)), 1),
            ),
        ),
        bytes: (binary_node!(
            Int32,
            Subtract,
            Box::new(binary_node!(
                Int32,
                Add,
                Box::new(OldMachineTerm::Variable(Variable(100_001))),
                Box::new(OldMachineTerm::constant(1)),
            )),
            Box::new(OldMachineTerm::Variable(Variable(100_001))),
        ))
        .into(),
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
        base.set_offset(AddressOffset::raw_add(
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_000)), 2),
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_001)), 2),
        ));
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
    let memory = SymbolicMemory::new().with_block("strlen:constant-bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let requirement =
        external_symbolic_element_requirement_term(memory, OldMachineTerm::constant(3));
    let synthesized = synthesize_surface_proposition(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
    )
    .expect("a constant reduced element must retain the historical range fallback");
    let SyntaxProposition::Loadable { segment } = &synthesized else {
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
    assert_eq!(bytes.old_form(), &OldMachineTerm::constant(1));
    assert_eq!(
        base.offset,
        AddressOffset::raw_add(
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_000)), 1),
            AddressOffset::constant(3)
        )
    );
}

#[test]
fn strlen_zero_based_element_range_round_trips_exactly() {
    let memory = SymbolicMemory::new().with_block("strlen:zero-based-bytes", 16);
    let (parameters, mut arguments, state) = external_symbolic_element_context(memory.clone());
    let pointer = ProgramValue::typed_pointer(
        Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0)),
        ProgramType::UInt8Pointer,
    );
    arguments[0] = ProgramExpression::Value(pointer.clone());
    let state = state.with_local("bytes", pointer);
    let mut requirement = external_symbolic_element_requirement(memory, Variable(100_001));
    let Proposition::MemoryLoadable { base, .. } = &mut requirement else {
        unreachable!();
    };
    base.set_offset(AddressOffset::scaled_int32_node(
        OldMachineTerm::Variable(Variable(100_001)),
        1,
    ));
    let synthesized = synthesize_surface_proposition(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
    )
    .expect("the canonical zero-based strlen element must be spellable");
    let SyntaxProposition::Loadable { segment } = &synthesized else {
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
    let memory = SymbolicMemory::new().with_block("local:elements", 8);
    let pointer = ProgramValue::typed_pointer(
        Address::new(
            AddressBase::Concrete("local:elements".into()),
            AddressOffset::constant(0),
        ),
        ProgramType::UInt8Pointer,
    );
    let start = ProgramValue::Int32(OldMachineTerm::Variable(Variable(100_001)));
    let state = ExecutionState::new()
        .with_memory(memory.clone())
        .with_local("elements", pointer)
        .with_local("start", start);
    let requirement = Proposition::MemoryLoadable {
        point: Default::default(),
        memory,
        base: Address::new(
            AddressBase::Concrete("local:elements".into()),
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_001)), 1),
        ),
        bytes: (binary_node!(
            Int32,
            Subtract,
            Box::new(binary_node!(
                Int32,
                Add,
                Box::new(OldMachineTerm::Variable(Variable(100_001))),
                Box::new(OldMachineTerm::constant(1)),
            )),
            Box::new(OldMachineTerm::Variable(Variable(100_001))),
        ))
        .into(),
        wide: false,
    };
    let synthesized =
        synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
            .expect("the general named-range path must remain available for local pointers");
    let SyntaxProposition::Loadable { segment } = &synthesized else {
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
    let memory = SymbolicMemory::new().with_block("strlen:quantified-bytes", 16);
    let (parameters, arguments, state) = external_symbolic_element_context(memory.clone());
    let binder = Variable(100_002);
    let requirement = crate::kernel::quantifiers::test_forall(
        Default::default(),
        binder,
        Sort::ProgramInt32,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::GreaterEqual,
                        left: Box::new(OldMachineTerm::Variable(binder)),
                        right: Box::new(OldMachineTerm::constant(0)),
                    },
                    true,
                )),
                Box::new(Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::LessThan,
                        left: Box::new(OldMachineTerm::Variable(binder)),
                        right: Box::new(OldMachineTerm::Variable(Variable(100_001))),
                    },
                    true,
                )),
            )),
            Box::new(external_symbolic_element_requirement(memory, binder)),
        ),
    );
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
    let pointer = Address::new(
        AddressBase::ExternalArgument,
        AddressOffset::scaled_int32_node(
            OldMachineTerm::Variable(Variable(100_000)),
            i64::from(width),
        ),
    );
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
        ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(
            100_001,
        )))),
        ProgramExpression::Value(ProgramValue::Int32(OldMachineTerm::Variable(Variable(
            100_002,
        )))),
    ];
    let state = ExecutionState::new()
        .with_local("elements", pointer)
        .with_local(
            "start",
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(100_001))),
        )
        .with_local(
            "end",
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(100_002))),
        );
    (parameters, arguments, state)
}

fn external_element_range_requirement(
    width: u32,
    start: OldMachineTerm,
    end: OldMachineTerm,
) -> Proposition {
    Proposition::MemoryLoadable {
        point: Default::default(),
        memory: SymbolicMemory::new(),
        base: Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::raw_add(
                AddressOffset::scaled_int32_node(
                    OldMachineTerm::Variable(Variable(100_000)),
                    i64::from(width),
                ),
                AddressOffset::scaled_int32_node(start.clone(), i64::from(width)),
            ),
        ),
        bytes: (binary_node!(
            Int32,
            Multiply,
            Box::new(binary_node!(
                Int32,
                Subtract,
                Box::new(end),
                Box::new(start)
            )),
            Box::new(OldMachineTerm::constant(width)),
        ))
        .into(),
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
    let length = OldMachineTerm::Variable(Variable(1));
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
    let SyntaxProposition::ForAll { body, .. } = &spelled else {
        panic!("the requirement is one universal: {spelled:?}");
    };
    let SyntaxProposition::Implies(_, consequent) = body.as_ref() else {
        panic!("the universal's body is one implication: {spelled:?}");
    };
    let SyntaxProposition::Loadable { segment } = consequent.as_ref() else {
        panic!("the consequent is one viewability: {spelled:?}");
    };
    assert_eq!(segment.base, ProgramExpression::Variable("bytes".into()));
    assert_ne!(segment.start, ProgramExpression::Value(int32(0)));

    let lowered = relower_written_proposition(&spelled, &state)
        .expect("the synthesized range lowers at the calling state");
    let Proposition::ForAll { var, .. } = &lowered else {
        panic!("re-lowering keeps the universal: {lowered:?}");
    };
    assert_eq!(lowered, external_byte_range_requirement(**var, &length));
}

#[test]
fn quantified_loadability_uses_saved_state() {
    let (parameters, arguments, retained_state) = external_byte_range_caller();
    let length = OldMachineTerm::Variable(Variable(1));
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

    let SyntaxProposition::ForAll { body, .. } = &spelled else {
        panic!("the saved requirement is one universal: {spelled:?}");
    };
    let SyntaxProposition::Implies(_, consequent) = body.as_ref() else {
        panic!("the saved universal has one guarded body: {spelled:?}");
    };
    assert!(
        matches!(
            consequent.as_ref(),
            SyntaxProposition::At {
                selector: actual,
                proposition,
            } if actual == &selector
                && matches!(proposition.as_ref(), SyntaxProposition::Loadable { .. })
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
            OldMachineTerm::Variable(Variable(100_001)),
            OldMachineTerm::Variable(Variable(100_002)),
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
        let SyntaxProposition::Loadable { segment } = &synthesized else {
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
            SyntaxProposition::Loadable {
                segment: segment.clone(),
            }
        );
        let lowered = relower_written_proposition(&synthesized, &state)
            .expect("the parsed range spelling must re-lower");
        assert_eq!(lowered, requirement);
    }

    let (parameters, arguments, state) =
        external_element_range_context(InterfaceType::Int32Pointer, ProgramType::Int32Pointer, 4);
    let requirement = external_element_range_requirement(
        4,
        OldMachineTerm::constant(3),
        OldMachineTerm::constant(8),
    );
    let synthesized = {
        let _budget = SurfaceSynthesisScope::enter();
        synthesize_surface_proposition(
            &requirement,
            ParameterBinding::new(&parameters, &arguments),
            &state,
        )
        .expect("a folded byte count must retain its nonzero named range")
    };
    let SyntaxProposition::Loadable { segment } = &synthesized else {
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
    assert_eq!(bytes.old_form(), &OldMachineTerm::constant(20));
    assert_eq!(
        base.offset,
        AddressOffset::raw_add(
            AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_000)), 4),
            AddressOffset::constant(12)
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
        OldMachineTerm::Variable(Variable(100_001)),
        OldMachineTerm::Variable(Variable(100_002)),
    );
    let Proposition::MemoryLoadable { base, .. } = &mut requirement else {
        unreachable!();
    };
    base.set_offset(AddressOffset::raw_add(
        AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_000)), 4),
        AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(100_003)), 4),
    ));
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
    let length = OldMachineTerm::Variable(Variable(1));
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
/// raise-lower principle is asserted here; the range shape itself round-trips in the
/// universal test above.
#[test]
fn exists_loadable_range_call_requirement_is_spellable() {
    let (parameters, arguments, state) = external_byte_range_caller();
    let witness = Variable(3_100_000);
    let requirement = crate::kernel::quantifiers::test_exists(
        "len".to_string(),
        witness,
        Sort::ProgramInt32,
        external_byte_range_requirement(Variable(3_100_001), &OldMachineTerm::Variable(witness)),
    );
    let _budget = SurfaceSynthesisScope::enter();
    let spelled = synthesize_surface_proposition(
        &requirement,
        ParameterBinding::new(&parameters, &arguments),
        &state,
    )
    .expect("the call requirement must be spellable");
    assert!(
        matches!(spelled, SyntaxProposition::Exists { .. }),
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
        assert!(matches!(call, SyntaxTerm::Call { arguments, .. } if arguments.len() == size));
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
    let pointer = ProgramValue::pointer(Address::new(
        AddressBase::Concrete("array".into()),
        AddressOffset::constant(0),
    ));
    let entry = ExecutionState::new().with_local("p", pointer.clone());
    let post = entry
        .clone()
        .with_memory(SymbolicMemory::new().with_block("other", 4));
    let values = [crate::kernel::PureFunctionArgument::ArrayRef {
        point: crate::kernel::ProgramPoint::of_memory(entry.memory()),
        pointer,
        element_type: ProgramType::Int32,
    }];
    let bindings = BTreeMap::<Variable, SurfaceBinder>::new();
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
        matches!(&call, SyntaxTerm::Call { arguments, .. } if matches!(arguments.as_slice(), [SyntaxTerm::Old(_)]))
    );
    // An unresolved historical pointer re-enters entry-state synthesis. The
    // entry slot must be free for that nested scope to clear and restore it.
    let unnamed = [crate::kernel::PureFunctionArgument::ArrayRef {
        point: crate::kernel::ProgramPoint::of_memory(entry.memory()),
        pointer: ProgramValue::pointer(Address::symbolic(Variable(9_830_001))),
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
    let pointer = ProgramValue::pointer(Address::symbolic(Variable(981_300)));
    let historical = ExecutionState::new()
        .with_local("p", pointer.clone())
        .with_memory(SymbolicMemory::new().with_block("historical-array", 4));
    let current = historical
        .clone()
        .with_memory(historical.memory().clone().with_block("later-write", 4));
    let values = [crate::kernel::PureFunctionArgument::ArrayRef {
        point: crate::kernel::ProgramPoint::of_memory(historical.memory()),
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
    let SyntaxTerm::Call { arguments, .. } = call else {
        panic!("call")
    };
    assert!(
        matches!(&arguments[0], SyntaxTerm::At { selector: selected, expression }
        if *selected == selector && matches!(expression.as_ref(), SyntaxTerm::ProgramExpression(ProgramExpression::Variable(name)) if name.is_named("p")))
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
                Proposition::condition_is(
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(OldMachineTerm::constant(7)),
                        right: Box::new(OldMachineTerm::constant(7)),
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
                        SyntaxProposition::And(left, right)
                        | SyntaxProposition::Or(left, right)
                        | SyntaxProposition::Implies(left, right) => {
                            pending.push(left);
                            pending.push(right);
                        }
                        SyntaxProposition::Comparison {
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
    let pointer = Address::new(
        AddressBase::Concrete("load-definition".into()),
        AddressOffset::constant(0),
    );
    let memory = SymbolicMemory::new().with_block("load-definition", 4);
    let state = ExecutionState::new().with_memory(memory).with_local(
        "p",
        ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
    );
    let load = OldMachineTerm::read_named(
        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(state.memory()))),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let OldMachineTerm::MemoryLoad(memory, address, kind) = load else {
        unreachable!()
    };
    let defining_load = crate::kernel::canonical_form_of_load(
        crate::kernel::ProgramPoint::from(memory).into_shared_memory(),
        address.into(),
        kind,
    );
    let requirement = Proposition::condition_is(
        OldConditionTerm::Compare {
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
    let pointer = Address::new(
        AddressBase::Concrete("load-definition-entry".into()),
        AddressOffset::constant(0),
    );
    let entry = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block("load-definition-entry", 4))
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        );
    let post = entry.clone().with_memory(
        SymbolicMemory::new()
            .with_block("load-definition-entry", 4)
            .store(pointer.clone(), int32(7)),
    );
    let load = OldMachineTerm::read_named(
        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(entry.memory()))),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let entry = entry.with_local(
        "result",
        ProgramValue::Int32(OldMachineTerm::Variable(variable)),
    );
    let requirement = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(variable)),
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
    let SyntaxProposition::At {
        selector: ProgramPointSelector::ProgramPoint(point),
        proposition,
    } = &spelled
    else {
        panic!("a changed post-state must retain the entry state: {spelled:?}");
    };
    assert_eq!(point.region, CodeRegionRef::Function);
    assert_eq!(point.kind, ProgramPointKind::Entry);
    let SyntaxProposition::Comparison { left, right, .. } = proposition.as_ref() else {
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
    let pointer = Address::new(
        AddressBase::Concrete("load-definition-saved".into()),
        AddressOffset::constant(0),
    );
    let base = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block("load-definition-saved", 4))
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        );
    let load = OldMachineTerm::read_named(
        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(base.memory()))),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let retained_state = base.with_local(
        "result",
        ProgramValue::Int32(OldMachineTerm::Variable(variable)),
    );
    let entry = retained_state.clone().with_memory(
        SymbolicMemory::new()
            .with_block("load-definition-saved", 4)
            .store(pointer.clone(), int32(1)),
    );
    let post = retained_state.clone().with_memory(
        SymbolicMemory::new()
            .with_block("load-definition-saved", 4)
            .store(pointer, int32(2)),
    );
    let requirement = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(variable)),
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
    let SyntaxProposition::At {
        selector: actual,
        proposition,
    } = &spelled
    else {
        panic!("a changed entry and post-state must use the saved state: {spelled:?}");
    };
    assert_eq!(actual, &selector);
    let SyntaxProposition::Comparison { left, right, .. } = proposition.as_ref() else {
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
    let pointer = Address::new(
        AddressBase::Concrete(block.into()),
        AddressOffset::constant(offset),
    );
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block(block, 16))
        .with_local(
            local,
            ProgramValue::typed_pointer(
                Address::new(
                    AddressBase::Concrete(block.into()),
                    AddressOffset::constant(0),
                ),
                ProgramType::Int32Pointer,
            ),
        );
    let load = OldMachineTerm::read_named(
        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(state.memory()))),
        Box::new(pointer),
        crate::kernel::LoadKind::Int32,
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    (
        state,
        Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(OldMachineTerm::Variable(variable)),
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
        ProgramValue::Int32(OldMachineTerm::Variable(variable)),
    );
    let spelled = synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
        .expect("bounded-pool call load equation must be spellable");
    let SyntaxProposition::Comparison { left, right, .. } = &spelled else {
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
        ProgramValue::Int32(OldMachineTerm::Variable(variable)),
    );
    let spelled = synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
        .expect("owned-string call load equation must be spellable");
    let SyntaxProposition::Comparison { left, right, .. } = &spelled else {
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
    let wrong_memory = SymbolicMemory::new().with_block("owned-string:other-epoch", 16);
    let wrong_pointer = Address::new(
        AddressBase::Concrete("owned-string:wrong-retained_state".into()),
        AddressOffset::constant(4),
    );
    let Some((
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left,
            right: _,
        },
        true,
    )) = requirement.old_condition()
    else {
        unreachable!()
    };
    let wrong_pointer_requirement = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: left.clone(),
            right: Box::new(OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::at(
                    &(crate::kernel::intern_memory_ref(state.memory())),
                ),
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

    let wrong_epoch = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: left.clone(),
            right: Box::new(OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(&wrong_memory))),
                Box::new(Address::new(
                    AddressBase::Concrete("owned-string:wrong-retained_state".into()),
                    AddressOffset::constant(0),
                )),
                crate::kernel::LoadKind::Int32,
            )),
        },
        true,
    );
    assert!(
        synthesize_surface_proposition(&wrong_epoch, ParameterBinding::default(), &state).is_none()
    );

    let unresolvable = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(Variable(variable.0 + 1))),
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
    let base = Address::new(
        AddressBase::Concrete(block.into()),
        AddressOffset::constant(0),
    );
    let pointer = base.offset_by_bytes(field_offset as u32);
    let memory = SymbolicMemory::new().with_block(block, 16);
    let load = OldMachineTerm::read_named(
        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(&memory))),
        Box::new(pointer.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let (variable, defining_load) = crate::kernel::load_variable_for_term(&load).unwrap();
    let requirement = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(variable)),
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
            ProgramValue::Int32(OldMachineTerm::Variable(variable)),
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
    let SyntaxProposition::Comparison { left, right, .. } = &spelled else {
        panic!("load equation must remain an equality: {spelled:?}");
    };
    assert_ne!(left, right, "the source spelling must not be tautological");
    assert!(matches!(left, SyntaxTerm::ProgramBinding(name) if name == "result"));
    assert!(matches!(right, SyntaxTerm::Field { field, .. } if field == field_name));
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
        let left = OldMachineTerm::Variable(Variable(972_001));
        let right = OldMachineTerm::Variable(Variable(972_002));
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
            let left = OldMachineTerm::Variable(Variable(1));
            let right = OldMachineTerm::Variable(Variable(2));
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
                    value(OldMachineTerm::machine_binary(
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
        let requirement = Proposition::condition_is(OldConditionTerm::Constant(condition), truth);
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
        Box::new(OldMachineTerm::Variable(variable)),
        Box::new(OldMachineTerm::constant(1)),
    );
    let requirement = crate::kernel::quantifiers::test_exists(
        "len".to_string(),
        variable,
        Sort::ProgramInt32,
        Proposition::And(
            Box::new(Proposition::signed_arithmetic_domain(
                MachineIntegerType::Int32,
                crate::kernel::MachineBinaryOp::Add,
                &OldMachineTerm::Variable(variable),
                &OldMachineTerm::constant(1),
            )),
            Box::new(Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(OldMachineTerm::constant(0)),
                    right: Box::new(increment),
                },
                true,
            )),
        ),
    );
    let state = ExecutionState::new();
    let spelled = synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
        .expect("strlen requirement should synthesize");
    assert!(matches!(
        &spelled,
        SyntaxProposition::Exists {
            body,
            ..
        } if matches!(body.as_ref(), SyntaxProposition::Comparison { .. })
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
    let requirement = crate::kernel::quantifiers::test_exists(
        "len".to_string(),
        variable,
        Sort::ProgramInt32,
        Proposition::And(
            Box::new(Proposition::signed_arithmetic_domain(
                MachineIntegerType::Int32,
                crate::kernel::MachineBinaryOp::Add,
                &OldMachineTerm::Variable(variable),
                &OldMachineTerm::constant(1),
            )),
            Box::new(Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::GreaterEqual,
                    left: Box::new(OldMachineTerm::Variable(variable)),
                    right: Box::new(OldMachineTerm::constant(0)),
                },
                true,
            )),
        ),
    );
    let state = ExecutionState::new();
    let spelled = synthesize_surface_proposition(&requirement, ParameterBinding::default(), &state)
        .expect("the negative shape should remain spellable");
    assert!(matches!(
        &spelled,
        SyntaxProposition::Exists {
            body,
            ..
        } if matches!(body.as_ref(), SyntaxProposition::And(left, _) if matches!(left.as_ref(), SyntaxProposition::And(..)))
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
        let guard = Proposition::condition_is(
            OldConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: Box::new(OldMachineTerm::Variable(variable)),
                right: Box::new(OldMachineTerm::constant(1)),
            },
            false,
        );
        let comparison = Proposition::condition_is(
            OldConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(OldMachineTerm::constant(0)),
                right: Box::new(binary_node!(
                    Int32,
                    Add,
                    Box::new(OldMachineTerm::Variable(variable)),
                    Box::new(OldMachineTerm::constant(1)),
                )),
            },
            true,
        );
        let mut body = comparison;
        for _ in 0..guard_count {
            body = Proposition::And(Box::new(guard.clone()), Box::new(body));
        }
        crate::kernel::quantifiers::test_exists(
            "len".to_string(),
            variable,
            Sort::ProgramInt32,
            body,
        )
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
                SyntaxProposition::Exists { body, .. }
                    if matches!(body.as_ref(), SyntaxProposition::And(left, _) if matches!(left.as_ref(), SyntaxProposition::Defined { .. }))
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
    let base = Address::new(
        AddressBase::Concrete("job".into()),
        AddressOffset::constant(0),
    );
    let owner = ProgramValue::typed_pointer(base.clone(), ProgramType::VoidPointer);
    let field_pointer = base.offset_by_bytes(layout.fields()["selected"].offset_bytes());
    let selected = AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(711)), 4);
    let decoy = AddressOffset::scale_int32(OldMachineTerm::Variable(Variable(712)), 4);
    let value = |offset| {
        ProgramValue::typed_pointer(
            Address::new(AddressBase::ExternalArgument, offset),
            ProgramType::Int32Pointer,
        )
    };
    let memory = SymbolicMemory::new()
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
            &selected.clone(),
            ParameterBinding::new(function.parameters(), &arguments),
            &state,
        )
        .expect("the actual pointer field must have a spelling");
        assert!(matches!(&spelled, SyntaxTerm::Field { field, .. } if field == "selected"));
        let equality = SyntaxProposition::Comparison {
            left: spelled,
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(value(selected.clone()))),
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
                &selected.clone(),
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
        AddressOffset::scaled_int32_node(OldMachineTerm::Variable(Variable(variable)), 4)
    };
    let external =
        |offset: crate::kernel::AddressOffset| Address::new(AddressBase::ExternalArgument, offset);
    let (arena, occupied, index) = (200_000, 200_001, 200_002);
    let state = ExecutionState::new().with_local(
        "arena",
        ProgramValue::typed_pointer(external(scaled(arena)), ProgramType::Int32Pointer),
    );
    let unrelated_cell = external(AddressOffset::raw_add(scaled(occupied), scaled(index)));
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
    let own_cell = external(AddressOffset::raw_add(scaled(arena), scaled(index)));
    let bound = (BTreeMap::<_, String>::from([(Variable(index), "k".to_string())]))
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
    let Some(SyntaxTerm::Index(base, _)) = synthesize_local_indexed_load(
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
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable(("arena".to_string()).into()))
    );
}

/// A `uint32` order is spelled as the unsigned comparison over the `uint32`
/// local, and it lowers back to the condition it was spelled from. A signed
/// local needs an explicit uint32 cast to preserve the unsigned
/// interpretation.
#[test]
fn unsigned_comparison_is_spelled_over_uint32_operands() {
    let x = OldMachineTerm::Variable(Variable(300_000));
    let state = ExecutionState::new().with_local("x", ProgramValue::UInt32(x.clone()));
    for (condition, spelling) in [
        (
            OldConditionTerm::unsigned_less_than(x.clone(), OldMachineTerm::constant(4)),
            "x < 4",
        ),
        (
            OldConditionTerm::unsigned_greater_equal(x.clone(), OldMachineTerm::constant(4)),
            "x >= 4",
        ),
    ] {
        for value in [true, false] {
            let fact = Proposition::condition_is(condition.clone(), value);
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
    let fact = Proposition::condition_is(
        OldConditionTerm::unsigned_less_than(
            OldMachineTerm::sign_cast32(MachineIntegerType::Int32, MachineIntegerType::UInt32, x),
            OldMachineTerm::constant(4),
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
        [300_010, 300_011, 300_012].map(|id| OldMachineTerm::Variable(Variable(id)));
    let state = ExecutionState::new()
        .with_local("x", ProgramValue::Int32(x.clone()))
        .with_local("divisor", ProgramValue::Int32(divisor.clone()))
        .with_local("result", ProgramValue::Int32(result.clone()));
    // The signed locals' unsigned readings are σ, a node of its own.
    let unsigned = |value| {
        OldMachineTerm::sign_cast32(MachineIntegerType::Int32, MachineIntegerType::UInt32, value)
    };
    let quotient = binary_node!(
        UInt32,
        Divide,
        Box::new(OldMachineTerm::uint32_constant(u32::MAX)),
        Box::new(unsigned(divisor.clone())),
    );
    let remainder = binary_node!(
        UInt32,
        Remainder,
        Box::new(unsigned(x.clone())),
        Box::new(unsigned(divisor))
    );
    for condition in [
        OldConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left: Box::new(quotient.clone()),
            right: Box::new(unsigned(result.clone())),
        },
        OldConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left: Box::new(remainder),
            right: Box::new(unsigned(result)),
        },
        OldConditionTerm::unsigned_less_equal(unsigned(x), quotient),
    ] {
        for polarity in [true, false] {
            let fact = Proposition::condition_is(condition.clone(), polarity);
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
                lowered.old_form(),
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
fn pure_sequence_membership_round_trips_its_operands_and_negation() {
    let element = |value| SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(value)));
    let literal = |value| SyntaxTerm::SequenceLiteral(vec![element(value)]);
    let empty = SyntaxTerm::SequenceLiteral(vec![]);
    let concat = |left, right| SyntaxTerm::SequenceConcat(Box::new(left), Box::new(right));
    let membership = SyntaxProposition::Comparison {
        left: element(2),
        operator: ComparisonOperator::In,
        right: concat(empty, concat(literal(1), literal(2))),
    };
    let state = ExecutionState::new();
    for written in [
        membership.clone(),
        SyntaxProposition::Not(Box::new(membership)),
    ] {
        let lowered = relower_written_proposition(&written, &state).unwrap();
        let atom = match &lowered {
            Proposition::Not(body) => body.as_ref(),
            atom => atom,
        };
        assert!(matches!(atom, Proposition::SequenceMembership { .. }));
        let raised =
            synthesize_surface_proposition(&lowered, ParameterBinding::default(), &state).unwrap();
        assert_eq!(raised, written);
        assert_eq!(
            relower_written_proposition(&raised, &state).unwrap(),
            lowered
        );
    }
}

#[test]
fn pure_sequence_equality_round_trips_empty_and_nested_concatenation() {
    let literal = |value| {
        SyntaxTerm::SequenceLiteral(vec![SyntaxTerm::ProgramExpression(
            ProgramExpression::Value(int32(value)),
        )])
    };
    let empty = SyntaxTerm::SequenceLiteral(vec![]);
    let concat = |left, right| SyntaxTerm::SequenceConcat(Box::new(left), Box::new(right));
    let written = SyntaxProposition::Comparison {
        left: concat(empty.clone(), concat(literal(1), literal(2))),
        operator: ComparisonOperator::Equal,
        right: concat(concat(literal(1), literal(2)), empty),
    };
    let state = ExecutionState::new();
    let lowered = relower_written_proposition(&written, &state).unwrap();
    assert!(matches!(
        lowered,
        Proposition::Equal(Term::Sequence(_), Term::Sequence(_))
    ));
    let raised =
        synthesize_surface_proposition(&lowered, ParameterBinding::default(), &state).unwrap();
    assert_eq!(raised, written);
    assert_eq!(
        relower_written_proposition(&raised, &state).unwrap(),
        lowered
    );
    assert_eq!(
        crate::surface::printing::source_click_proposition(&raised),
        "[] ++ ([1] ++ [2]) == [1] ++ [2] ++ []",
    );
}

#[test]
fn synthesized_uint32_cast_preserves_its_state() {
    let selector = ProgramPointSelector::Mark("before".into());
    let expression = synthesize_uint32_operand(SyntaxTerm::At {
        selector: selector.clone(),
        expression: Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
            "x".into(),
        ))),
    })
    .unwrap();
    assert!(matches!(&expression, SyntaxTerm::At { selector: actual, .. } if actual == &selector));
    let surface = SyntaxProposition::Comparison {
        left: expression,
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt32(
            OldMachineTerm::constant(u32::MAX),
        ))),
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
            ProgramValue::Int64(OldMachineTerm::int64_constant(8589934592)),
        ),
        (
            "uint64",
            ProgramType::UInt64,
            ProgramType::UInt64Pointer,
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(8589934592)),
        ),
    ] {
        let function = syntax::parse_function(&format!("void read({spelling} *p) {{ }}")).unwrap();
        let base = Address::new(
            AddressBase::Concrete("wide".into()),
            AddressOffset::constant(0),
        );
        let argument = ProgramValue::typed_pointer(base.clone(), pointer_type);
        let state = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block("wide", 32))
            .with_local("p", argument.clone());
        for offset in [0, 8, 24] {
            let address = ProgramExpression::Value(ProgramValue::typed_pointer(
                base.offset_by_bytes(offset),
                pointer_type,
            ));
            let written = SyntaxProposition::Comparison {
                left: SyntaxTerm::ProgramExpression(ProgramExpression::TypedLoad {
                    pointer: Box::new(address),
                    value_type,
                    volatile: false,
                    pointee_constant: false,
                    access_class: None,
                    source: Default::default(),
                }),
                operator: ComparisonOperator::LessThan,
                right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(constant.clone())),
            };
            let fact = relower_written_proposition(&written, &state).unwrap();
            let Proposition::ConditionIs(condition, _) = fact else {
                panic!("native order")
            };
            for truth in [true, false] {
                let fact = Proposition::condition_is(condition.clone(), truth);
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
    let pointer = Address::new(
        AddressBase::Concrete("item".into()),
        AddressOffset::constant(0),
    );
    let value = ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer);
    let state = ExecutionState::new().with_local("p", value.clone());
    let arguments = [ProgramExpression::Value(value)];
    let plain = synthesize_struct_loadable_segment(
        &pointer.offset_by_bytes(4),
        &OldMachineTerm::constant(4),
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
        &OldMachineTerm::constant(4),
        ParameterBinding::new(&[parameter], &arguments),
        &state,
    )
    .unwrap();
    assert!(matches!(
        &clipped,
        SyntaxProposition::Loadable {
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
fn a_pointer_a_local_no_longer_holds_is_spelled_where_it_was_introduced() {
    // `q = view(p); q = r;` leaves the value `view` returned in no local, so
    // the current state cannot name it; the point after the first call held
    // it in `q`, so `at(that point, q) != NULL` spells the fact `view`'s
    // contract gave about it.
    let returned = Address::new(
        AddressBase::Symbolic(Variable(910_001)),
        AddressOffset::constant(0),
    );
    let other = Address::new(
        AddressBase::Concrete("pointer-introduced-other".into()),
        AddressOffset::constant(0),
    );
    let memory = SymbolicMemory::new().with_block("pointer-introduced-other", 4);
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
    let fact = Proposition::condition_is(
        OldConditionTerm::AddressEqual(Box::new(returned), Box::new(Address::null())),
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
fn entry_model_raising_uses_the_binder_that_minted_the_field() {
    use crate::kernel::{
        AlgebraicTerm, AlgebraicTermNode, AlgebraicValue, Resource, ResourceContext, ResourceFact,
        ResourceFieldSchema, ResourceFieldType, ResourceInstance, TypeParameterName,
        model_fields::{self, ModelFieldOrigin, ModelMint},
    };

    let _session = crate::kernel::VerificationSession::enter();
    let identity = crate::kernel::InstanceId::from_variable(Variable(930_011));
    let model_variable = Variable(930_012);
    let model = AlgebraicTerm {
        algebraic_type: TypeParameterName::intern("Tree").algebraic_type(),
        node: AlgebraicTermNode::Variable(model_variable),
    };
    let size = Variable(930_013);
    let schema = ResourceFieldSchema::new(vec![
        (
            "model".into(),
            ResourceFieldType::Algebraic(model.algebraic_type.clone()),
        ),
        (
            "size".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        ),
    ])
    .unwrap();
    let instance = ResourceInstance::new(
        identity,
        "tree".into(),
        vec![].into(),
        schema,
        vec![
            AlgebraicValue::Algebraic(model.clone()),
            AlgebraicValue::Program(ProgramValue::Int32(OldMachineTerm::Variable(size))),
        ]
        .into(),
    )
    .unwrap();
    let entry = ExecutionState::new().with_resource_context(
        ResourceContext::new().unchecked_with_fact(ResourceFact::own(Resource::Instance(instance))),
    );
    let _entry = SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(entry))));
    // A different binder registered this identity before the current contract.
    model_fields::register_instance_spelling(identity, "after");
    for (field_index, (variable, field)) in [(model_variable, "model"), (size, "size")]
        .into_iter()
        .enumerate()
    {
        model_fields::register_model_field_variable(
            variable,
            ModelFieldOrigin {
                identity,
                field: field.into(),
                field_index,
                minted_by: ModelMint::ContractEntry { owner: "t".into() },
            },
        );
    }
    let current = ExecutionState::new();
    let model = synthesize_surface_algebraic(
        &model,
        ParameterBinding::default(),
        &current,
        &BTreeMap::new(),
    )
    .unwrap();
    let size = synthesize_scalar_model_field(size, &current).unwrap();
    for (raised, name) in [(model, "model"), (size, "size")] {
        let SyntaxTerm::Old(inner) = raised else {
            panic!("the entry field must raise through old: {raised:?}");
        };
        assert!(
            matches!(*inner, SyntaxTerm::ResourceField(ref access)
                if access.owner == "t" && access.field == name),
            "{inner:?}"
        );
    }
}

#[test]
fn a_model_field_value_its_instance_no_longer_holds_is_spelled_where_it_was_introduced() {
    // A call replaces `o`'s model, so the earlier `o.size` value is held by
    // no current instance; the point after the first call held it.
    use crate::kernel::{
        AlgebraicValue, Resource, ResourceContext, ResourceFact, ResourceFieldSchema,
        ResourceFieldType, ResourceInstance,
    };
    let identity = crate::kernel::InstanceId::from_variable(Variable(930_001));
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
                OldMachineTerm::Variable(value),
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
    let fact = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(OldMachineTerm::Variable(earlier)),
            right: Box::new(OldMachineTerm::constant(5)),
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
    let SyntaxProposition::Comparison { left, .. } = &spelled else {
        panic!("the fact must be spelled as a comparison: {spelled:?}");
    };
    let SyntaxTerm::At {
        selector,
        expression,
    } = left
    else {
        panic!("the earlier field value must be read at a recorded point: {spelled:?}");
    };
    assert_eq!(selector, &point(0));
    assert!(
        matches!(expression.as_ref(), SyntaxTerm::ResourceField(field) if field.field == "size"),
        "the value must be spelled as the instance's field: {spelled:?}"
    );
}

#[test]
fn recorded_cells_offer_the_points_that_held_a_value_newest_first() {
    // A value two stores put in a cell, between which a store overwrote
    // it, is offered at both points that recorded it there, newest first;
    // a value no cell held is offered nowhere.
    let cell = Address::new(
        AddressBase::Concrete("cell-introduced".into()),
        AddressOffset::constant(0),
    );
    let value = OldMachineTerm::Variable(Variable(940_001));
    let point = |index| {
        ProgramPointSelector::from(ProgramPointRef {
            region: CodeRegionRef::Region(index),
            kind: ProgramPointKind::Exit,
        })
    };
    let entry = SymbolicMemory::new()
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
    let offered = |term: &OldMachineTerm| {
        recorded_states
            .points_holding_cell_integer(term)
            .map(|(selector, _)| selector.clone())
            .collect::<Vec<_>>()
    };
    assert_eq!(offered(&value), vec![point(3), point(1)]);
    assert!(offered(&OldMachineTerm::Variable(Variable(940_002))).is_empty());
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
    let first = Address::new(AddressBase::Heap(989_030), AddressOffset::constant(0));
    let second = Address::new(AddressBase::Heap(989_031), AddressOffset::constant(0));
    let state = |pointer: &Address| {
        ExecutionState::new().with_local(
            crate::kernel::BindingName::Local(crate::kernel::LocalBindingId::new(
                crate::kernel::LocalFunctionId::new(None, "f".into()),
                false,
                0,
                Some("p".into()),
            )),
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
    let current = state(&Address::null());
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
        Some(SyntaxTerm::RegionAllocation(point.region.clone()))
    );
    let surface = SyntaxProposition::Comparison {
        left: SyntaxTerm::RegionAllocation(point.region.clone()),
        operator: ComparisonOperator::Equal,
        right: SyntaxTerm::QualifiedC {
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
    // Lowering is structural: the two spellings of one allocation keep
    // their comparison, which checking decides.
    assert_eq!(
        lowered,
        Proposition::condition_is(
            OldConditionTerm::AddressEqual(Box::new(first.clone()), Box::new(first.clone())),
            true
        )
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
    let pointer = SymbolicMemory::global_pointer("g").offset_by_bytes(12);
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
        &OldMachineTerm::constant(1),
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
    let i = OldMachineTerm::Variable(Variable(989_971));
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
                OldMachineTerm::constant(0),
            ),
            (
                ProgramType::Int64Pointer,
                MachineIntegerType::Int64,
                8,
                crate::kernel::LoadKind::Bits64,
                OldMachineTerm::int64_constant(0),
            ),
        ] {
            for increment in [false, true] {
                let value = match format {
                    MachineIntegerType::Int32 => ProgramValue::Int32(i.clone()),
                    MachineIntegerType::UInt32 => ProgramValue::UInt32(i.clone()),
                    MachineIntegerType::UInt64 => ProgramValue::UInt64(i.clone()),
                    _ => unreachable!(),
                };
                let base = Address::new(
                    AddressBase::Concrete("indexed-array".into()),
                    AddressOffset::constant(0),
                );
                let state = ExecutionState::new()
                    .with_memory(SymbolicMemory::new().with_block("indexed-array", 128))
                    .with_local("a", ProgramValue::typed_pointer(base.clone(), pointer_type))
                    .with_local("i", value);
                let index = if increment {
                    let one = match format {
                        MachineIntegerType::Int32 => OldMachineTerm::constant(1),
                        MachineIntegerType::UInt32 => OldMachineTerm::uint32_constant(1),
                        _ => OldMachineTerm::uint64_constant(1),
                    };
                    OldMachineTerm::Binary {
                        format,
                        op: crate::kernel::MachineBinaryOp::Add,
                        left: Box::new(i.clone()),
                        right: Box::new(one),
                    }
                } else {
                    i.clone()
                };
                let offset = match format {
                    MachineIntegerType::Int32 => AddressOffset::scaled_int32_node(index, width),
                    MachineIntegerType::UInt32 => AddressOffset::scaled_int64_node(
                        OldMachineTerm::legacy_cast(
                            MachineCastSpelling::UInt64From32,
                            Box::new(index),
                        ),
                        width,
                        true,
                    ),
                    _ => AddressOffset::scaled_int64_node(index, width, true),
                };
                let load = OldMachineTerm::read_named(
                    crate::kernel::ProgramPoint::at(
                        &(crate::kernel::intern_memory_ref(state.memory())),
                    ),
                    Box::new(base.with_offset(offset)),
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
                assert!(matches!(&spelled, SyntaxTerm::Index(..)), "{spelled:?}");
                let text = crate::surface::diagnostics::describe_contract_expression(&spelled);
                assert!(!text.contains(" as "), "{text}");
                if !increment {
                    assert_eq!(text, "a[i]");
                }
                let right =
                    SyntaxTerm::ProgramExpression(ProgramExpression::Value(if width == 8 {
                        ProgramValue::Int64(zero.clone())
                    } else {
                        ProgramValue::Int32(zero.clone())
                    }));
                let surface = SyntaxProposition::Comparison {
                    left: spelled,
                    operator: ComparisonOperator::Equal,
                    right: right.clone(),
                };
                let expected = Proposition::condition_is(
                    OldConditionTerm::Compare {
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
                let reparsed = SyntaxProposition::Comparison {
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
    let flag = OldConditionTerm::Variable(Variable(9001));
    let x = OldMachineTerm::Variable(Variable(9002));
    let state = ExecutionState::new()
        .with_local("flag", ProgramValue::of_bool(flag.clone()))
        .with_local("x", ProgramValue::Int32(x.clone()));
    let positive = OldConditionTerm::bool_application(
        "positive",
        vec![crate::kernel::PureFunctionArgument::Value(
            ProgramValue::Int32(x.clone()),
        )],
    );
    let chosen = OldConditionTerm::bool_application(
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
        OldConditionTerm::bool_if(flag, positive.clone(), OldConditionTerm::Constant(false)),
        OldConditionTerm::bool_equal(positive.clone(), OldConditionTerm::bool_not(positive)),
        OldConditionTerm::BoolEqual(
            Box::new(OldConditionTerm::Constant(true)),
            Box::new(OldConditionTerm::Constant(false)),
        ),
    ] {
        for truth in [false, true] {
            let root = crate::kernel::KernelTermImport::default().condition(&condition);
            let retained = Proposition::ConditionIs(
                crate::kernel::StoredConditionTerm::from_root(root.clone()).unwrap(),
                truth,
            );
            let fact = condition.truth_claim(truth);
            let surface =
                synthesize_surface_proposition(&retained, ParameterBinding::default(), &state)
                    .expect("retained Bool fact spelling");
            assert!(!root.has_cached_native_argument());
            let lowered = crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
                &surface, &PureFactContext::new(), ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
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
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(99001))),
        );
        let values = ProgramValueBindings::from([(
            "x".to_string(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(99001))),
        )]);
        let lower = |proposition: &SyntaxProposition| {
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
    let pointer = Address::new(
        AddressBase::Concrete("square".into()),
        AddressOffset::constant(0),
    );
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
    let expected = SyntaxProposition::Defined {
        expression: SyntaxTerm::ProgramExpression(ProgramExpression::TypedLoad {
            pointer: Box::new(ProgramExpression::PointerOffsetBytes {
                pointer: Box::new(ProgramExpression::Variable("p".into())),
                bytes: 8.into(),
            }),
            value_type: ProgramType::Int32,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        }),
    };
    let surface = SyntaxProposition::Defined { expression: load };
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
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
            OldConditionTerm::IntegerEqual,
            OldConditionTerm::IntegerNotEqual,
            OldConditionTerm::IntegerLessThan,
            OldConditionTerm::IntegerLessEqual,
            OldConditionTerm::IntegerGreaterThan,
            OldConditionTerm::IntegerGreaterEqual,
        ] {
            for truth in [false, true] {
                let goal = Proposition::condition_is(
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
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
        let value = ProgramValue::Int32(OldMachineTerm::Variable(Variable(99002)));
        let state = ExecutionState::new().with_local("x", value.clone());
        let values = ProgramValueBindings::from([("x".to_string(), value)]);
        let lower = |proposition: &SyntaxProposition| {
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
    let names = (BTreeMap::<_, String>::from([(variable, "a".into())]))
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
    let bindings = PersistentBinderMap::default().with_inserted(
        "a",
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

fn local_read_test_address(name: &str) -> Address {
    Address::new(
        AddressBase::Concrete(format!("local:{name}")),
        AddressOffset::constant(0),
    )
}

fn local_test_read_operand(claim: &Proposition, value_type: ProgramType) -> &OldMachineTerm {
    let term = match claim.old_condition() {
        Some((OldConditionTerm::Compare { left, .. }, true)) => left,
        Some((OldConditionTerm::IntegerLessEqual(left, _), true)) => {
            let crate::kernel::IntegerTerm::Machine(observation) = &**left else {
                panic!("expected an exact Integer observation: {left:?}");
            };
            assert_eq!(observation.ty().program_type(), value_type);
            observation.value()
        }
        _ => panic!("read comparison: {claim:?}"),
    };
    if let Some((source, operand)) = term.narrow_widening32_operand()
        && source.program_type() == value_type
    {
        return operand;
    }
    term
}

fn local_read_test_store(
    state: &ExecutionState,
    pointer: &Address,
    value_type: ProgramType,
    bits: u32,
) -> ExecutionState {
    let value = match value_type {
        ProgramType::Int8 => ProgramValue::Int8(OldMachineTerm::narrow_constant(
            MachineIntegerType::Int8,
            u128::from(bits & 0xff),
        )),
        ProgramType::UInt8 => ProgramValue::UInt8(OldMachineTerm::narrow_constant(
            MachineIntegerType::UInt8,
            u128::from(bits & 0xff),
        )),
        ProgramType::Int16 => ProgramValue::Int16(OldMachineTerm::narrow_constant(
            MachineIntegerType::Int16,
            u128::from(bits & 0xffff),
        )),
        ProgramType::UInt16 => ProgramValue::UInt16(OldMachineTerm::narrow_constant(
            MachineIntegerType::UInt16,
            u128::from(bits & 0xffff),
        )),
        ProgramType::Int32 => ProgramValue::Int32(OldMachineTerm::constant(bits)),
        ProgramType::UInt32 => ProgramValue::UInt32(OldMachineTerm::uint32_constant(bits)),
        ProgramType::Int64 => ProgramValue::Int64(OldMachineTerm::int64_constant(i64::from(bits))),
        ProgramType::UInt64 => {
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(u64::from(bits)))
        }
        ProgramType::Int128 | ProgramType::UInt128 => {
            let format = MachineIntegerType::from_program_type(value_type).unwrap();
            format
                .constant_value(
                    crate::kernel::MachineIntegerConstant::from_bits(
                        format.format(),
                        u128::from(bits),
                    )
                    .unwrap(),
                )
                .unwrap()
        }
        _ => unreachable!("indexed local test type"),
    };
    state
        .clone()
        .with_memory(state.memory().clone().store(pointer.clone(), value))
}

fn local_read_test_claim(value_type: ProgramType) -> SyntaxProposition {
    let limit = match value_type {
        ProgramType::UInt32 => ProgramValue::UInt32(OldMachineTerm::uint32_constant(20)),
        ProgramType::Int64 => ProgramValue::Int64(OldMachineTerm::int64_constant(20)),
        ProgramType::UInt64 => ProgramValue::UInt64(OldMachineTerm::uint64_constant(20)),
        _ => int32(20),
    };
    SyntaxProposition::Comparison {
        left: SyntaxTerm::CUnary {
            operand: Box::new(SyntaxTerm::ProgramExpression(ProgramExpression::Variable(
                "p".into(),
            ))),
            lowered: ProgramExpression::TypedLoad {
                pointer: Box::new(ProgramExpression::Value(int32(0))),
                value_type,
                volatile: false,
                pointee_constant: false,
                access_class: None,
                source: Default::default(),
            },
        },
        operator: ComparisonOperator::LessEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(limit)),
    }
}

#[test]
fn exact_read_raises_at_its_own_point_when_another_point_has_equal_memory() {
    let _session = crate::kernel::VerificationSession::enter();
    let slot = local_read_test_address("slot");
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block("local:slot", 4))
        .with_local(
            "p",
            ProgramValue::typed_pointer(slot.clone(), ProgramType::Int32Pointer),
        );
    let first = local_read_test_store(&state, &slot, ProgramType::Int32, 7);
    let second = local_read_test_store(&first, &slot, ProgramType::Int32, 7);
    assert_eq!(first.memory(), second.memory());

    let mut claim = local_read_test_claim(ProgramType::Int32);
    let SyntaxProposition::Comparison { left, .. } = &mut claim else {
        unreachable!("test comparison");
    };
    *left = SyntaxTerm::Exact(Box::new(left.clone()));
    let exact = relower_written_proposition(&claim, &first).unwrap();
    let read = local_test_read_operand(&exact, ProgramType::Int32);
    let OldMachineTerm::MemoryLoad(point, ..) = read else {
        panic!("expected exact read: {read:?}");
    };
    assert!(point.is_exact_read());
    assert_eq!(point.read_version_id(), first.program_point_id());
    assert_ne!(exact, relower_written_proposition(&claim, &second).unwrap());

    let selector = ProgramPointSelector::Mark("first".into());
    let mut points = RecordedStates::new();
    points.insert(selector.clone(), first);
    let _points = SynthesisRecordedPointsScope::enter(&points);
    let root = crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, read);
    let raised = raise_kernel_term(
        &root,
        ParameterBinding::default(),
        &second,
        &BTreeMap::new(),
    )
    .expect("the exact read has a recorded point");
    // At `first` the place's ordinary read selects `first` itself, the same
    // read key as the exact read, so the read is spelled plainly there: the
    // spelling depends on the read's key, not on its selection kind.
    assert!(
        matches!(&raised, SyntaxTerm::At { selector: at, expression }
        if at == &selector && !matches!(expression.as_ref(), SyntaxTerm::Exact(_)))
    );
    let SyntaxProposition::Comparison { left, .. } = &mut claim else {
        unreachable!("test comparison");
    };
    *left = raised;
    assert_eq!(
        relower_written_proposition_with_states(&claim, &second, &second, &points),
        Ok(exact)
    );
}

#[test]
fn ordinary_indexed_integer_reads_select_the_write_on_their_own_path() {
    check_local_read_versions(ProgramType::Int8, ProgramType::UInt8);
    check_local_read_versions(ProgramType::UInt8, ProgramType::Int8);
    check_local_read_versions(ProgramType::Int16, ProgramType::UInt16);
    check_local_read_versions(ProgramType::UInt16, ProgramType::Int16);
    check_local_read_versions(ProgramType::UInt8, ProgramType::Int32);
    check_local_read_versions(ProgramType::Int32, ProgramType::UInt8);
    check_local_read_versions(ProgramType::Int32, ProgramType::UInt32);
    check_local_read_versions(ProgramType::UInt32, ProgramType::Int32);
    check_local_read_versions(ProgramType::Int64, ProgramType::Int32);
    check_local_read_versions(ProgramType::UInt64, ProgramType::UInt32);
    check_local_read_versions(ProgramType::Int128, ProgramType::UInt128);
    check_local_read_versions(ProgramType::UInt128, ProgramType::Int128);
}

fn check_local_read_versions(value_type: ProgramType, disjoint_type: ProgramType) {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer_type = match value_type {
        ProgramType::Int8 => ProgramType::Int8Pointer,
        ProgramType::UInt8 => ProgramType::UInt8Pointer,
        ProgramType::Int16 => ProgramType::Int16Pointer,
        ProgramType::UInt16 => ProgramType::UInt16Pointer,
        ProgramType::Int32 => ProgramType::Int32Pointer,
        ProgramType::UInt32 => ProgramType::UInt32Pointer,
        ProgramType::Int64 => ProgramType::Int64Pointer,
        ProgramType::UInt64 => ProgramType::UInt64Pointer,
        ProgramType::Int128 => ProgramType::Int128Pointer,
        ProgramType::UInt128 => ProgramType::UInt128Pointer,
        _ => unreachable!("indexed local test type"),
    };
    let slot = local_read_test_address("slot");
    let other = local_read_test_address("other");
    let load_kind = crate::kernel::LoadKind::of_type(value_type).unwrap();
    let start = ExecutionState::new()
        .with_memory(
            SymbolicMemory::new()
                .with_block("local:slot", value_type.byte_width())
                .with_block("local:other", disjoint_type.byte_width()),
        )
        .with_local("p", ProgramValue::typed_pointer(slot.clone(), pointer_type));
    let left_write = local_read_test_store(&start, &slot, value_type, 7);
    let right_write = local_read_test_store(&start, &slot, value_type, 7);
    let left = local_read_test_store(&left_write, &other, disjoint_type, 1);
    let right = local_read_test_store(&right_write, &other, disjoint_type, 1);
    assert_eq!(left.memory(), right.memory());
    assert_ne!(
        left_write.program_point_id(),
        right_write.program_point_id()
    );

    let claim = local_read_test_claim(value_type);
    let selectors = [
        ProgramPointSelector::Mark("left_write".into()),
        ProgramPointSelector::Mark("right_write".into()),
    ];
    let mut points = RecordedStates::new();
    points.insert(selectors[0].clone(), left_write.clone());
    points.insert(selectors[1].clone(), right_write.clone());
    let _points = SynthesisRecordedPointsScope::enter(&points);

    let mut roots = Vec::new();
    for (reader, write, other_path, selector) in [
        (&left, &left_write, &right, &selectors[0]),
        (&right, &right_write, &left, &selectors[1]),
    ] {
        let lowered = relower_written_proposition(&claim, reader).unwrap();
        let read = local_test_read_operand(&lowered, value_type);
        let OldMachineTerm::MemoryLoad(point, _, kind) = read else {
            panic!("ordinary {value_type:?} read: {read:?}");
        };
        assert_eq!(*kind, load_kind);
        assert_eq!(point.id(), write.program_point_id());
        let root = crate::kernel::KernelTermImport::default().machine(
            MachineIntegerType::from_program_type(value_type).unwrap(),
            read,
        );
        assert!(
            matches!(root.node(), crate::kernel::KernelTermNode::MemoryLoad { point, .. }
            if point.id() == write.program_point_id())
        );
        let raised = raise_kernel_term(
            &root,
            ParameterBinding::default(),
            other_path,
            &BTreeMap::new(),
        )
        .expect("a named version has an ordinary read spelling");
        assert!(matches!(&raised, SyntaxTerm::At { selector: at, .. } if at == selector));
        let mut replay = claim.clone();
        let SyntaxProposition::Comparison { left, .. } = &mut replay else {
            unreachable!("test comparison")
        };
        *left = raised;
        assert_eq!(
            relower_written_proposition_with_states(&replay, other_path, other_path, &points),
            Ok(lowered)
        );
        roots.push(root);
    }
    assert_ne!(roots[0], roots[1]);

    let repeated = local_read_test_store(&left, &slot, value_type, 7);
    assert_eq!(left.memory(), repeated.memory());
    assert_eq!(
        repeated
            .program_point()
            .indexed_integer_version(&slot, load_kind)
            .unwrap()
            .id(),
        repeated.program_point_id()
    );
    let mismatched = local_read_test_store(&left, &slot, disjoint_type, 7);
    assert!(
        mismatched
            .program_point()
            .indexed_integer_version(&slot, load_kind)
            .is_none(),
        "a write with a different load kind ends the prior version"
    );

    let possibly_aliasing =
        local_read_test_store(&left, &Address::symbolic(Variable(981_640)), value_type, 9);
    assert!(
        possibly_aliasing
            .program_point()
            .indexed_integer_version(&slot, load_kind)
            .is_none(),
        "an unclassified store cannot keep an indexed version"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn ordinary_indexed_integer_read_work_is_bounded_as_path_grows() {
    check_local_read_work(ProgramType::Int8, ProgramType::UInt8);
    check_local_read_work(ProgramType::Int16, ProgramType::UInt16);
    check_local_read_work(ProgramType::UInt16, ProgramType::Int16);
    check_local_read_work(ProgramType::UInt8, ProgramType::Int32);
    check_local_read_work(ProgramType::Int32, ProgramType::UInt32);
    check_local_read_work(ProgramType::UInt32, ProgramType::Int32);
    check_local_read_work(ProgramType::Int64, ProgramType::Int32);
    check_local_read_work(ProgramType::UInt64, ProgramType::UInt32);
    check_local_read_work(ProgramType::Int128, ProgramType::UInt128);
    check_local_read_work(ProgramType::UInt128, ProgramType::Int128);
}

#[test]
fn whole_static_read_selects_and_replays_its_recorded_store() {
    let _session = crate::kernel::VerificationSession::enter();
    let scalar = SymbolicMemory::global_pointer("counter");
    let other = SymbolicMemory::global_pointer("other_counter");
    let ty = ProgramType::Int32;
    let entry = ExecutionState::new()
        .with_memory(
            SymbolicMemory::new()
                .with_block(scalar.base.clone(), 4)
                .with_block(other.base.clone(), 4),
        )
        .with_local(
            "p",
            ProgramValue::typed_pointer(scalar.clone(), ProgramType::Int32Pointer),
        )
        .begin_function_entry_memory();
    let written = local_read_test_store(&entry, &scalar, ty, 7);
    let claim = local_read_test_claim(ty);
    let expected = relower_written_proposition(&claim, &written).unwrap();
    let read = local_test_read_operand(&expected, ty);
    let OldMachineTerm::MemoryLoad(point, _, crate::kernel::LoadKind::Int32) = read else {
        panic!("whole static read: {read:?}");
    };
    assert_eq!(point.read_version_id(), written.program_point_id());

    let work = [1, 8, 64, 256].map(|count| {
        let mut reader = written.clone();
        for value in 0..count {
            reader = local_read_test_store(&reader, &other, ty, value);
        }
        let (lowered, work) = crate::instrumentation::measure_deterministic_work(|| {
            relower_written_proposition(&claim, &reader).unwrap()
        });
        assert_eq!(lowered, expected);
        work
    });
    assert!(work.iter().all(|units| *units <= work[0] + 8), "{work:?}");

    let replaced = local_read_test_store(&written, &scalar, ty, 7);
    assert_eq!(written.memory(), replaced.memory());
    assert_ne!(
        relower_written_proposition(&claim, &replaced).unwrap(),
        expected
    );
    let selector = ProgramPointSelector::Mark("written".into());
    let mut points = RecordedStates::new();
    points.insert(selector.clone(), written.clone());
    let _points = SynthesisRecordedPointsScope::enter(&points);
    let root = crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, read);
    let raised = raise_kernel_term(
        &root,
        ParameterBinding::default(),
        &replaced,
        &BTreeMap::new(),
    )
    .expect("the earlier static read has a recorded spelling");
    assert!(matches!(&raised, SyntaxTerm::At { selector: at, .. } if at == &selector));
    let mut replay = claim;
    let SyntaxProposition::Comparison { left, .. } = &mut replay else {
        unreachable!("test comparison");
    };
    *left = raised;
    assert_eq!(
        relower_written_proposition_with_states(&replay, &replaced, &replaced, &points),
        Ok(expected)
    );

    let partial = local_read_test_store(&written, &scalar, ProgramType::UInt8, 7);
    assert!(
        partial
            .program_point()
            .ordinary_typed_version(&scalar, ty)
            .is_none()
    );

    let alias = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let may_alias = local_read_test_store(&written, &alias, ty, 9);
    assert!(
        may_alias
            .program_point()
            .ordinary_typed_version(&scalar, ty)
            .is_none()
    );
}

#[test]
fn ordinary_fixed_offset_read_keeps_its_version_across_sibling_stores() {
    let _session = crate::kernel::VerificationSession::enter();
    let left = local_read_test_address("pair");
    let right = left.with_offset(AddressOffset::constant(4));
    let ty = ProgramType::Int32;
    let entry = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block("local:pair", 8))
        .with_local(
            "p",
            ProgramValue::typed_pointer(right.clone(), ProgramType::Int32Pointer),
        );
    let written = local_read_test_store(&entry, &right, ty, 7);
    let selector = ProgramPointSelector::Mark("written".into());
    let mut points = RecordedStates::new();
    points.insert(selector.clone(), written.clone());
    let _points = SynthesisRecordedPointsScope::enter(&points);
    let claim = local_read_test_claim(ty);

    let mut work = Vec::new();
    for count in [4, 64, 1024] {
        let mut reader = written.clone();
        for value in 0..count {
            reader = local_read_test_store(&reader, &left, ty, value);
        }
        let ((lowered, map_work), proof_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                crate::persistent::measure_persistent_work(|| {
                    relower_written_proposition(&claim, &reader).unwrap()
                })
            });
        let read = local_test_read_operand(&lowered, ty);
        let OldMachineTerm::MemoryLoad(point, address, crate::kernel::LoadKind::Int32) = read
        else {
            panic!("expected a typed read: {read:?}");
        };
        assert_eq!(address.as_ref(), &right);
        assert_eq!(point.read_version_id(), written.program_point_id());
        work.push((proof_work, map_work));

        let root =
            crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, read);
        let raised =
            raise_kernel_term(&root, ParameterBinding::default(), &entry, &BTreeMap::new())
                .expect("a recorded fixed-offset read has a spelling");
        assert!(matches!(&raised, SyntaxTerm::At { selector: at, .. } if at == &selector));
        let mut replay = claim.clone();
        let SyntaxProposition::Comparison { left, .. } = &mut replay else {
            unreachable!("test comparison")
        };
        *left = raised;
        assert_eq!(
            relower_written_proposition_with_states(&replay, &entry, &entry, &points),
            Ok(lowered)
        );
    }
    let (proof_work, map_work) = work[0];
    assert!(
        work.iter()
            .all(|&(proof, map)| proof <= proof_work + 64 && map <= map_work + 256),
        "read work grew with sibling stores: {work:?}"
    );
}

fn check_local_read_work(value_type: ProgramType, disjoint_type: ProgramType) {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer_type = match value_type {
        ProgramType::Int8 => ProgramType::Int8Pointer,
        ProgramType::UInt8 => ProgramType::UInt8Pointer,
        ProgramType::Int16 => ProgramType::Int16Pointer,
        ProgramType::UInt16 => ProgramType::UInt16Pointer,
        ProgramType::Int32 => ProgramType::Int32Pointer,
        ProgramType::UInt32 => ProgramType::UInt32Pointer,
        ProgramType::Int64 => ProgramType::Int64Pointer,
        ProgramType::UInt64 => ProgramType::UInt64Pointer,
        ProgramType::Int128 => ProgramType::Int128Pointer,
        ProgramType::UInt128 => ProgramType::UInt128Pointer,
        _ => unreachable!("indexed local test type"),
    };
    let slot = local_read_test_address("slot");
    let other = local_read_test_address("other");
    let start = ExecutionState::new()
        .with_memory(
            SymbolicMemory::new()
                .with_block("local:slot", value_type.byte_width())
                .with_block("local:other", disjoint_type.byte_width()),
        )
        .with_local("p", ProgramValue::typed_pointer(slot.clone(), pointer_type));
    let claim = local_read_test_claim(value_type);
    let mut work = Vec::new();
    for (earlier, later) in [(4, 4), (64, 4), (1024, 4), (4, 64), (4, 1024)] {
        // Grow the history of overwritten values and the disjoint suffix
        // independently. Every sample names a new version on its own path.
        let mut before = start.clone();
        for i in 0..earlier {
            before = local_read_test_store(&before, &slot, value_type, i);
        }
        let write = local_read_test_store(&before, &slot, value_type, 0x80);
        let mut reader = write.clone();
        for i in 0..later {
            reader = local_read_test_store(&reader, &other, disjoint_type, i);
        }
        let ((lowered, map_work), proof_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                crate::persistent::measure_persistent_work(|| {
                    relower_written_proposition(&claim, &reader).unwrap()
                })
            });
        assert!(
            matches!(local_test_read_operand(&lowered, value_type), OldMachineTerm::MemoryLoad(point, _, _)
            if point.id() == write.program_point_id())
        );
        work.push((proof_work, map_work));
    }
    let (first_proof_work, first_map_work) = work[0];
    // The terms and persistent-map keys for each version have fresh identities.
    // Allow a fixed amount of lookup variation as the history grows by 256x.
    assert!(
        work.iter()
            .all(|&(proof, map)| { proof <= first_proof_work + 64 && map <= first_map_work + 256 }),
        "lowering {value_type:?} grew with the execution history: {work:?}"
    );
}

#[test]
fn shared_scalar_load_raises_and_relowers_to_the_same_read_node() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Address::new(
        AddressBase::Concrete("shared-read-round-trip".into()),
        AddressOffset::constant(0),
    );
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block("shared-read-round-trip", 4))
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::Int32Pointer),
        );
    let raw = OldMachineTerm::read_named(
        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(state.memory()))),
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
    let claim = SyntaxProposition::Comparison {
        left: surface,
        operator: ComparisonOperator::LessEqual,
        right: SyntaxTerm::IntegerLiteral("20".into()),
    };
    let lowered = relower_written_proposition(&claim, &state).unwrap();
    let Some((OldConditionTerm::Compare { left, .. }, true)) = lowered.old_condition() else {
        panic!("read comparison")
    };
    // Both native lowering and checker observations enter the same structural
    // boundary; the test needs no special registered-name conversion.
    assert_eq!(
        crate::kernel::KernelTermImport::default().machine(MachineIntegerType::Int32, left),
        root
    );
    assert_eq!(
        crate::kernel::KernelTermImport::default()
            .machine_arithmetic(MachineIntegerType::Int32, left),
        Some(root)
    );
}

#[test]
fn volatile_read_event_results_raise_and_lower_exactly() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new();
    let values = [
        ProgramValue::Int32(OldMachineTerm::Variable(Variable(762001))),
        ProgramValue::typed_pointer(
            Address::symbolic(Variable(762002)),
            ProgramType::Int32Pointer,
        ),
    ];
    let mut points = RecordedStates::new();
    points.record_read_event_values(3, values.iter());
    let _points = SynthesisRecordedPointsScope::enter(&points);
    for (event, value) in values.iter().enumerate() {
        let expression = synthesize_surface_value(value, ParameterBinding::default(), &state)
            .expect("event result spelling");
        let expected = SyntaxTerm::RegionResult(CodeRegionRef::Path(vec![
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
            &SyntaxProposition::Comparison {
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
            ProgramValue::Int32(term) => Proposition::condition_is(
                OldConditionTerm::Compare {
                    format: crate::kernel::MachineIntegerType::Int32,
                    relation: crate::kernel::CompareRelation::Equal,
                    left: Box::new(term.clone()),
                    right: Box::new(term.clone()),
                },
                true,
            ),
            ProgramValue::Pointer(pointer) => Proposition::condition_is(
                OldConditionTerm::AddressEqual(
                    Box::new(pointer.address().clone()),
                    Box::new(pointer.address().clone()),
                ),
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
    let old = ProgramValue::Int32(OldMachineTerm::Variable(Variable(762010)));
    let next = ProgramValue::Int32(OldMachineTerm::Variable(Variable(762011)));
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
    let interface = left.for_branch_interface(
        &joined,
        &ProgramPointRef {
            region: CodeRegionRef::Region(4),
            kind: ProgramPointKind::Entry,
        },
        &ExecutionState::new(),
    );
    assert!(
        interface
            .region_result_value(&CodeRegionRef::Region(3))
            .is_err()
    );
    assert_eq!(
        left.region_result_value(&CodeRegionRef::Region(3)).unwrap(),
        next
    );
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
    let native = OldMachineTerm::logical_machine_binary(
        MachineIntegerType::Int32,
        MachineBinaryOp::Add,
        OldMachineTerm::Variable(variable),
        OldMachineTerm::constant(1),
    );
    let root = KernelTermImport::default().machine(MachineIntegerType::Int32, &native);
    let state = ExecutionState::new()
        .with_local("x", ProgramValue::Int32(OldMachineTerm::Variable(variable)));
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
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable("current".into())),
        "a current local must be named before spelling its historical operands",
    );
    assert_eq!(KernelTermExport::machine_export_count(), named_exports);
    // Both roots and immediate child tags collide in the local-name index.
    // Exact matching must reject the earlier name before using the true holder.
    let outer = |value| {
        OldMachineTerm::logical_machine_binary(
            MachineIntegerType::Int32,
            MachineBinaryOp::Add,
            value,
            OldMachineTerm::constant(1),
        )
    };
    let nested = outer(native.clone());
    let nested_root = KernelTermImport::default().machine(MachineIntegerType::Int32, &nested);
    let collision_state = named_state
        .with_local(
            "a_collision",
            ProgramValue::Int32(outer(outer(OldMachineTerm::Variable(Variable(993499))))),
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
        SyntaxTerm::ProgramExpression(ProgramExpression::Variable("current_nested".into())),
    );
    assert_eq!(KernelTermExport::machine_export_count(), named_exports);
    let exports = KernelTermExport::machine_export_count();
    let surface =
        raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new()).unwrap();
    assert_eq!(KernelTermExport::machine_export_count(), exports);
    let written = SyntaxProposition::Comparison {
        left: surface,
        operator: ComparisonOperator::LessEqual,
        right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(int32(20))),
    };
    let lowered = relower_written_proposition(&written, &state).unwrap();
    let Proposition::ConditionIs(condition, true) = lowered else {
        panic!("comparison")
    };
    let view = crate::kernel::machine_integer::comparison::structural_comparison_view(
        condition.old_form(),
    )
    .unwrap();
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn common_machine_calls_round_trip_source_with_nested_arguments_and_casts() {
    check_common_machine_call_formats(&[
        (MachineIntegerType::Int32, "int32"),
        (MachineIntegerType::UInt32, "uint32"),
        (MachineIntegerType::Int64, "int64"),
        (MachineIntegerType::UInt64, "uint64"),
    ]);
}

#[test]
#[cfg(not(feature = "fast-gate"))]
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
        let variable = ProgramValue::Int32(OldMachineTerm::Variable(Variable(995900)));
        let state = ExecutionState::new().with_local("x", variable.clone());
        let values = ProgramValueBindings::from([("x".to_string(), variable)]);
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
        let lower = |expression: &SyntaxTerm| {
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
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(710003))),
        )
        .with_local(
            "__click_binder_0",
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(710004))),
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
                spelled,
                &lowered,
                ParameterBinding::default(),
                &state
            ),
            "{expression}: {spelled:?}; restored: {:?}; original: {lowered:?}",
            relower_written_proposition(spelled, &state)
        );
    }
}

#[test]
fn range_fold_surface_separates_integer_and_machine_binder_ids() {
    use crate::kernel::{IntegerRangeFoldIndex, IntegerTerm, SharedIntegerRangeEndpoint};
    let _session = crate::kernel::VerificationSession::enter();
    let id = Variable(710005);
    let n = OldMachineTerm::Variable(Variable(710006));
    let state = ExecutionState::new().with_local("n", ProgramValue::Int32(n.clone()));
    let fold = IntegerTerm::RangeFold {
        index: IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(OldMachineTerm::constant(0)),
            end: SharedIntegerRangeEndpoint::intern(n),
        },
        initial: IntegerTerm::constant_i64(0).into(),
        accumulator: id,
        item: id,
        body: IntegerTerm::Add(
            IntegerTerm::Variable(id).into(),
            IntegerTerm::from_machine(MachineIntegerType::Int32, OldMachineTerm::Variable(id))
                .unwrap()
                .into(),
        )
        .into(),
    };
    let proposition = Proposition::condition_is(
        OldConditionTerm::integer_equal(fold, IntegerTerm::constant_i64(0)),
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
fn common_match_surface_preserves_typed_binders_and_relowers_nested_results() {
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
    let values = ProgramValueBindings::from([
        (
            "payload".to_string(),
            ProgramValue::Parameter(Box::new(scrutinee.clone())),
        ),
        (
            "n".to_string(),
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(991951))),
        ),
    ]);
    let state = ExecutionState::new()
        .with_local("payload", ProgramValue::Parameter(Box::new(scrutinee)))
        .with_local(
            "n",
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(991951))),
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
        let lower = |proposition: &SyntaxProposition| {
            crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
            proposition, &PureFactContext::new(), ContractEnvironment::new(&values, &BTreeMap::new()),
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::with_algebraic_types(file.click_function_definitions(), file.algebraic_type_definitions())),
            FixedStateLoweringOptions { algebraic_values: Some(&algebraic_values), ..Default::default() },
        ).unwrap_or_else(|error| panic!("{requirement}: {proposition:?}: {error}")).0
        };
        let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
            panic!()
        };
        let original = lower(written);
        let spelled =
            synthesize_surface_proposition(&original, ParameterBinding::default(), &state)
                .unwrap_or_else(|| panic!("match spelling: {original:?}"));
        let text = crate::surface::printing::source_click_proposition(&spelled);
        assert!(!text.contains("binder("), "{requirement}: {text}");
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
    use crate::kernel::{AddressBase, KernelTerm, KernelTermImport, Pointer, PureFunctionArgument};
    let _session = crate::kernel::VerificationSession::enter();
    let declarations = "function select(p: int32*) -> int32* { p }";
    let file = parser::parse(declarations).unwrap();
    let input = ProgramValue::Pointer(Pointer::new(
        Address::symbolic(Variable(1025900)),
        ProgramType::Int32Pointer,
    ));
    let state = ExecutionState::new().with_local("p", input.clone());
    let values = ProgramValueBindings::from([("p".to_string(), input)]);
    let lower = |expression: &SyntaxTerm| {
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
        fn common(pointer: &Pointer) -> KernelTerm {
            let value = pointer.shared().clone();
            let AddressBase::PureFunctionApplication(application) = &pointer.base else {
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
                        point: memory,
                        pointer: ProgramValue::Pointer(pointer),
                        element_type,
                    } => Some(KernelTerm::shared_array_reference(
                        memory.clone(),
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
            .map(|(name, value)| (value.clone(), SurfaceBinder::from(name)))
            .collect();
        let raised = with_proof_local_value_names(names, || {
            raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new())
        })
        .unwrap_or_else(|| panic!("could not raise {text}"));
        assert_eq!(lower(&raised), expected, "{raised:?}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: literal raising round trips through a verified C function"]
fn string_literal_pointer_raising_names_the_exact_source_occurrence() {
    let identity = crate::kernel::StringLiteralId::new("text", 1).with_source("literal_raising.c");
    let pointer = SymbolicMemory::string_literal_pointer(&identity, b"same\0");
    let value = ProgramValue::typed_pointer(pointer, ProgramType::UInt8Pointer);
    let raised =
        synthesize_surface_value(&value, ParameterBinding::default(), &ExecutionState::new())
            .expect("a literal needs no local or recorded alias to have a name");
    let name = diagnostics::describe_contract_expression(&raised);
    assert!(name.contains("text.string_literal(1)"), "{name}");
    let c = "const uint8* text() { const uint8* discarded = \"same\"; return \"same\"; }";
    let click = format!(
        "target \"x86_64-unknown-linux-gnu\"; mode \"kernel\"; verifying \"literal_raising.c\"; const uint8* text() {{ ensures result == {name}; }}"
    );
    crate::surface::verify_c_sources(&click, &[("literal_raising.c", c)])
        .expect("raised literal reference");
    assert!(
        crate::surface::verify_c_sources(
            &click.replace("string_literal(1)", "string_literal(0)"),
            &[("literal_raising.c", c)]
        )
        .is_err()
    );
}

#[test]
fn typed_word_reads_round_trip_their_observation_without_a_sign_cast() {
    use crate::kernel::{IntegerTerm, Pointer};
    for (format, name) in [
        (MachineIntegerType::Int64, "load<int64>"),
        (MachineIntegerType::UInt64, "load<uint64>"),
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::symbolic(Variable(981_200));
        let memory = SymbolicMemory::new().with_block("word-read-source", 8);
        let state = ExecutionState::new()
            .with_memory(memory.clone())
            .with_local(
                "p",
                ProgramValue::Pointer(Pointer::new(pointer.clone(), ProgramType::UInt64Pointer)),
            );
        let read = crate::kernel::canonical_form_of_load(
            crate::kernel::intern_memory(memory),
            pointer,
            crate::kernel::LoadKind::Bits64,
        );
        let value = IntegerTerm::from_machine(format, read).unwrap();
        let goal = Proposition::condition_is(
            OldConditionTerm::IntegerLessThan(value.into(), IntegerTerm::constant_i64(1).into()),
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
        values.push(ProgramValue::Float32(OldMachineTerm::constant(bits)));
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
        values.push(ProgramValue::Float64(OldMachineTerm::uint64_constant(bits)));
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
            if let ProgramValue::Float32(_) = &value {
                let bits = text.strip_suffix(')').unwrap();
                let suffixed = parser::parse(&format!(
                    "{prefix} function probe() -> {ty} {{ {bits}u32) }}"
                ))
                .unwrap();
                assert_eq!(
                    suffixed.click_function_definitions()[0].body(),
                    Some(expression),
                    "{text}, rust={rust}"
                );
            }
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                expression,
                BTreeMap::new(),
                &state,
                ProgramValueBindings::new(),
                ProgramValueBindings::new(),
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
        ProgramValue::Float32(OldMachineTerm::Variable(Variable(999804))),
        ProgramValue::Float64(OldMachineTerm::Variable(Variable(999805))),
        ProgramValue::Float32(OldMachineTerm::constant(0x80000000)),
        ProgramValue::Float32(OldMachineTerm::constant(0x7f800123)),
        ProgramValue::Float64(OldMachineTerm::uint64_constant(0x8000000000000000)),
        ProgramValue::Float64(OldMachineTerm::uint64_constant(0x7ff8000000000123)),
    ];
    for value in values {
        let named = matches!(
            &value,
            ProgramValue::Float32(OldMachineTerm::Variable(_))
                | ProgramValue::Float64(OldMachineTerm::Variable(_))
        );
        let values = if named {
            BTreeMap::from([("value".to_string(), value.clone())])
        } else {
            BTreeMap::new()
        };
        let state = ExecutionState::new();
        // Scoped float binders already have their source names. Execution-local
        // name/storage handoffs are the later 8aa boundary.
        let bindings = (match &value {
            ProgramValue::Float32(OldMachineTerm::Variable(variable))
            | ProgramValue::Float64(OldMachineTerm::Variable(variable)) => {
                BTreeMap::from([(*variable, "value".to_string())])
            }
            _ => BTreeMap::new(),
        })
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
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
                values.clone().into(),
                values.clone().into(),
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

#[test]
fn float_pointer_casts_round_trip_native_load_spelling() {
    for (value_type, pointer_type, spelling, kind) in [
        (
            ProgramType::Float32,
            ProgramType::Float32Pointer,
            "float",
            crate::kernel::LoadKind::Float32,
        ),
        (
            ProgramType::Float64,
            ProgramType::Float64Pointer,
            "double",
            crate::kernel::LoadKind::Float64,
        ),
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::new(
            AddressBase::Concrete("float-cast-read".into()),
            AddressOffset::constant(0),
        );
        let state = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block("float-cast-read", 8))
            .with_local(
                "p",
                ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt8Pointer),
            );
        let cast = ProgramExpression::Cast {
            expression: Box::new(ProgramExpression::Cast {
                expression: Box::new(ProgramExpression::Variable("p".into())),
                target_type: ProgramType::VoidPointer,
                integer_mode: crate::kernel::IntegerCastMode::Standard,
                pointee_struct: None,
                pointee_struct_size: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            }),
            target_type: pointer_type,
            integer_mode: crate::kernel::IntegerCastMode::Standard,
            pointee_struct: None,
            pointee_struct_size: None,
            pointee_volatile: false,
            pointee_constant: false,
            explicit_qualification: false,
        };
        for expression in [
            ProgramExpression::Load(Box::new(cast.clone())),
            ProgramExpression::Index(Box::new(cast), Box::new(ProgramExpression::Value(int32(0)))),
        ] {
            let text = diagnostics::describe_program_expression(&expression);
            let parsed = parser::parse(&format!(
                "function probe(p: uint8*) -> {spelling} {{ {text} }}"
            ))
            .unwrap_or_else(|error| panic!("{text}: {error}"));
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                parsed.click_function_definitions()[0].body().unwrap(),
                BTreeMap::new(),
                &state,
                ProgramValueBindings::new(),
                ProgramValueBindings::new(),
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
            let (value, _) =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &spec,
                    Some(&state),
                    &PureFactContext::new(),
                )
                .unwrap();
            assert_eq!(value.program_type(), value_type, "{text}");
            let (ProgramValue::Float32(read) | ProgramValue::Float64(read)) = value else {
                panic!("{text}: expected a float value");
            };
            let OldMachineTerm::MemoryLoad(point, address, actual_kind) = read else {
                panic!("{text}: expected a float load");
            };
            assert_eq!(actual_kind, kind, "{text}");
            assert_eq!(*address, pointer, "{text}");
            assert_eq!(
                point.read_version_id(),
                state.observation_point_id(),
                "{text}"
            );
        }
    }
    for text in ["p as (float)", "p as (double)"] {
        assert!(
            parser::parse(&format!("function probe(p: uint8*) -> float {{ {text} }}")).is_err()
        );
    }
}

#[test]
fn a_boolean_cell_read_round_trips_as_a_typed_load() {
    use crate::kernel::effective_type::{CAccessClass, CScalarClass};
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Address::new(
        AddressBase::Concrete("boolean-source-read".into()),
        AddressOffset::constant(0),
    );
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_classed_block(
            pointer.base.clone(),
            Some(CAccessClass::Scalar(CScalarClass::Bool)),
            1,
        ))
        .with_local(
            "p",
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt8Pointer),
        );
    let detached = OldConditionTerm::boolean_cell_read(
        crate::kernel::ProgramPoint::of_memory(state.memory()),
        pointer.clone(),
    );
    assert!(
        synthesize_boolean_cell_read(
            crate::kernel::BooleanOperandView::Native(detached.bool_negation_operand().unwrap()),
            ParameterBinding::default(),
            &state,
            &BTreeMap::new(),
        )
        .is_none()
    );

    let read = crate::kernel::SpecExpression::MemoryLoad {
        point: crate::kernel::SpecPoint::Current,
        pointer: Box::new(crate::kernel::SpecExpression::Value(
            ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt8Pointer),
        )),
        value_type: ProgramType::Bool,
        exact: false,
    };
    let (value, _) =
        crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
            &state,
            &read,
            Some(&state),
            &PureFactContext::new(),
        )
        .unwrap();
    let ProgramValue::Bool(word) = value else {
        panic!("the typed source read is a Boolean");
    };
    let condition = OldConditionTerm::truth_of_bool_word(&word);
    let root = crate::kernel::KernelTermImport::default().condition(&condition);
    let surface = raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new())
        .expect("name of the Boolean cell read");
    let text = diagnostics::describe_contract_expression(&surface);
    assert_eq!(text, "exact(load<Bool>(p))");
    let parsed = parser::parse(&format!("function probe(p: uint8*) -> Bool {{ {text} }}"))
        .expect("typed Boolean load parses");
    let expression = parsed.click_function_definitions()[0].body().unwrap();
    let spec = crate::surface::lowering::elaborate_fixed_state_expression(
        expression,
        BTreeMap::new(),
        &state,
        ProgramValueBindings::new(),
        ProgramValueBindings::new(),
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
    let (value, _) =
        crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
            &state,
            &spec,
            Some(&state),
            &PureFactContext::new(),
        )
        .unwrap();
    assert_eq!(value, ProgramValue::of_bool(condition.clone()));
    for truth in [false, true] {
        let goal = condition.truth_claim(truth);
        let spelled =
            synthesize_surface_proposition(&goal, ParameterBinding::default(), &state).unwrap();
        let text = crate::surface::printing::source_click_proposition(&spelled);
        assert!(text.contains("load<Bool>(p)"), "{text}");
        let lowered = relower_written_proposition(&spelled, &state).unwrap();
        assert_eq!(lowered, goal, "{text}");
    }

    let later = state
        .clone()
        .with_memory(state.memory().clone().with_block("later-boolean-read", 1));
    let _entry =
        SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(state.clone()))));
    let old = raise_kernel_term(&root, ParameterBinding::default(), &later, &BTreeMap::new())
        .expect("name of the Boolean read at entry");
    assert_eq!(
        diagnostics::describe_contract_expression(&old),
        "old(exact(load<Bool>(p)))"
    );
    assert_eq!(
        relower_written_proposition_with_states(
            &bool_truth(old),
            &state,
            &later,
            &RecordedStates::new(),
        )
        .unwrap(),
        condition.truth_claim(true),
    );

    let byte_memory = crate::kernel::intern_memory(SymbolicMemory::new().with_classed_block(
        pointer.base.clone(),
        Some(CAccessClass::Scalar(CScalarClass::Char)),
        1,
    ));
    let byte_test =
        OldConditionTerm::boolean_cell_read(crate::kernel::ProgramPoint::at(&byte_memory), pointer);
    assert!(
        synthesize_boolean_cell_read(
            crate::kernel::BooleanOperandView::Native(byte_test.bool_negation_operand().unwrap()),
            ParameterBinding::default(),
            &state,
            &BTreeMap::new(),
        )
        .is_none()
    );
}

fn evaluate_float_cell_read(
    state: &ExecutionState,
    pointer: &Address,
    format: crate::kernel::KernelFloatType,
    exact: bool,
) -> OldMachineTerm {
    use crate::kernel::{SpecExpression, SpecPoint};
    let ty = format.program_type();
    let expression = SpecExpression::MemoryLoad {
        point: SpecPoint::Current,
        pointer: Box::new(SpecExpression::Value(ProgramValue::typed_pointer(
            pointer.clone(),
            ty.pointer_to().unwrap(),
        ))),
        value_type: ty,
        exact,
    };
    let (value, _) =
        crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
            state,
            &expression,
            None,
            &PureFactContext::new(),
        )
        .unwrap();
    assert_eq!(value.program_type(), ty);
    let (ProgramValue::Float32(read) | ProgramValue::Float64(read)) = value else {
        panic!("expected a float value");
    };
    let OldMachineTerm::MemoryLoad(point, address, kind) = &read else {
        panic!("expected a float load");
    };
    assert_eq!(point.read_version_id(), state.observation_point_id());
    assert_eq!(address.as_ref(), pointer);
    assert_eq!(*kind, format.load_kind());
    read
}

#[test]
fn common_float_reads_round_trip_existing_cast_dereference_syntax() {
    for (format, spelling) in [
        (crate::kernel::KernelFloatType::Float32, "float"),
        (crate::kernel::KernelFloatType::Float64, "double"),
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::new(
            AddressBase::Concrete("float-source-read".into()),
            AddressOffset::constant(0),
        );
        let state = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block("float-source-read", 8))
            .with_local(
                "p",
                ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt8Pointer),
            );
        let read = evaluate_float_cell_read(&state, &pointer, format, false);
        let root = crate::kernel::KernelTermImport::default().float(format, &read);
        assert!(matches!(
            root.node(),
            crate::kernel::KernelTermNode::FloatRead(_)
        ));
        let surface =
            raise_kernel_term(&root, ParameterBinding::default(), &state, &BTreeMap::new())
                .unwrap();
        assert!(!root.has_cached_native_argument());
        let text = diagnostics::describe_contract_expression(&surface);
        let parsed = parser::parse(&format!(
            "function probe(p: uint8*) -> {spelling} {{ {text} }}"
        ))
        .unwrap();
        let expression = parsed.click_function_definitions()[0].body().unwrap();
        let spec = crate::surface::lowering::elaborate_fixed_state_expression(
            expression,
            BTreeMap::new(),
            &state,
            ProgramValueBindings::new(),
            ProgramValueBindings::new(),
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
        let (value, _) =
            crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                &state,
                &spec,
                Some(&state),
                &PureFactContext::new(),
            )
            .unwrap();
        assert_eq!(value, format.value(read), "{text}");
    }
}

#[test]
fn common_float_reads_retain_old_and_recorded_states() {
    check_float_reads_at_old_and_recorded_states(false);
}

#[test]
fn exact_float_reads_name_distinct_points_with_equal_memory() {
    check_float_reads_at_old_and_recorded_states(true);
}

fn check_float_reads_at_old_and_recorded_states(exact: bool) {
    for format in [
        crate::kernel::KernelFloatType::Float32,
        crate::kernel::KernelFloatType::Float64,
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Address::new(
            AddressBase::Concrete("float-retained_state".into()),
            AddressOffset::constant(0),
        );
        let selected = ExecutionState::new()
            .with_memory(SymbolicMemory::new().with_block("float-retained_state", 8))
            .with_local(
                "p",
                ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt8Pointer),
            );
        let (now, read) = if exact {
            let now = selected.clone().begin_function_entry_memory();
            assert_eq!(selected.memory(), now.memory());
            assert_ne!(selected.program_point_id(), now.program_point_id());
            let read = evaluate_float_cell_read(&selected, &pointer, format, true);
            assert_ne!(read, evaluate_float_cell_read(&now, &pointer, format, true));
            (now, read)
        } else {
            let now = selected
                .clone()
                .with_memory(selected.memory().clone().with_block("later-block", 8));
            let read = OldMachineTerm::read_named(
                crate::kernel::ProgramPoint::of_memory(selected.memory()),
                Box::new(pointer),
                format.load_kind(),
            );
            (now, read)
        };
        let root = crate::kernel::KernelTermImport::default().float(format, &read);
        let current = raise_kernel_term(
            &root,
            ParameterBinding::default(),
            &selected,
            &BTreeMap::new(),
        )
        .unwrap();
        let comparison = |left| SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right: SyntaxTerm::ProgramExpression(ProgramExpression::Value(format.value(
                match format {
                    crate::kernel::KernelFloatType::Float32 => OldMachineTerm::constant(0),
                    crate::kernel::KernelFloatType::Float64 => OldMachineTerm::uint64_constant(0),
                },
            ))),
        };
        let expected = relower_written_proposition(&comparison(current), &selected).unwrap();
        for old in [true, false] {
            let selector = ProgramPointSelector::from(ProgramPointRef {
                region: CodeRegionRef::Region(0),
                kind: ProgramPointKind::Entry,
            });
            let mut points = RecordedStates::new();
            points.insert(selector.clone(), selected.clone());
            let _points = SynthesisRecordedPointsScope::enter(&points);
            let entry = if old { &selected } else { &now };
            let _entry = SynthesisEntryScope(
                SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(entry.clone()))),
            );
            let surface =
                raise_kernel_term(&root, ParameterBinding::default(), &now, &BTreeMap::new())
                    .unwrap();
            if old {
                assert!(matches!(&surface, SyntaxTerm::Old(_)));
            } else {
                assert!(
                    matches!(&surface, SyntaxTerm::At { selector: actual, .. } if actual == &selector)
                );
            }
            let text = diagnostics::describe_contract_expression(&surface);
            assert_eq!(text.contains("exact("), exact, "{text}");
            let zero = if format == crate::kernel::KernelFloatType::Float32 {
                "float32_from_bits(0)"
            } else {
                "float64_from_bits(0)"
            };
            let parsed = parser::parse(&format!(
                "theorem probe() {{ requires {text} == {zero}; ensures true; }}"
            ))
            .unwrap();
            let Requirement::Proposition(claim) = &parsed.theorem_definitions()[0].requires()[0]
            else {
                panic!("comparison")
            };
            assert_eq!(
                relower_written_proposition_with_states(claim, entry, &now, &points).unwrap(),
                expected,
                "{text}"
            );
        }
    }
}
#[test]
fn click_float_unary_negation_preserves_positive_zero_sign() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut actual = Vec::new();
    for (ty, bits) in [
        ("float", "float32_from_bits"),
        ("double", "float64_from_bits"),
    ] {
        let parsed =
            parser::parse(&format!("function negate_zero() -> {ty} {{ -{bits}(0) }}")).unwrap();
        let state = ExecutionState::new();
        let spec = crate::surface::lowering::elaborate_fixed_state_expression(
            parsed.click_function_definitions()[0].body().unwrap(),
            BTreeMap::new(),
            &state,
            ProgramValueBindings::new(),
            ProgramValueBindings::new(),
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
        let (value, _) =
            crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                &state,
                &spec,
                Some(&state),
                &PureFactContext::new(),
            )
            .unwrap();
        actual.push(value);
    }
    assert_eq!(
        actual,
        vec![
            ProgramValue::Float32(OldMachineTerm::constant(0x80000000)),
            ProgramValue::Float64(OldMachineTerm::uint64_constant(0x8000000000000000))
        ]
    );
}

#[test]
fn click_float_unary_negation_preserves_bits_and_symbolic_operands() {
    let _session = crate::kernel::VerificationSession::enter();
    for wide in [false, true] {
        let ty = if wide { "double" } else { "float" };
        let parsed = parser::parse(&format!("function negate(x: {ty}) -> {ty} {{ -x }}")).unwrap();
        let body = parsed.click_function_definitions()[0].body().unwrap();
        let program =
            crate::surface::lowering::resource_argument_to_program_expression(body).unwrap();
        let patterns: &[u64] = if wide {
            &[
                0,
                0x8000000000000000,
                0x3ff0000000000000,
                0x7ff0000000000000,
                0x7ff8000000000123,
                0xfff0000000000123,
                1,
            ]
        } else {
            &[
                0, 0x80000000, 0x3f800000, 0x7f800000, 0x7fc00123, 0xff800123, 1,
            ]
        };
        for term in patterns
            .iter()
            .map(|&bits| {
                if wide {
                    OldMachineTerm::uint64_constant(bits)
                } else {
                    OldMachineTerm::constant(bits as u32)
                }
            })
            .chain(std::iter::once(OldMachineTerm::Variable(Variable(981001))))
        {
            let (value, expected) = if wide {
                (
                    ProgramValue::Float64(term.clone()),
                    ProgramValue::Float64(OldMachineTerm::float64_negate(term)),
                )
            } else {
                (
                    ProgramValue::Float32(term.clone()),
                    ProgramValue::Float32(OldMachineTerm::float32_negate(term)),
                )
            };
            let state = ExecutionState::new().with_local("x", value);
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                body,
                BTreeMap::new(),
                &state,
                ProgramValueBindings::new(),
                ProgramValueBindings::new(),
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
            for expression in [spec, SpecExpression::ProgramExpression(program.clone())] {
                let (actual, obligations) =
                    crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                        &state, &expression, Some(&state), &PureFactContext::new(),
                    ).unwrap();
                assert_eq!(actual, expected);
                assert!(obligations.is_empty());
            }
        }
    }
}

#[test]
fn click_integer_unary_negation_keeps_subtraction_semantics() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new();
    for value in [
        ProgramValue::Int32(OldMachineTerm::constant(0)),
        ProgramValue::Int32(OldMachineTerm::constant(0x80000000)),
        ProgramValue::Int32(OldMachineTerm::Variable(Variable(981002))),
        ProgramValue::UInt32(OldMachineTerm::constant(1)),
        ProgramValue::UInt32(OldMachineTerm::Variable(Variable(981003))),
        ProgramValue::UInt64(OldMachineTerm::Variable(Variable(981004))),
        ProgramValue::Int64(OldMachineTerm::int64_constant(i64::MIN)),
        ProgramValue::UInt64(OldMachineTerm::uint64_constant(1)),
    ] {
        let zero = SpecExpression::Value(ProgramValue::Int32(OldMachineTerm::constant(0)));
        let operand = SpecExpression::Value(value.clone());
        let expressions = [
            SpecExpression::Negate(Box::new(operand.clone())),
            SpecExpression::ProgramExpression(ProgramExpression::Negate(Box::new(
                ProgramExpression::Value(value.clone()),
            ))),
        ];
        let previous = [
            SpecExpression::Subtract(Box::new(zero), Box::new(operand)),
            SpecExpression::ProgramExpression(ProgramExpression::Subtract(
                Box::new(ProgramExpression::Value(ProgramValue::Int32(
                    OldMachineTerm::constant(0),
                ))),
                Box::new(ProgramExpression::Value(value)),
            )),
        ];
        let evaluate = |expression: &SpecExpression| {
            crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                &state,
                expression,
                Some(&state),
                &PureFactContext::new(),
            )
        };
        for (expression, previous) in expressions.into_iter().zip(previous) {
            assert_eq!(evaluate(&expression), evaluate(&previous));
        }
    }
}

#[test]
fn common_float_arithmetic_round_trips_existing_operators() {
    use crate::kernel::{FloatBinaryOperator, KernelFloatType};
    let _session = crate::kernel::VerificationSession::enter();
    for (format, spelling) in [
        (KernelFloatType::Float32, "float"),
        (KernelFloatType::Float64, "double"),
    ] {
        let variable = OldMachineTerm::Variable(Variable(999936));
        let state = ExecutionState::new().with_local("x", format.value(variable.clone()));
        let names = (BTreeMap::<_, String>::from([(Variable(999936), "x".to_string())]))
            .into_iter()
            .map(|(var, name)| (var, SurfaceBinder::from(name)))
            .collect::<BTreeMap<_, _>>();
        let literal = match format {
            KernelFloatType::Float32 => OldMachineTerm::constant(0x80000000),
            KernelFloatType::Float64 => OldMachineTerm::uint64_constant(0x8000000000000000),
        };
        let mut sources = vec![match format {
            KernelFloatType::Float32 => OldMachineTerm::float32_negate(variable.clone()),
            KernelFloatType::Float64 => OldMachineTerm::float64_negate(variable.clone()),
        }];
        for operator in [
            FloatBinaryOperator::Add,
            FloatBinaryOperator::Subtract,
            FloatBinaryOperator::Multiply,
            FloatBinaryOperator::Divide,
        ] {
            sources.push(match format {
                KernelFloatType::Float32 => {
                    OldMachineTerm::float32_binary(variable.clone(), literal.clone(), operator)
                }
                KernelFloatType::Float64 => {
                    OldMachineTerm::float64_binary(variable.clone(), literal.clone(), operator)
                }
            });
        }
        for source in sources {
            let root = crate::kernel::KernelTermImport::default().float(format, &source);
            let surface =
                raise_kernel_term(&root, ParameterBinding::default(), &state, &names).unwrap();
            let text = diagnostics::describe_contract_expression(&surface);
            let parsed = parser::parse(&format!(
                "function probe(x: {spelling}) -> {spelling} {{ {text} }}"
            ))
            .unwrap_or_else(|error| panic!("{text}: {error}"));
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                parsed.click_function_definitions()[0].body().unwrap(),
                BTreeMap::new(),
                &state,
                ProgramValueBindings::new(),
                ProgramValueBindings::new(),
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
            let (value, _) =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &spec,
                    Some(&state),
                    &PureFactContext::new(),
                )
                .unwrap();
            assert_eq!(value, format.value(source), "{text}");
        }
    }
}

#[test]
fn numeric_float_cast_spellings_match_native_conversions_and_round_trip() {
    let _session = crate::kernel::VerificationSession::enter();
    let sources = [
        (
            "uint8*",
            ProgramValue::typed_pointer(Address::null(), ProgramType::UInt8Pointer),
        ),
        (
            "int128",
            ProgramValue::Int128(OldMachineTerm::Variable(Variable(999943))),
        ),
        (
            "int32",
            ProgramValue::Int32(OldMachineTerm::constant(16_777_217)),
        ),
        (
            "int32",
            ProgramValue::Int32(OldMachineTerm::Variable(Variable(999940))),
        ),
        (
            "uint32",
            ProgramValue::UInt32(OldMachineTerm::uint32_constant(u32::MAX)),
        ),
        (
            "int64",
            ProgramValue::Int64(OldMachineTerm::int64_constant(i64::MIN)),
        ),
        (
            "uint64",
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(u64::MAX)),
        ),
        (
            "float",
            ProgramValue::Float32(OldMachineTerm::constant(0x80000000)),
        ),
        (
            "float",
            ProgramValue::Float32(OldMachineTerm::constant(0x7f800123)),
        ),
        (
            "float",
            ProgramValue::Float32(OldMachineTerm::Variable(Variable(999941))),
        ),
        (
            "double",
            ProgramValue::Float64(OldMachineTerm::uint64_constant(0x8000000000000000)),
        ),
        (
            "double",
            ProgramValue::Float64(OldMachineTerm::uint64_constant(0xfff8000000000123)),
        ),
        (
            "double",
            ProgramValue::Float64(OldMachineTerm::uint64_constant(0x3ff0000010000000)),
        ),
        (
            "double",
            ProgramValue::Float64(OldMachineTerm::Variable(Variable(999942))),
        ),
    ];
    for (source_name, value) in sources {
        let state = ExecutionState::new().with_local("x", value.clone());
        for (target_name, target_type) in [
            ("float", ProgramType::Float32),
            ("double", ProgramType::Float64),
        ] {
            let native = ProgramExpression::Cast {
                expression: Box::new(ProgramExpression::Value(value.clone())),
                target_type,
                integer_mode: crate::kernel::IntegerCastMode::CConversion,
                pointee_struct: None,
                pointee_struct_size: None,
                pointee_volatile: false,
                pointee_constant: false,
                explicit_qualification: false,
            };
            let expected =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &SpecExpression::ProgramExpression(native),
                    Some(&state),
                    &PureFactContext::new(),
                );
            let mut text = format!("x as {target_name}");
            for _ in 0..2 {
                let parsed = parser::parse(&format!(
                    "function probe(x: {source_name}) -> {target_name} {{ {text} }}"
                ))
                .unwrap();
                let expression = parsed.click_function_definitions()[0].body().unwrap();
                let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                    expression,
                    BTreeMap::new(),
                    &state,
                    ProgramValueBindings::new(),
                    ProgramValueBindings::new(),
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
                let actual =
                    crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                        &state,
                        &spec,
                        Some(&state),
                        &PureFactContext::new(),
                    );
                match (&actual, &expected) {
                    (Ok(actual), Ok(expected)) => {
                        assert_eq!(actual, expected, "{source_name}: {text}")
                    }
                    (Err(_), Err(_)) => {}
                    _ => panic!("{source_name}: {text}: {actual:?} vs {expected:?}"),
                }
                text = diagnostics::describe_contract_expression(expression);
                assert!(text.contains(&format!("as {target_name}")), "{text}");
            }
        }
    }
}

#[test]
fn numeric_float_casts_read_historical_and_current_operands() {
    let _session = crate::kernel::VerificationSession::enter();
    let parsed =
        parser::parse("double probe(int32 x) { ensures result == (old(x) + x) as double; }")
            .unwrap();
    let Ensure::Proposition(SyntaxProposition::Comparison {
        right: expression, ..
    }) = parsed.function_blocks()[0].ensures()[0].ensure()
    else {
        panic!("cast postcondition")
    };
    let entry = ProgramValue::Int32(OldMachineTerm::constant(1));
    let current = ProgramValue::Int32(OldMachineTerm::constant(3));
    let state = ExecutionState::new().with_local("x", entry.clone());
    let spec = crate::surface::lowering::elaborate_fixed_state_expression(
        expression,
        BTreeMap::new(),
        &state,
        ProgramValueBindings::from([("x".into(), entry)]),
        ProgramValueBindings::from([("x".into(), current)]),
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
    let (value, obligations) =
        crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
            &state,
            &spec,
            Some(&state),
            &PureFactContext::new(),
        )
        .unwrap();
    assert_eq!(
        value,
        ProgramValue::Float64(OldMachineTerm::uint64_constant(0x4010000000000000))
    );
    assert!(obligations.is_empty());
}

#[test]
fn numeric_float_cast_syntax_keeps_pointer_targets_and_c_style_refusals() {
    for text in [
        "function probe(x: int32) -> float { x as (float) }",
        "function probe(x: int32) -> double { (double)x }",
        "function probe(p: void*) -> void* { p as (float **) }",
    ] {
        let error = parser::parse(text).expect_err("unsupported cast spelling");
        assert_eq!(error.kind, ClickErrorKind::Syntax, "{error:?}");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn common_float_conversions_round_trip_existing_casts() {
    use crate::kernel::KernelFloatType;
    let _session = crate::kernel::VerificationSession::enter();
    let variable = OldMachineTerm::Variable(Variable(999963));
    let names = (BTreeMap::<_, String>::from([(Variable(999963), "x".to_string())]))
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
    for (source_spelling, source_type) in [
        ("int8", ProgramType::Int8),
        ("uint8", ProgramType::UInt8),
        ("int16", ProgramType::Int16),
        ("uint16", ProgramType::UInt16),
        ("int32", ProgramType::Int32),
        ("uint32", ProgramType::UInt32),
        ("int64", ProgramType::Int64),
        ("uint64", ProgramType::UInt64),
        ("float", ProgramType::Float32),
        ("double", ProgramType::Float64),
    ] {
        let source_value = match source_type {
            ProgramType::Float32 => ProgramValue::Float32(variable.clone()),
            ProgramType::Float64 => ProgramValue::Float64(variable.clone()),
            _ => MachineIntegerType::from_program_type(source_type)
                .unwrap()
                .value_from_term(variable.clone()),
        };
        let state = ExecutionState::new().with_local("x", source_value);
        for (format, target_spelling) in [
            (KernelFloatType::Float32, "float"),
            (KernelFloatType::Float64, "double"),
        ] {
            if source_type == format.program_type() {
                continue;
            }
            let source = OldMachineTerm::opaque_conversion(
                format!(
                    "c_{}_to_{}",
                    crate::kernel::program_type_spelling(source_type),
                    crate::kernel::program_type_spelling(format.program_type())
                ),
                variable.clone(),
            );
            let (widen, narrow) = if format == KernelFloatType::Float32 {
                ("c_float32_to_float64", "c_float64_to_float32")
            } else {
                ("c_float64_to_float32", "c_float32_to_float64")
            };
            let nested = OldMachineTerm::opaque_conversion(
                narrow,
                OldMachineTerm::opaque_conversion(widen, source.clone()),
            );
            for source in [source, nested] {
                let expected = format.value(source.clone());
                let root = crate::kernel::KernelTermImport::default().float(format, &source);
                let surface =
                    raise_kernel_term(&root, ParameterBinding::default(), &state, &names).unwrap();
                let text = diagnostics::describe_contract_expression(&surface);
                let parsed = parser::parse(&format!(
                    "function probe(x: {source_spelling}) -> {target_spelling} {{ {text} }}"
                ))
                .unwrap_or_else(|error| panic!("{text}: {error}"));
                let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                    parsed.click_function_definitions()[0].body().unwrap(),
                    BTreeMap::new(),
                    &state,
                    ProgramValueBindings::new(),
                    ProgramValueBindings::new(),
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
                let (value, _) =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &spec,
                    Some(&state),
                    &PureFactContext::new(),
                )
                .unwrap();
                assert_eq!(value, expected, "{text}");
            }
        }
    }
}

#[test]
fn common_float_to_integer_conversions_round_trip_with_definedness() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = OldMachineTerm::Variable(Variable(999963));
    let names = (BTreeMap::<_, String>::from([(Variable(999963), "x".to_string())]))
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
    for (source_spelling, source_type) in [
        ("float", ProgramType::Float32),
        ("double", ProgramType::Float64),
    ] {
        let source_value = match source_type {
            ProgramType::Float32 => ProgramValue::Float32(variable.clone()),
            ProgramType::Float64 => ProgramValue::Float64(variable.clone()),
            _ => MachineIntegerType::from_program_type(source_type)
                .unwrap()
                .value_from_term(variable.clone()),
        };
        let state = ExecutionState::new().with_local("x", source_value);
        for (format, target_spelling) in [
            (MachineIntegerType::Int8, "int8"),
            (MachineIntegerType::UInt8, "uint8"),
            (MachineIntegerType::Int16, "int16"),
            (MachineIntegerType::UInt16, "uint16"),
            (MachineIntegerType::Int32, "int32"),
            (MachineIntegerType::UInt32, "uint32"),
            (MachineIntegerType::Int64, "int64"),
            (MachineIntegerType::UInt64, "uint64"),
        ] {
            if source_type == format.program_type() {
                continue;
            }
            let source = OldMachineTerm::opaque_conversion(
                format!(
                    "c_{}_to_{}",
                    crate::kernel::program_type_spelling(source_type),
                    crate::kernel::program_type_spelling(format.program_type())
                ),
                variable.clone(),
            );
            {
                let expected = format.value_from_term(source.clone());
                let root = crate::kernel::KernelTermImport::default().machine(format, &source);
                let surface =
                    raise_kernel_term(&root, ParameterBinding::default(), &state, &names).unwrap();
                let text = diagnostics::describe_contract_expression(&surface);
                let parsed = parser::parse(&format!(
                    "function probe(x: {source_spelling}) -> {target_spelling} {{ {text} }}"
                ))
                .unwrap_or_else(|error| panic!("{text}: {error}"));
                let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                    parsed.click_function_definitions()[0].body().unwrap(),
                    BTreeMap::new(),
                    &state,
                    ProgramValueBindings::new(),
                    ProgramValueBindings::new(),
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
                let (value, obligations) =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &spec,
                    Some(&state),
                    &PureFactContext::new(),
                )
                .unwrap();
                assert_eq!(value, expected, "{text}");
                assert!(
                    !obligations.is_empty(),
                    "symbolic conversion must retain its definedness obligations: {text}"
                );
            }
        }
    }
}

#[test]
fn common_float_predicates_round_trip_existing_spelling() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = OldMachineTerm::Variable(Variable(999977));
    let names = (BTreeMap::<_, String>::from([(Variable(999977), "x".to_string())]))
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
    for (spelling, value) in [
        ("float", ProgramValue::Float32(variable.clone())),
        ("double", ProgramValue::Float64(variable.clone())),
    ] {
        let state = ExecutionState::new().with_local("x", value);
        let mut conditions = vec![];
        for operator in [
            crate::kernel::ComparisonOperator::Equal,
            crate::kernel::ComparisonOperator::NotEqual,
            crate::kernel::ComparisonOperator::LessThan,
            crate::kernel::ComparisonOperator::LessEqual,
            crate::kernel::ComparisonOperator::GreaterThan,
            crate::kernel::ComparisonOperator::GreaterEqual,
        ] {
            conditions.push(crate::kernel::FloatCondition::Comparison {
                operator,
                left: Box::new(variable.clone()),
                right: Box::new(variable.clone()),
            });
        }
        for classification in [
            crate::kernel::FloatClassification::Finite,
            crate::kernel::FloatClassification::Infinite,
            crate::kernel::FloatClassification::Zero,
            crate::kernel::FloatClassification::Subnormal,
            crate::kernel::FloatClassification::Nan,
        ] {
            conditions.push(crate::kernel::FloatCondition::Classification {
                classification,
                value: Box::new(variable.clone()),
            });
        }
        for condition in conditions {
            let condition = if spelling == "float" {
                OldConditionTerm::Float32(condition)
            } else {
                OldConditionTerm::Float64(condition)
            };
            let root = crate::kernel::KernelTermImport::default().condition(&condition);
            let surface =
                raise_kernel_term(&root, ParameterBinding::default(), &state, &names).unwrap();
            let text = diagnostics::describe_contract_expression(&surface);
            let parsed = parser::parse(&format!(
                "function probe(x: {spelling}) -> Bool {{ {text} }}"
            ))
            .unwrap();
            let spec = crate::surface::lowering::elaborate_fixed_state_expression(
                parsed.click_function_definitions()[0].body().unwrap(),
                BTreeMap::new(),
                &state,
                ProgramValueBindings::new(),
                ProgramValueBindings::new(),
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
            let (value, obligations) =
                crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                    &state,
                    &spec,
                    Some(&state),
                    &PureFactContext::new(),
                )
                .unwrap();
            assert_eq!(value, ProgramValue::of_bool(condition), "{text}");
            assert!(obligations.is_empty(), "{text}");
        }
    }
}

#[test]
fn common_float_calls_round_trip_existing_function_syntax() {
    let _session = crate::kernel::VerificationSession::enter();
    for (format, spelling) in [
        (crate::kernel::KernelFloatType::Float32, "float"),
        (crate::kernel::KernelFloatType::Float64, "double"),
    ] {
        let variable = OldMachineTerm::Variable(Variable(1008204));
        let names = (BTreeMap::<_, String>::from([(Variable(1008204), "x".to_string())]))
            .into_iter()
            .map(|(var, name)| (var, SurfaceBinder::from(name)))
            .collect::<BTreeMap<_, _>>();
        let state = ExecutionState::new().with_local("x", format.value(variable.clone()));
        let source = OldMachineTerm::ClickFunctionApplication {
            name: "step".into(),
            arguments: vec![crate::kernel::PureFunctionArgument::Value(format.value(
                OldMachineTerm::ClickFunctionApplication {
                    name: "step".into(),
                    arguments: vec![crate::kernel::PureFunctionArgument::Value(
                        format.value(variable),
                    )],
                },
            ))],
        };
        let root = crate::kernel::KernelTermImport::default().float(format, &source);
        let surface =
            raise_kernel_term(&root, ParameterBinding::default(), &state, &names).unwrap();
        let text = diagnostics::describe_contract_expression(&surface);
        let parsed = parser::parse(&format!("function step(x: {spelling}) -> {spelling} {{ x }} function probe(x: {spelling}) -> {spelling} {{ {text} }}")).unwrap();
        let spec = crate::surface::lowering::elaborate_fixed_state_expression(
            parsed
                .click_function_definitions()
                .last()
                .unwrap()
                .body()
                .unwrap(),
            BTreeMap::new(),
            &state,
            ProgramValueBindings::new(),
            ProgramValueBindings::new(),
            None,
            &RecordedStates::new(),
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(parsed.click_function_definitions()),
            ),
            BTreeSet::new(),
            BTreeMap::new(),
        )
        .unwrap();
        let (value, obligations) =
            crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
                &state,
                &spec,
                Some(&state),
                &PureFactContext::new(),
            )
            .unwrap();
        assert_eq!(value, format.value(source), "{text}");
        assert!(obligations.is_empty());
    }
}

#[test]
fn mixed_float_boolean_calls_round_trip_existing_surface_syntax() {
    let _session = crate::kernel::VerificationSession::enter();
    let variable = OldMachineTerm::Variable(Variable(1008516));
    let names = (BTreeMap::<_, String>::from([(Variable(1008516), "x".to_string())]))
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
    let state = ExecutionState::new().with_local("x", ProgramValue::Float32(variable.clone()));
    let condition =
        crate::kernel::OldConditionTerm::Float32(crate::kernel::FloatCondition::Comparison {
            operator: crate::kernel::ComparisonOperator::LessThan,
            left: Box::new(variable.clone()),
            right: Box::new(OldMachineTerm::constant(0)),
        });
    let source = OldMachineTerm::ClickFunctionApplication {
        name: "mixed_sink".into(),
        arguments: vec![
            crate::kernel::PureFunctionArgument::Value(ProgramValue::Bool(
                OldMachineTerm::bool_cast(crate::kernel::MachineIntegerType::UInt8, condition),
            )),
            crate::kernel::PureFunctionArgument::Value(ProgramValue::Float32(
                OldMachineTerm::ClickFunctionApplication {
                    name: "mixed_seed".into(),
                    arguments: vec![crate::kernel::PureFunctionArgument::Value(
                        ProgramValue::Float32(variable),
                    )],
                },
            )),
        ],
    };
    let root = crate::kernel::KernelTermImport::default()
        .float(crate::kernel::KernelFloatType::Float64, &source);
    assert!(
        root.children()
            .iter()
            .all(|child| !child.requires_native_argument_input())
    );
    let surface = raise_kernel_term(&root, ParameterBinding::default(), &state, &names).unwrap();
    let text = diagnostics::describe_contract_expression(&surface);
    let parsed = parser::parse(&format!("function mixed_seed(x: float) -> float {{ x }} function mixed_sink(flag: Bool, x: float) -> double {{ x as double }} function probe(x: float) -> double {{ {text} }}")).unwrap();
    let spec = crate::surface::lowering::elaborate_fixed_state_expression(
        parsed
            .click_function_definitions()
            .last()
            .unwrap()
            .body()
            .unwrap(),
        BTreeMap::new(),
        &state,
        ProgramValueBindings::new(),
        ProgramValueBindings::new(),
        None,
        &RecordedStates::new(),
        SpecDefinitions::new(
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(parsed.click_function_definitions()),
        ),
        BTreeSet::new(),
        BTreeMap::new(),
    )
    .unwrap();
    let (value, obligations) =
        crate::kernel::program_evaluate_speresource_expression_with_checked_obligations(
            &state,
            &spec,
            Some(&state),
            &PureFactContext::new(),
        )
        .unwrap();
    assert_eq!(value, ProgramValue::Float64(source), "{text}");
    assert!(obligations.is_empty());
}

#[test]
fn shared_pointer_call_arguments_keep_exact_native_name_policy() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = crate::kernel::Pointer::new(
        Address::symbolic(Variable(1008590)),
        ProgramType::Int32Pointer,
    );
    let value = ProgramValue::Pointer(pointer);
    let argument = crate::kernel::PureFunctionArgument::Value(value.clone());
    let root = crate::kernel::KernelTermImport::default().argument(&argument);
    let state = ExecutionState::new().with_local("p", value.clone());
    let bound = BTreeMap::<Variable, SurfaceBinder>::new();
    for names in [vec![], vec![(value.clone(), "exact_p".into())]] {
        with_proof_local_value_names(names, || {
            let native = synthesize_legacy_call_argument(
                &argument,
                ParameterBinding::default(),
                &state,
                &bound,
            );
            let shared = raise_call_argument(&root, ParameterBinding::default(), &state, &bound);
            assert_eq!(shared, native);
            let call = synthesize_surface_call(
                "pointer_probe",
                std::slice::from_ref(&argument),
                ParameterBinding::default(),
                &state,
                &bound,
            );
            assert_eq!(
                call,
                native.map(|argument| SyntaxTerm::Call {
                    name: "pointer_probe".into(),
                    arguments: vec![argument],
                })
            );
        });
    }
}

/// Reduced from the inclusive-range loop's signed `0 <= total` premise.
/// There is one named word, no program execution, and no recorded snapshot.
fn comparison_over_named_word_round_trip(
    local_type: MachineIntegerType,
    comparison_type: MachineIntegerType,
) {
    let word = OldMachineTerm::Variable(Variable(730_001));
    let state = ExecutionState::new().with_local(
        "x",
        match local_type {
            MachineIntegerType::Int32 => ProgramValue::Int32(word.clone()),
            MachineIntegerType::UInt32 => ProgramValue::UInt32(word.clone()),
            _ => unreachable!(),
        },
    );
    let original = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: comparison_type,
            relation: CompareRelation::LessEqual,
            left: Box::new(OldMachineTerm::constant(0)),
            right: Box::new(word),
        },
        true,
    );
    let surface = synthesize_surface_proposition(&original, ParameterBinding::default(), &state)
        .expect("one current local names the only variable");
    let text = crate::surface::printing::source_click_proposition(&surface);
    let lowered = relower_written_proposition(&surface, &state).unwrap();
    assert_eq!(lowered, original, "raised source: {text}");
}

#[test]
fn signed_comparison_over_a_signed_local_round_trips() {
    comparison_over_named_word_round_trip(MachineIntegerType::Int32, MachineIntegerType::Int32);
}

#[test]
fn unsigned_comparison_over_an_unsigned_local_round_trips() {
    comparison_over_named_word_round_trip(MachineIntegerType::UInt32, MachineIntegerType::UInt32);
}

fn raw_signed_nonnegative(word: OldMachineTerm) -> Proposition {
    Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: Box::new(OldMachineTerm::constant(0)),
            right: Box::new(word),
        },
        true,
    )
}

#[test]
fn unsigned_small_bound_produces_round_tripping_signed_facts() {
    let word = OldMachineTerm::Variable(Variable(730_002));
    let raw_signed_bound = raw_signed_nonnegative(word.clone());
    let converted_signed_bound = raw_signed_nonnegative(OldMachineTerm::sign_cast32(
        MachineIntegerType::UInt32,
        MachineIntegerType::Int32,
        word.clone(),
    ));
    let parent = PureFactContext::new();
    assert!(!parent.contains_assumed_exact(&raw_signed_bound));
    let small = parent.clone().assume_condition(
        OldConditionTerm::unsigned_less_equal(word.clone(), OldMachineTerm::constant(256)),
        true,
    );
    assert!(!small.contains_assumed_exact(&raw_signed_bound));
    let state = ExecutionState::new().with_local("x", ProgramValue::UInt32(word.clone()));
    let signed_word = OldMachineTerm::sign_cast32(
        MachineIntegerType::UInt32,
        MachineIntegerType::Int32,
        word.clone(),
    );
    let upper = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: Box::new(signed_word),
            right: Box::new(OldMachineTerm::constant(256)),
        },
        true,
    );
    for fact in [&converted_signed_bound, &upper] {
        assert!(small.contains_assumed_exact(fact));
        let surface = synthesize_surface_proposition(fact, ParameterBinding::default(), &state)
            .expect("the derived signed bound has a typed Surface form");
        let text = crate::surface::printing::source_click_proposition(&surface);
        assert_eq!(
            relower_written_proposition(&surface, &state).unwrap(),
            *fact,
            "{text}"
        );
    }
    let beyond_sign_bit = parent.assume_condition(
        OldConditionTerm::unsigned_less_equal(word, OldMachineTerm::constant(0x8000_0000)),
        true,
    );
    assert!(!beyond_sign_bit.contains_assumed_exact(&raw_signed_bound));
    assert!(!beyond_sign_bit.contains_assumed_exact(&converted_signed_bound));
}

#[test]
fn unsigned_small_bound_recovers_an_already_converted_signed_source() {
    let signed = OldMachineTerm::Variable(Variable(730_003));
    let unsigned = OldMachineTerm::sign_cast32(
        MachineIntegerType::Int32,
        MachineIntegerType::UInt32,
        signed.clone(),
    );
    let facts = PureFactContext::new().assume_condition(
        OldConditionTerm::unsigned_less_equal(unsigned, OldMachineTerm::constant(256)),
        true,
    );
    assert!(facts.contains_assumed_exact(&raw_signed_nonnegative(signed)));
}

#[test]
fn shared_constructor_fields_preserve_native_spelling_and_refusals() {
    use crate::kernel::{
        AlgebraicTermNode, AlgebraicValue, KernelMatch, KernelTermExport, KernelTermImport,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(999981);
    let names = (BTreeMap::<_, String>::from([(variable, "item".into())]))
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
    let state = ExecutionState::new();
    let word = OldMachineTerm::Variable(variable);
    for value in [
        ProgramValue::Int32(word.clone()),
        ProgramValue::UInt32(word.clone()),
        ProgramValue::Int64(word.clone()),
        ProgramValue::UInt64(word.clone()),
        ProgramValue::Int8(word.clone()),
        ProgramValue::UInt8(word.clone()),
        ProgramValue::Int16(word.clone()),
        ProgramValue::UInt16(word.clone()),
        ProgramValue::Bool(word),
        int32(7),
        ProgramValue::UInt32(OldMachineTerm::uint32_constant(7)),
        ProgramValue::UInt64(OldMachineTerm::uint64_constant(0)),
        ProgramValue::of_bool(OldConditionTerm::Constant(true)),
        ProgramValue::of_bool(OldConditionTerm::Constant(false)),
        ProgramValue::of_bool(OldConditionTerm::Variable(variable)),
    ] {
        let mut native =
            KernelMatch::test_scrutinee(vec![crate::kernel::AlgebraicValueType::Program(
                value.program_type(),
            )]);
        native.node = AlgebraicTermNode::Constructor {
            variant: "Arm".into(),
            fields: vec![AlgebraicValue::Program(value)],
        };
        let expected =
            synthesize_surface_algebraic(&native, ParameterBinding::default(), &state, &names);
        assert!(
            expected.is_some(),
            "constructor field needs a Surface spelling"
        );
        let root = KernelTermImport::default().algebraic(&native);
        let exports = KernelTermExport::algebraic_export_count();
        assert_eq!(
            raise_kernel_term(&root, ParameterBinding::default(), &state, &names),
            expected
        );
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
    }
}

#[test]
fn shared_algebraic_reads_and_variables_raise_without_tree_exports() {
    use crate::kernel::{
        AlgebraicTerm, AlgebraicTermNode, KernelTermExport, KernelTermImport, TypeParameterName,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let ty = TypeParameterName::intern("ReadBoundary");
    let state = ExecutionState::new();
    let pointer = Address::symbolic(Variable(999983));
    let parameters = vec![crate::languages::interface::ImportedParameter::new(
        InterfaceType::ParameterPointer(ty),
        "p".into(),
        None,
    )];
    let arguments = vec![ProgramExpression::Value(ProgramValue::typed_pointer(
        pointer.clone(),
        ProgramType::ParameterPointer(ty),
    ))];
    let binding = ParameterBinding::new(&parameters, &arguments);
    let variable = Variable(999984);
    let names = (BTreeMap::<_, String>::from([(variable, "value".into())]))
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
    for node in [
        AlgebraicTermNode::Variable(variable),
        AlgebraicTermNode::MemoryLoad {
            point: crate::kernel::ProgramPoint::at(&crate::kernel::intern_memory_ref(
                state.memory(),
            )),
            pointer: Box::new(pointer.clone()),
        },
    ] {
        let native = AlgebraicTerm {
            algebraic_type: ty.algebraic_type(),
            node,
        };
        let expected = synthesize_surface_algebraic(&native, binding, &state, &names).unwrap();
        let root = KernelTermImport::default().algebraic(&native);
        let exports = KernelTermExport::algebraic_export_count();
        assert_eq!(
            raise_kernel_term(&root, binding, &state, &names),
            Some(expected)
        );
        assert_eq!(KernelTermExport::algebraic_export_count(), exports);
    }
}

#[test]
fn shared_boolean_raising_preserves_overflow_and_algebraic_spelling() {
    use crate::kernel::{
        AlgebraicTermNode, AlgebraicValue, AlgebraicValueType, KernelMatch, KernelTermExport,
        KernelTermImport,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let variable = Variable(999986);
    let names = (BTreeMap::<_, String>::from([(variable, "x".into())]))
        .into_iter()
        .map(|(var, name)| (var, SurfaceBinder::from(name)))
        .collect::<BTreeMap<_, _>>();
    let mut conditions = vec![];
    for format in [MachineIntegerType::Int32, MachineIntegerType::Int64] {
        for op in [
            OverflowOperation::Add,
            OverflowOperation::Subtract,
            OverflowOperation::Multiply,
        ] {
            conditions.push(OldConditionTerm::Overflows {
                format,
                op,
                left: Box::new(OldMachineTerm::Variable(variable)),
                right: Box::new(OldMachineTerm::Variable(variable)),
            });
        }
    }
    let mut constructor =
        KernelMatch::test_scrutinee(vec![AlgebraicValueType::Program(ProgramType::Int32)]);
    constructor.node = AlgebraicTermNode::Constructor {
        variant: "Arm".into(),
        fields: vec![AlgebraicValue::Program(int32(7))],
    };
    conditions.push(OldConditionTerm::AlgebraicEqual(
        Box::new(constructor.clone()),
        Box::new(constructor),
    ));
    for native in conditions {
        let state = ExecutionState::new();
        let expected =
            synthesize_surface_bool(&native, ParameterBinding::default(), &state, &names).unwrap();
        let root = KernelTermImport::default().condition(&native);
        let exports = (
            KernelTermExport::machine_export_count(),
            KernelTermExport::algebraic_export_count(),
        );
        assert_eq!(
            raise_kernel_term(&root, ParameterBinding::default(), &state, &names),
            Some(expected)
        );
        assert_eq!(
            (
                KernelTermExport::machine_export_count(),
                KernelTermExport::algebraic_export_count()
            ),
            exports
        );
    }
}

#[test]
fn shared_pointer_comparisons_preserve_native_spelling() {
    use crate::kernel::{KernelTermImport, Pointer};
    let _session = crate::kernel::VerificationSession::enter();
    let left = Pointer::new(
        Address::symbolic(Variable(999988)),
        ProgramType::Int32Pointer,
    );
    let right = Pointer::new(
        Address::symbolic(Variable(999989)),
        ProgramType::Int32Pointer,
    );
    let parameters = ["p", "q"].map(|name| {
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32Pointer,
            name.into(),
            None,
        )
    });
    let arguments = [left.clone(), right.clone()]
        .map(|value| ProgramExpression::Value(ProgramValue::Pointer(value)));
    let binding = ParameterBinding::new(&parameters, &arguments);
    let state = ExecutionState::new();
    let names = BTreeMap::<Variable, SurfaceBinder>::new();
    for native in [
        OldConditionTerm::PointerEqual(Box::new(left.clone()), Box::new(right.clone())),
        OldConditionTerm::AddressEqual(
            Box::new(left.address().clone()),
            Box::new(right.address().clone()),
        ),
        OldConditionTerm::AddressEqual(Box::new(left.address().clone()), Box::new(Address::null())),
    ] {
        let expected = synthesize_surface_bool(&native, binding, &state, &names).unwrap();
        let root = KernelTermImport::default().condition(&native);
        assert_eq!(
            raise_kernel_term(&root, binding, &state, &names),
            Some(expected)
        );
    }
}

#[test]
fn closed_machine_orders_round_trip_after_checked_rewrite() {
    use crate::kernel::proof::PureFactStore;
    for (spelling, suffix, value) in [
        (
            "uint32",
            "u32",
            ProgramValue::UInt32(OldMachineTerm::Variable(Variable(999701))),
        ),
        (
            "int64",
            "i64",
            ProgramValue::Int64(OldMachineTerm::Variable(Variable(999701))),
        ),
        (
            "uint64",
            "u64",
            ProgramValue::UInt64(OldMachineTerm::Variable(Variable(999701))),
        ),
    ] {
        for bound in [5, 100] {
            let _session = crate::kernel::VerificationSession::enter();
            let state = ExecutionState::new().with_local("x", value.clone());
            let values = ProgramValueBindings::from([("x".to_string(), value.clone())]);
            let empty = BTreeMap::new();
            let lower = |surface: &SyntaxProposition| {
                crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
                    surface, &PureFactContext::new(), ContractEnvironment::new(&values, &empty),
                    FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                    SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::new(&[])),
                    FixedStateLoweringOptions::default(),
                ).unwrap().0
            };
            let file = parser::parse(&format!("theorem probe(x: {spelling}) {{ requires x == 9{suffix}; ensures x <= {bound}{suffix}; }}")).unwrap();
            let theorem = &file.theorem_definitions()[0];
            let Requirement::Proposition(equality) = &theorem.requires()[0] else {
                panic!("requirement")
            };
            let Ensure::Proposition(goal) = theorem.ensures()[0].ensure() else {
                panic!("ensure")
            };
            let equality = lower(equality);
            let produced = PureFactStore::from_ordered(std::slice::from_ref(&equality))
                .check_equality_rewrite(&lower(goal), &equality)
                .unwrap()
                .proposition()
                .clone();
            let Some((condition @ OldConditionTerm::Compare { .. }, true)) =
                produced.old_condition()
            else {
                panic!("retained native comparison: {produced:?}")
            };
            assert_eq!(PureFactContext::new().decide(condition), Some(9 <= bound));
            let raised =
                synthesize_surface_proposition(&produced, ParameterBinding::default(), &state)
                    .unwrap();
            let text = crate::surface::printing::source_click_proposition(&raised);
            let file = parser::parse(&format!(
                "theorem probe(x: {spelling}) {{ requires {text}; ensures true; }}"
            ))
            .unwrap();
            let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0]
            else {
                panic!("requirement")
            };
            assert_eq!(
                lower(written),
                produced,
                "{spelling}, bound {bound}: {text}"
            );
        }
    }
}

#[test]
fn closed_machine_order_keeps_a_defined_right_disjunct() {
    let file = parser::parse(
        "theorem probe() { requires 64u64 >= 64u64 or (1u64 << 1u64) == 2u64; ensures true; }",
    )
    .unwrap();
    let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
        panic!("requirement")
    };
    let lowered = relower_written_proposition(written, &ExecutionState::new()).unwrap();
    assert!(matches!(lowered, Proposition::Or(..)));
}

#[test]
fn closed_machine_order_short_circuits_undefined_right_operand() {
    let file = parser::parse(
        "theorem probe() { requires 64u64 >= 64u64 or (1u64 << 64u64) == 2u64; ensures true; }",
    )
    .unwrap();
    let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
        panic!("requirement")
    };
    let lowered = relower_written_proposition(written, &ExecutionState::new()).unwrap();
    assert!(
        matches!(&lowered, condition_source_0 @ Proposition::ConditionIs(
            _,
            true
        ) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare {
                format: crate::kernel::MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                ..
            }, _))))
    );
}

#[test]
fn closed_machine_order_lowering_preserves_relations_and_truth_checking() {
    use crate::kernel::MachineIntegerType as T;
    let state = ExecutionState::new();
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        for (operator, relation, truth) in [
            ("<", CompareRelation::LessThan, false),
            ("<=", CompareRelation::LessEqual, false),
            (">", CompareRelation::GreaterThan, true),
            (">=", CompareRelation::GreaterEqual, true),
        ] {
            let file = parser::parse(&format!("theorem probe() {{ requires (9 as {spelling}) {operator} (5 as {spelling}); ensures true; }}")).unwrap();
            let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0]
            else {
                panic!("requirement")
            };
            let lowered = relower_written_proposition(written, &state).unwrap();
            let Some((
                condition @ OldConditionTerm::Compare {
                    format: actual,
                    relation: actual_relation,
                    ..
                },
                true,
            )) = lowered.old_condition()
            else {
                panic!("{spelling} {operator}: {lowered:?}")
            };
            assert_eq!((*actual, *actual_relation), (format, relation));
            assert_eq!(PureFactContext::new().decide(condition), Some(truth));
            assert_eq!(
                crate::kernel::proof::checked_branch_fact_is_available(
                    &crate::kernel::proof::PureFactStore::from_ordered(&[]),
                    &lowered,
                ),
                truth,
            );
        }
    }
}

/// Parsed arithmetic, checked rewriting, and the ordinary speller retain one
/// exact form after a substitution exposes literal operands.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn machine_arithmetic_round_trips_after_checked_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    use crate::kernel::proof::PureFactStore;
    let mut failures = Vec::new();
    for (format, spelling, suffix) in [
        (T::Int32, "int32", ""),
        (T::UInt32, "uint32", "u32"),
        (T::Int64, "int64", "i64"),
        (T::UInt64, "uint64", "u64"),
    ] {
        for bound in [5, 100] {
            for operator in [
                None,
                Some("+"),
                Some("-"),
                Some("*"),
                Some("/"),
                Some("%"),
                Some("<<"),
                Some(">>"),
            ] {
                let _session = crate::kernel::VerificationSession::enter();
                let value = OldMachineTerm::Variable(Variable(999701));
                let value = match format {
                    T::Int32 => ProgramValue::Int32(value),
                    T::UInt32 => ProgramValue::UInt32(value),
                    T::Int64 => ProgramValue::Int64(value),
                    T::UInt64 => ProgramValue::UInt64(value),
                    _ => unreachable!(),
                };
                let state = ExecutionState::new().with_local("x", value.clone());
                let values = ProgramValueBindings::from([("x".to_string(), value)]);
                let empty = BTreeMap::new();
                let lower = |surface: &SyntaxProposition| {
                    crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
                        surface, &PureFactContext::new(), ContractEnvironment::new(&values, &empty),
                        FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                        SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::new(&[])),
                        FixedStateLoweringOptions::default(),
                    ).unwrap().0
                };
                let expression = operator.map_or_else(
                    || "x".to_string(),
                    |op| format!("(x {op} 3{suffix}) as {spelling}"),
                );
                let file = parser::parse(&format!("theorem probe(x: {spelling}) {{ requires x == 9{suffix}; ensures {expression} <= {bound}{suffix}; }}")).unwrap();
                let theorem = &file.theorem_definitions()[0];
                let Requirement::Proposition(equality) = &theorem.requires()[0] else {
                    panic!("requirement")
                };
                let Ensure::Proposition(goal) = theorem.ensures()[0].ensure() else {
                    panic!("ensure")
                };
                let equality = lower(equality);
                let original = lower(goal);
                let facts = PureFactStore::from_ordered(std::slice::from_ref(&equality));
                let produced = facts
                    .check_equality_rewrite(&original, &equality)
                    .unwrap()
                    .proposition()
                    .clone();
                let value = match operator {
                    None => 9,
                    Some("+") => 12,
                    Some("-") => 6,
                    Some("*") => 27,
                    Some("/") => 3,
                    Some("%") => 0,
                    Some("<<") => 72,
                    Some(">>") => 1,
                    _ => unreachable!(),
                };
                let Proposition::ConditionIs(condition, truth) = &produced else {
                    panic!("expected an arithmetic comparison: {produced:?}")
                };
                assert_eq!(
                    PureFactContext::new()
                        .decide(condition.old_form())
                        .map(|value| value == *truth),
                    Some(value <= bound)
                );
                let Some(raised) =
                    synthesize_surface_proposition(&produced, ParameterBinding::default(), &state)
                else {
                    println!("UNSPELLABLE {format:?} {operator:?} bound={bound}: {produced:?}");
                    failures.push(format!(
                        "{format:?} {operator:?} bound={bound} (unspellable)"
                    ));
                    continue;
                };
                let text = crate::surface::printing::source_click_proposition(&raised);
                let file = parser::parse(&format!(
                    "theorem probe(x: {spelling}) {{ requires {text}; ensures true; }}"
                ))
                .unwrap();
                let Requirement::Proposition(written) =
                    &file.theorem_definitions()[0].requires()[0]
                else {
                    panic!("requirement")
                };
                let restored = lower(written);
                if restored != produced {
                    println!(
                        "BROKEN {format:?} {operator:?} bound={bound}: {text}\n  produced: {produced:?}\n  restored: {restored:?}"
                    );
                    failures.push(format!("{format:?} {operator:?} bound={bound}"));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "round-trip failures: {}",
        failures.join(", ")
    );
}

fn assert_narrow_comparison_round_trip(
    proposition: &Proposition,
    format: MachineIntegerType,
    state: &ExecutionState,
    lower: impl Fn(&SyntaxProposition) -> Proposition,
) {
    let Some((OldConditionTerm::Compare { format: actual, .. }, _)) = proposition.old_condition()
    else {
        panic!("expected a retained {format:?} comparison: {proposition:?}")
    };
    assert_eq!(*actual, format);
    let raised = synthesize_surface_proposition(proposition, ParameterBinding::default(), state)
        .expect("a narrow comparison has an exact typed spelling");
    let text = crate::surface::printing::source_click_proposition(&raised);
    let parsed = parser::parse(&format!(
        "theorem probe() {{ requires {text}; ensures true; }}"
    ))
    .unwrap();
    let Requirement::Proposition(written) = &parsed.theorem_definitions()[0].requires()[0] else {
        panic!()
    };
    assert_eq!(lower(written), *proposition, "{format:?}: {text}");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn narrow_comparisons_round_trip_after_checked_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    use crate::kernel::proof::PureFactStore;
    for (source, source_spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        for (target, spelling) in [
            (T::Int8, "int8"),
            (T::UInt8, "uint8"),
            (T::Int16, "int16"),
            (T::UInt16, "uint16"),
        ] {
            for operator in ["<", "<=", ">", ">="] {
                for bound in [5, 100] {
                    let _session = crate::kernel::VerificationSession::enter();
                    let x = source.value_from_term(OldMachineTerm::Variable(Variable(999702)));
                    let state = ExecutionState::new().with_local("x", x.clone());
                    let values = ProgramValueBindings::from([("x".to_string(), x)]);
                    let empty = BTreeMap::new();
                    let lower = |surface: &SyntaxProposition| {
                        crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
                            surface, &PureFactContext::new(), ContractEnvironment::new(&values, &empty),
                            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                            SpecDefinitions::new(&PredicateEnvironment::new(&[]), &ClickFunctionEnvironment::new(&[])),
                            FixedStateLoweringOptions::default(),
                        ).unwrap().0
                    };
                    let input = parser::parse(&format!("theorem probe() {{ requires x == (9 as {}); ensures to_integer(x as {spelling}) {operator} {bound}; }}", source_spelling)).unwrap();
                    let theorem = &input.theorem_definitions()[0];
                    let Requirement::Proposition(equality) = &theorem.requires()[0] else {
                        panic!()
                    };
                    let Ensure::Proposition(goal) = theorem.ensures()[0].ensure() else {
                        panic!()
                    };
                    let equality = lower(equality);
                    let produced = PureFactStore::from_ordered(std::slice::from_ref(&equality))
                        .check_equality_rewrite(&lower(goal), &equality)
                        .unwrap()
                        .proposition()
                        .clone();
                    assert_narrow_comparison_round_trip(&produced, target, &state, lower);
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn narrow_comparison_literals_preserve_format_polarity_and_builtin_truth() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int8, "int8"),
        (T::UInt8, "uint8"),
        (T::Int16, "int16"),
        (T::UInt16, "uint16"),
    ] {
        let (min, max) = format.format().bounds();
        for (left, right, less) in [(min.clone(), max.clone(), true), (max, min, false)] {
            for (operator, holds) in [("<", less), ("<=", less), (">", !less), (">=", !less)] {
                let _session = crate::kernel::VerificationSession::enter();
                let state = ExecutionState::new();
                let input = parser::parse(&format!("theorem probe() {{ requires ({left} as {spelling}) {operator} ({right} as {spelling}); ensures true; }}")).unwrap();
                let Requirement::Proposition(written) =
                    &input.theorem_definitions()[0].requires()[0]
                else {
                    panic!()
                };
                let Proposition::ConditionIs(condition, true) =
                    relower_written_proposition(written, &state).unwrap()
                else {
                    panic!()
                };
                for truth in [true, false] {
                    let proposition = Proposition::condition_is(condition.clone(), truth);
                    assert_narrow_comparison_round_trip(&proposition, format, &state, |p| {
                        relower_written_proposition(p, &state).unwrap()
                    });
                    assert_eq!(
                        crate::kernel::reasoning::path_facts::solve_builtin_prop(&proposition),
                        holds == truth
                    );
                }
            }
        }
    }
}

#[test]
fn narrow_symbolic_comparisons_keep_their_existing_normal_forms() {
    use crate::kernel::MachineIntegerType as T;
    for format in [T::Int8, T::UInt8, T::Int16, T::UInt16] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new()
            .with_local(
                "a",
                format.value_from_term(OldMachineTerm::Variable(Variable(999703))),
            )
            .with_local(
                "b",
                format.value_from_term(OldMachineTerm::Variable(Variable(999704))),
            );
        for operator in ["<", "<=", ">", ">=", "=="] {
            // Symbolic Integer observations keep their existing canonical
            // direction. Test facts the source actually produces, separately
            // from the newly retained closed comparisons above.
            let parsed = parser::parse(&format!("theorem probe() {{ requires to_integer(a) {operator} to_integer(b); ensures true; }}")).unwrap();
            let Requirement::Proposition(written) = &parsed.theorem_definitions()[0].requires()[0]
            else {
                panic!()
            };
            let Proposition::ConditionIs(condition, true) =
                relower_written_proposition(written, &state).unwrap()
            else {
                panic!()
            };
            for truth in [true, false] {
                let proposition = Proposition::condition_is(condition.clone(), truth);
                assert_narrow_comparison_round_trip(&proposition, format, &state, |p| {
                    relower_written_proposition(p, &state).unwrap()
                });
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: retained pthread value parse/lower round trip"]
fn pthread_handle_words_use_c_names_and_retained_states() {
    use crate::kernel::{KernelTermImport, ThreadHandleId};
    let _session = crate::kernel::VerificationSession::enter();
    let native = OldMachineTerm::ThreadHandle(ThreadHandleId(1008820));
    let root = KernelTermImport::default().machine(MachineIntegerType::UInt64, &native);
    let saved = ExecutionState::new().with_local("h", ProgramValue::UInt64(native));
    let now = saved.clone().with_local(
        "h",
        ProgramValue::UInt64(OldMachineTerm::uint64_constant(0)),
    );
    let current =
        raise_kernel_term(&root, ParameterBinding::default(), &saved, &BTreeMap::new()).unwrap();
    assert_eq!(diagnostics::describe_contract_expression(&current), "h");
    let selector = ProgramPointSelector::Mark("created".into());
    let mut points = RecordedStates::new();
    points.insert(selector.clone(), saved);
    let _points = SynthesisRecordedPointsScope::enter(&points);
    let retained =
        raise_kernel_term(&root, ParameterBinding::default(), &now, &BTreeMap::new()).unwrap();
    assert!(matches!(&retained, SyntaxTerm::At { selector: actual, .. } if *actual == selector));
    let text = diagnostics::describe_contract_expression(&retained);
    assert_eq!(text, "at(created, h)");
    let parsed = parser::parse(&format!(
        "theorem probe() {{ requires {text} == 0; ensures true; }}"
    ))
    .unwrap();
    let Requirement::Proposition(claim) = &parsed.theorem_definitions()[0].requires()[0] else {
        panic!("comparison")
    };
    let lowered = relower_written_proposition_with_states(claim, &now, &now, &points).unwrap();
    let Proposition::ConditionIs(condition, true) = lowered else {
        panic!("comparison")
    };
    let view = crate::kernel::machine_integer::comparison::structural_comparison_view(
        condition.old_form(),
    )
    .unwrap();
    assert_eq!(view.format, MachineIntegerType::Int64);
    assert_eq!(
        crate::kernel::KernelTerm::retained_machine_operand(
            view.format,
            view.operands[0].operand_view()
        ),
        root.with_machine_observation_type(view.format)
    );
}

fn check_int64_literal_comparison_round_trips(values: &[i64]) {
    use crate::kernel::proof::PureFactStore;
    for value in values {
        for operator in ["<", "<=", ">", ">="] {
            for reverse in [false, true] {
                let _session = crate::kernel::VerificationSession::enter();
                let state = ExecutionState::new().with_local(
                    "x",
                    ProgramValue::Int64(OldMachineTerm::Variable(Variable(999707))),
                );
                let parse = |text: &str| {
                    let file = parser::parse(&format!(
                        "theorem probe() {{ requires {text}; ensures true; }}"
                    ))
                    .unwrap();
                    let Requirement::Proposition(p) = &file.theorem_definitions()[0].requires()[0]
                    else {
                        panic!("expected a proposition")
                    };
                    p.clone()
                };
                let equality = relower_written_proposition(
                    &parse(&format!("x == ({value}i64 as int64)")),
                    &state,
                )
                .unwrap();
                let expression = if reverse {
                    format!("100i64 {operator} x")
                } else {
                    format!("x {operator} 100i64")
                };
                let original = relower_written_proposition(&parse(&expression), &state).unwrap();
                let rewritten = PureFactStore::from_ordered(std::slice::from_ref(&equality))
                    .check_equality_rewrite(&original, &equality)
                    .unwrap()
                    .proposition()
                    .clone();
                let Proposition::ConditionIs(condition, true) = rewritten else {
                    panic!("expected a comparison")
                };
                for truth in [true, false] {
                    let produced = Proposition::condition_is(condition.clone(), truth);
                    let raised = synthesize_surface_proposition(
                        &produced,
                        ParameterBinding::default(),
                        &state,
                    )
                    .unwrap();
                    let text = crate::surface::printing::source_click_proposition(&raised);
                    let restored = relower_written_proposition(&parse(&text), &state).unwrap();
                    assert_eq!(
                        restored, produced,
                        "value={value} reverse={reverse} {operator}, truth={truth}: {text}"
                    );
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn negative_int64_comparisons_round_trip_after_rewrite() {
    check_int64_literal_comparison_round_trips(&[-10, -1]);
}

#[test]
fn int64_boundary_comparisons_round_trip_after_rewrite() {
    check_int64_literal_comparison_round_trips(&[i64::MIN, i64::MAX]);
}

#[test]
fn nonnegative_int64_comparisons_round_trip_after_rewrite() {
    check_int64_literal_comparison_round_trips(&[0, 9]);
}

#[test]
fn negative_int64_comparisons_round_trip_under_point_selectors() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new();
    let word = |n| {
        SyntaxTerm::ProgramExpression(ProgramExpression::Value(ProgramValue::Int64(
            OldMachineTerm::int64_constant(n),
        )))
    };
    for left in [
        word(-9),
        SyntaxTerm::Old(Box::new(word(-9))),
        SyntaxTerm::At {
            selector: ProgramPointSelector::from(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            expression: Box::new(word(-9)),
        },
    ] {
        let original = SyntaxProposition::Comparison {
            left,
            operator: ComparisonOperator::LessEqual,
            right: word(100),
        };
        let expected = relower_written_proposition(&original, &state).unwrap();
        let text = crate::surface::printing::source_click_proposition(&original);
        let parsed = parser::parse(&format!(
            "theorem probe() {{ requires {text}; ensures true; }}"
        ))
        .unwrap();
        let Requirement::Proposition(written) = &parsed.theorem_definitions()[0].requires()[0]
        else {
            panic!("expected a proposition")
        };
        assert_eq!(
            relower_written_proposition(written, &state).unwrap(),
            expected,
            "{text}"
        );
    }
}

fn check_comparison_guard_conditional_round_trips(
    format: crate::kernel::MachineIntegerType,
    spelling: &str,
    guards: &[(&str, u64)],
    operators: &[&str],
    replacement: u64,
) {
    for operator in operators {
        for &(guard, bound) in guards {
            let guard = format!("{guard} {operator} ({bound} as {spelling})");
            for reverse in [false, true] {
                check_conditional_round_trip(format, spelling, &guard, reverse, replacement);
            }
        }
    }
}

fn check_conditional_round_trip(
    format: crate::kernel::MachineIntegerType,
    spelling: &str,
    guard: &str,
    reverse: bool,
    replacement: u64,
) {
    let equality = format!("x == ({replacement} as {spelling})");
    check_conditional_round_trip_using_equality(format, spelling, guard, reverse, &equality);
}

fn check_conditional_round_trip_using_equality(
    format: crate::kernel::MachineIntegerType,
    spelling: &str,
    guard: &str,
    reverse: bool,
    equality: &str,
) {
    check_conditional_round_trip_with_arm(format, spelling, guard, reverse, equality, "x");
}

fn check_conditional_round_trip_with_arm(
    format: crate::kernel::MachineIntegerType,
    spelling: &str,
    guard: &str,
    reverse: bool,
    equality: &str,
    then_value: &str,
) {
    let fixture = ConditionalRoundTrip::new(format, spelling);
    let equality = fixture.lower(equality);
    let original = fixture.goal(guard, reverse, then_value);
    fixture.check(&original, &equality, guard, reverse);
}

struct ConditionalRoundTrip<'a> {
    spelling: &'a str,
    state: ExecutionState,
    _session: crate::kernel::VerificationSession,
}

impl<'a> ConditionalRoundTrip<'a> {
    fn new(format: MachineIntegerType, spelling: &'a str) -> Self {
        let session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new()
            .with_local(
                "x",
                format.value_from_term(OldMachineTerm::Variable(Variable(999708))),
            )
            .with_local(
                "y",
                format.value_from_term(OldMachineTerm::Variable(Variable(999709))),
            )
            .with_local(
                "z",
                format.value_from_term(OldMachineTerm::Variable(Variable(999710))),
            )
            .with_local(
                "flag",
                ProgramValue::of_bool(OldConditionTerm::Variable(Variable(999711))),
            );
        Self {
            spelling,
            state,
            _session: session,
        }
    }

    fn lower(&self, text: &str) -> Proposition {
        let file = parser::parse(&format!(
            "theorem probe() {{ requires {text}; ensures true; }}"
        ))
        .unwrap();
        let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
            panic!("expected a proposition");
        };
        relower_written_proposition(written, &self.state).unwrap()
    }

    fn goal(&self, guard: &str, reverse: bool, then_value: &str) -> Proposition {
        let spelling = self.spelling;
        let value = format!("to_integer(if {guard} {{ {then_value} }} else {{ 3 as {spelling} }})");
        let goal = if reverse {
            format!("100 <= {value}")
        } else {
            format!("{value} <= 100")
        };
        self.lower(&goal)
    }

    fn check(&self, original: &Proposition, equality: &Proposition, guard: &str, reverse: bool) {
        use crate::kernel::proof::PureFactStore;
        let spelling = self.spelling;
        let rewritten = PureFactStore::from_ordered(std::slice::from_ref(equality))
            .check_equality_rewrite(original, equality)
            .unwrap()
            .proposition()
            .clone();
        let Proposition::ConditionIs(condition, true) = rewritten else {
            panic!("expected a comparison");
        };
        for truth in [true, false] {
            let produced = Proposition::condition_is(condition.clone(), truth);
            let raised =
                synthesize_surface_proposition(&produced, ParameterBinding::default(), &self.state)
                    .unwrap();
            assert_eq!(
                relower_written_proposition(&raised, &self.state).unwrap(),
                produced,
                "Surface AST: {spelling}, guard={guard}, reverse={reverse}, truth={truth}, equality={equality:?}"
            );
            let text = crate::surface::printing::source_click_proposition(&raised);
            assert_eq!(
                self.lower(&text),
                produced,
                "{spelling}, guard={guard}, reverse={reverse}, truth={truth}, equality={equality:?}: {text}"
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn closed_uint32_order_guard_conditionals_round_trip_after_rewrite() {
    check_comparison_guard_conditional_round_trips(
        crate::kernel::MachineIntegerType::UInt32,
        "uint32",
        &[("x", 8), ("x", 10)],
        &["<", "<=", ">", ">="],
        9,
    );
}
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn closed_int64_order_guard_conditionals_round_trip_after_rewrite() {
    check_comparison_guard_conditional_round_trips(
        crate::kernel::MachineIntegerType::Int64,
        "int64",
        &[("x", 8), ("x", 10)],
        &["<", "<=", ">", ">="],
        9,
    );
}
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn closed_uint64_order_guard_conditionals_round_trip_after_rewrite() {
    check_comparison_guard_conditional_round_trips(
        crate::kernel::MachineIntegerType::UInt64,
        "uint64",
        &[("x", 8), ("x", 10)],
        &["<", "<=", ">", ">="],
        9,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn symbolic_order_guard_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        check_comparison_guard_conditional_round_trips(
            format,
            spelling,
            &[("y", 8)],
            &["<", "<=", ">", ">="],
            9,
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn closed_wide_equality_guard_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [(T::Int64, "int64"), (T::UInt64, "uint64")] {
        check_comparison_guard_conditional_round_trips(
            format,
            spelling,
            &[("x", 8), ("x", 9)],
            &["==", "!="],
            9,
        );
    }
}

#[test]
fn closed_unsigned_equality_guards_keep_high_bit_literals() {
    check_comparison_guard_conditional_round_trips(
        crate::kernel::MachineIntegerType::UInt64,
        "uint64",
        &[("x", u64::MAX)],
        &["==", "!="],
        u64::MAX,
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn symbolic_equality_guard_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        for op in ["==", "!="] {
            for guard in [
                format!("y {op} (8 as {spelling})"),
                format!("(8 as {spelling}) {op} y"),
                format!("y {op} z"),
            ] {
                for reverse in [false, true] {
                    check_conditional_round_trip(format, spelling, &guard, reverse, 9);
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn symbolic_unsigned_equality_guards_keep_high_bit_literals() {
    for op in ["==", "!="] {
        for guard in [
            format!("y {op} {}u64", u64::MAX),
            format!("{}u64 {op} y", u64::MAX),
        ] {
            for reverse in [false, true] {
                check_conditional_round_trip(
                    crate::kernel::MachineIntegerType::UInt64,
                    "uint64",
                    &guard,
                    reverse,
                    9,
                );
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn boolean_equality_guards_round_trip_after_rewrite() {
    use MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        let mut fixture = ConditionalRoundTrip::new(format, spelling);
        for (name, id) in [("a", 999712), ("b", 999713)] {
            fixture.state = fixture.state.with_local(
                name,
                ProgramValue::of_bool(OldConditionTerm::Variable(Variable(id))),
            );
        }
        for replacement in [
            "if a == b { true } else { false }",
            "a",
            "if y < z { true } else { false }",
        ] {
            let equality = fixture.lower(&format!("flag == ({replacement})"));
            let literal = format!("(5 as {spelling})");
            for guard in ["flag", "not flag"] {
                for arm in ["x", literal.as_str()] {
                    for reverse in [false, true] {
                        let original = fixture.goal(guard, reverse, arm);
                        fixture.check(&original, &equality, guard, reverse);
                    }
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn boolean_variable_guard_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        for guard in ["flag", "not flag"] {
            for reverse in [false, true] {
                check_conditional_round_trip(format, spelling, guard, reverse, 9);
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn reflexive_guard_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        for op in ["==", "!=", "<", "<=", ">", ">="] {
            let guard = format!("x {op} y");
            for reverse in [false, true] {
                check_conditional_round_trip_using_equality(
                    format, spelling, &guard, reverse, "x == y",
                );
            }
        }
    }
}

#[test]
fn closed_machine_equality_lowering_retains_its_comparison() {
    use crate::kernel::MachineIntegerType as T;
    let state = ExecutionState::new();
    // A wide equality is filed at `int64`, as the folding constructor files
    // a symbolic one.
    for (spelling, filed) in [
        ("int8", T::Int8),
        ("uint8", T::UInt8),
        ("int16", T::Int16),
        ("uint16", T::UInt16),
        ("int32", T::Int32),
        ("uint32", T::UInt32),
        ("int64", T::Int64),
        ("uint64", T::Int64),
    ] {
        for (right, operator, held, truth) in [
            (5, "==", true, false),
            (9, "==", true, true),
            (5, "!=", false, true),
            (9, "!=", false, false),
        ] {
            let source = format!(
                "theorem probe() {{ requires (9 as {spelling}) {operator} ({right} as {spelling}); ensures true; }}"
            );
            let file = parser::parse(&source).unwrap();
            let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0]
            else {
                panic!("requirement")
            };
            let lowered = relower_written_proposition(written, &state).unwrap();
            let Some((
                condition @ OldConditionTerm::Compare {
                    format: actual,
                    relation: CompareRelation::Equal,
                    ..
                },
                actual_held,
            )) = lowered.old_condition()
            else {
                panic!("{source}: {lowered:?}")
            };
            assert_eq!((*actual, *actual_held), (filed, held), "{source}");
            assert_eq!(
                PureFactContext::new().decide(condition) == Some(held),
                truth,
                "{source}"
            );
            assert_eq!(
                crate::kernel::machine_integer::comparison::closed_condition_value(
                    crate::kernel::BooleanOperandView::Native(condition)
                ) == Some(held),
                truth,
                "{source}: {condition:?}"
            );
            let raised =
                synthesize_surface_proposition(&lowered, ParameterBinding::default(), &state)
                    .unwrap();
            assert_eq!(
                relower_written_proposition(&raised, &state).unwrap(),
                lowered,
                "{source}: {}",
                crate::surface::printing::source_click_proposition(&raised)
            );
        }
    }
}

#[test]
fn a_constant_condition_raises_as_a_bool_literal_that_lowers_back() {
    let state = ExecutionState::new();
    for constant in [false, true] {
        for held in [false, true] {
            let kernel = Proposition::condition_is(OldConditionTerm::Constant(constant), held);
            let raised =
                synthesize_surface_proposition(&kernel, ParameterBinding::default(), &state)
                    .unwrap();
            let text = crate::surface::printing::source_click_proposition(&raised);
            let literal = if constant { "true" } else { "false" };
            let expected = if held {
                literal.to_string()
            } else {
                format!("not {literal}")
            };
            assert_eq!(text, expected);
            assert_eq!(
                relower_written_proposition(&raised, &state).unwrap(),
                kernel
            );
            let file = parser::parse(&format!(
                "theorem probe() {{ requires {text}; ensures true; }}"
            ))
            .unwrap();
            let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0]
            else {
                panic!("requirement")
            };
            assert_eq!(written, &raised, "{text}");
            assert_eq!(
                relower_written_proposition(written, &state).unwrap(),
                kernel,
                "{text}"
            );
        }
    }
}

#[test]
fn closed_bool_literal_comparison_lowering_retains_its_comparison() {
    let state = ExecutionState::new();
    for (left, operator, right, held, truth) in [
        (true, "==", false, true, false),
        (true, "==", true, true, true),
        (false, "!=", true, false, true),
        (true, "!=", true, false, false),
    ] {
        let source =
            format!("theorem probe() {{ requires {left} {operator} {right}; ensures true; }}");
        let file = parser::parse(&source).unwrap();
        let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
            panic!("requirement")
        };
        let lowered = relower_written_proposition(written, &state).unwrap();
        let Some((condition @ OldConditionTerm::BoolEqual(..), actual_held)) =
            lowered.old_condition()
        else {
            panic!("{source}: {lowered:?}")
        };
        assert_eq!(*actual_held, held, "{source}");
        assert_eq!(
            crate::kernel::machine_integer::comparison::closed_condition_value(
                crate::kernel::BooleanOperandView::Native(condition)
            ) == Some(held),
            truth,
            "{source}"
        );
        assert_eq!(
            PureFactContext::new().decide(condition) == Some(held),
            truth,
            "{source}"
        );
        let raised =
            synthesize_surface_proposition(&lowered, ParameterBinding::default(), &state).unwrap();
        assert_eq!(
            relower_written_proposition(&raised, &state).unwrap(),
            lowered,
            "{source}: {}",
            crate::surface::printing::source_click_proposition(&raised)
        );
    }
}

fn bitwise_round_trip_operands(spelling: &str) -> [String; 4] {
    [
        format!("z & (7 as {spelling})"),
        format!("z | (7 as {spelling})"),
        format!("z ^ (7 as {spelling})"),
        "~z".into(),
    ]
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.2s in the parallel gate"]
fn nested_machine_conditionals_round_trip_after_rewrite() {
    use MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        let mut fixture = ConditionalRoundTrip::new(format, spelling);
        fixture.state = fixture.state.with_local(
            "inner",
            ProgramValue::of_bool(OldConditionTerm::Variable(Variable(999712))),
        );
        for replacement in [
            "y".into(),
            format!("y & (7 as {spelling})"),
            "if inner { y } else { z }".into(),
            format!("if y < z {{ y }} else {{ 4 as {spelling} }}"),
        ] {
            let equality = fixture.lower(&format!("x == ({replacement})"));
            for guard in ["flag", "not flag", "y < z", "y == z"] {
                for reverse in [false, true] {
                    let original = fixture.goal(guard, reverse, "x");
                    fixture.check(&original, &equality, guard, reverse);
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn bitwise_arm_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        for operand in bitwise_round_trip_operands(spelling) {
            let equality = format!("x == ({operand})");
            for guard in ["flag", "not flag"] {
                for reverse in [false, true] {
                    check_conditional_round_trip_using_equality(
                        format, spelling, guard, reverse, &equality,
                    );
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4.4s in the parallel gate"]
fn bitwise_guard_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        // The source goal depends on the guard and comparison direction,
        // while the equality depends only on the bitwise operand.
        let fixture = ConditionalRoundTrip::new(format, spelling);
        let equalities = bitwise_round_trip_operands(spelling)
            .map(|operand| fixture.lower(&format!("x == ({operand})")));
        for guard in [
            "x < y", "x <= y", "x > y", "x >= y", "x == y", "x != y", "y < x", "y <= x", "y > x",
            "y >= x", "y == x", "y != x",
        ] {
            for reverse in [false, true] {
                let original = fixture.goal(guard, reverse, "z");
                for equality in &equalities {
                    fixture.check(&original, equality, guard, reverse);
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn intrinsically_decided_bitwise_guards_retain_their_conditionals() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new()
            .with_local(
                "z",
                format.value_from_term(OldMachineTerm::Variable(Variable(999710))),
            )
            .with_local(
                "y",
                format.value_from_term(OldMachineTerm::Variable(Variable(999709))),
            );
        for guard in [
            format!("(z & (7 as {spelling})) < (100 as {spelling})"),
            format!("(z ^ (7 as {spelling})) == (z ^ (7 as {spelling}))"),
            format!("(z | (7 as {spelling})) < (z | (7 as {spelling}))"),
            "(~z) == (~z)".into(),
            "(~z) < (~z)".into(),
            "(z >> 1) == (z >> 1)".into(),
            "(z >> 1) < (z >> 1)".into(),
        ] {
            let text = format!("to_integer(if {guard} {{ y }} else {{ 3 as {spelling} }}) <= 100");
            let file = parser::parse(&format!(
                "theorem probe() {{ requires {text}; ensures true; }}"
            ))
            .unwrap();
            let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0]
            else {
                panic!()
            };
            let original = relower_written_proposition(written, &state).unwrap();
            assert!(
                matches!(&original, condition_source_0 @ Proposition::ConditionIs(_, true) if matches!(condition_source_0.old_condition(), Some((OldConditionTerm::Compare { left, .. }, _)) if (matches!(left.as_ref(), OldMachineTerm::If { .. })))),
                "{text}: {original:?}"
            );
            let raised =
                synthesize_surface_proposition(&original, ParameterBinding::default(), &state)
                    .unwrap();
            assert_eq!(
                relower_written_proposition(&raised, &state).unwrap(),
                original,
                "{text}"
            );
            let printed = crate::surface::printing::source_click_proposition(&raised);
            let file = parser::parse(&format!(
                "theorem probe() {{ requires {printed}; ensures true; }}"
            ))
            .unwrap();
            let Requirement::Proposition(parsed) = &file.theorem_definitions()[0].requires()[0]
            else {
                panic!()
            };
            assert_eq!(
                relower_written_proposition(parsed, &state).unwrap(),
                original,
                "{printed}"
            );
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn mixed_format_integer_comparisons_of_bitwise_values_round_trip() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new()
            .with_local(
                "z",
                format.value_from_term(OldMachineTerm::Variable(Variable(999710))),
            )
            .with_local(
                "y",
                format.value_from_term(OldMachineTerm::Variable(Variable(999709))),
            );
        for op in ["&", "|", "^"] {
            let text = format!("(z {op} (7 as {spelling})) < y");
            let file = parser::parse(&format!(
                "theorem probe() {{ requires {text}; ensures true; }}"
            ))
            .unwrap();
            let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0]
            else {
                panic!()
            };
            let native = relower_written_proposition(written, &state).unwrap();
            let Some((OldConditionTerm::Compare { left, right, .. }, true)) =
                native.old_condition()
            else {
                panic!("native bitwise comparison");
            };
            let left =
                crate::kernel::IntegerTerm::from_machine(format, left.as_ref().clone()).unwrap();
            // Same-format observations canonically use a native comparison.
            // A mixed-format observation pair must retain its Integer form.
            let other_format = if format.format().bits() == 32 {
                T::Int64
            } else {
                T::Int32
            };
            let right =
                crate::kernel::IntegerTerm::from_machine(other_format, right.as_ref().clone())
                    .unwrap();
            let state = state.clone().with_local(
                "y",
                other_format.value_from_term(OldMachineTerm::Variable(Variable(999709))),
            );
            for condition in [
                OldConditionTerm::integer_less_than(left.clone(), right.clone()),
                OldConditionTerm::integer_equal(left, right),
            ] {
                for truth in [true, false] {
                    let original = Proposition::condition_is(condition.clone(), truth);
                    let raised = synthesize_surface_proposition(
                        &original,
                        ParameterBinding::default(),
                        &state,
                    )
                    .unwrap();
                    assert_eq!(
                        relower_written_proposition(&raised, &state).unwrap(),
                        original,
                        "{text}: {raised:?}"
                    );
                    let printed = crate::surface::printing::source_click_proposition(&raised);
                    let file = parser::parse(&format!(
                        "theorem probe() {{ requires {printed}; ensures true; }}"
                    ))
                    .unwrap();
                    let Requirement::Proposition(parsed) =
                        &file.theorem_definitions()[0].requires()[0]
                    else {
                        panic!()
                    };
                    assert_eq!(
                        relower_written_proposition(parsed, &state).unwrap(),
                        original,
                        "{printed}"
                    );
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn closed_word32_equality_guards_with_selected_literal_arms_round_trip() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [(T::Int32, "int32"), (T::UInt32, "uint32")] {
        for guard in ["x == 9", "x != 9"] {
            for replacement in [9, 10] {
                for reverse in [false, true] {
                    check_conditional_round_trip(format, spelling, guard, reverse, replacement);
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.7s in the parallel gate"]
fn fixed_right_shifts_in_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling, max_count) in [
        (T::Int32, "int32", 31),
        (T::UInt32, "uint32", 31),
        (T::Int64, "int64", 63),
        (T::UInt64, "uint64", 63),
    ] {
        for count in [1, 7, max_count] {
            let equality = format!("x == (z >> {count})");
            for reverse in [false, true] {
                for guard in ["flag", "not flag"] {
                    check_conditional_round_trip_using_equality(
                        format, spelling, guard, reverse, &equality,
                    );
                }
                for guard in ["x < y", "x == y", "y <= x", "y != x"] {
                    check_conditional_round_trip_with_arm(
                        format, spelling, guard, reverse, &equality, "z",
                    );
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn fixed_unsigned_left_shifts_in_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling, max_count) in [(T::UInt32, "uint32", 31), (T::UInt64, "uint64", 63)] {
        for count in [1, 7, max_count] {
            let equality = format!("x == (z << {count})");
            for reverse in [false, true] {
                for guard in ["flag", "not flag"] {
                    check_conditional_round_trip_using_equality(
                        format, spelling, guard, reverse, &equality,
                    );
                }
                for guard in ["x < y", "x == y", "y <= x", "y != x"] {
                    check_conditional_round_trip_with_arm(
                        format, spelling, guard, reverse, &equality, "z",
                    );
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.4s in the parallel gate"]
fn variable_shift_counts_in_conditionals_round_trip_after_rewrite() {
    use MachineIntegerType as T;
    for (format, spelling, operator) in [
        (T::Int32, "int32", ">>"),
        (T::UInt32, "uint32", ">>"),
        (T::Int64, "int64", ">>"),
        (T::UInt64, "uint64", ">>"),
        (T::UInt32, "uint32", "<<"),
        (T::UInt64, "uint64", "<<"),
    ] {
        let mut fixture = ConditionalRoundTrip::new(format, spelling);
        fixture.state = fixture.state.with_local(
            "w",
            format.value_from_term(OldMachineTerm::Variable(Variable(999712))),
        );
        for count in ["w", "3"] {
            let equality = fixture.lower(&format!("x == (z {operator} {count})"));
            for reverse in [false, true] {
                for (guards, arm) in [
                    (&["flag", "not flag"][..], "x"),
                    (&["x < y", "x == y", "y <= x", "y != x"][..], "z"),
                ] {
                    for guard in guards {
                        let original = fixture.goal(guard, reverse, arm);
                        fixture.check(&original, &equality, guard, reverse);
                    }
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn signed_variable_arithmetic_in_conditionals_round_trips_after_rewrite() {
    use MachineIntegerType as T;
    for (format, spelling) in [(T::Int32, "int32"), (T::Int64, "int64")] {
        let mut fixture = ConditionalRoundTrip::new(format, spelling);
        fixture.state = fixture.state.with_local(
            "w",
            format.value_from_term(OldMachineTerm::Variable(Variable(999712))),
        );
        for operator in ["+", "-", "*", "&"] {
            let equality = fixture.lower(&format!("x == ((z {operator} w) as {spelling})"));
            for reverse in [false, true] {
                for (guards, arm) in [
                    (&["flag", "not flag"][..], "x"),
                    (&["x < y", "x == y", "y <= x", "y != x"][..], "z"),
                ] {
                    for guard in guards {
                        let original = fixture.goal(guard, reverse, arm);
                        fixture.check(&original, &equality, guard, reverse);
                    }
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.0s in the parallel gate"]
fn wrapping_add_subtract_in_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling, boundary) in [
        (T::UInt32, "uint32", u64::from(u32::MAX)),
        (T::UInt64, "uint64", u64::MAX),
    ] {
        for (op, value) in ["+", "-"]
            .into_iter()
            .flat_map(|op| [1, 7, boundary].map(|value| (op, value)))
        {
            let equality = format!("x == (z {op} ({value} as {spelling}))");
            for reverse in [false, true] {
                for guard in ["flag", "not flag"] {
                    check_conditional_round_trip_using_equality(
                        format, spelling, guard, reverse, &equality,
                    );
                }
                for guard in ["x < y", "x == y", "y <= x", "y != x"] {
                    check_conditional_round_trip_with_arm(
                        format, spelling, guard, reverse, &equality, "z",
                    );
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn two_variable_unsigned_arithmetic_in_conditionals_round_trips_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [(T::UInt32, "uint32"), (T::UInt64, "uint64")] {
        let mut fixture = ConditionalRoundTrip::new(format, spelling);
        fixture.state = fixture.state.clone().with_local(
            "w",
            format.value_from_term(OldMachineTerm::Variable(Variable(999712))),
        );
        for operator in ["+", "-", "*"] {
            let equality = fixture.lower(&format!("x == ((z {operator} w) as {spelling})"));
            for reverse in [false, true] {
                for (guards, then_value) in [
                    (&["flag", "not flag"][..], "x"),
                    (&["x < y", "x == y", "y <= x", "y != x"][..], "z"),
                ] {
                    for guard in guards {
                        let original = fixture.goal(guard, reverse, then_value);
                        fixture.check(&original, &equality, guard, reverse);
                    }
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn variable_divisors_in_conditionals_round_trip_after_rewrite() {
    use MachineIntegerType as T;
    for (format, spelling) in [(T::UInt32, "uint32"), (T::UInt64, "uint64")] {
        let mut fixture = ConditionalRoundTrip::new(format, spelling);
        fixture.state = fixture.state.with_local(
            "w",
            format.value_from_term(OldMachineTerm::Variable(Variable(999712))),
        );
        for operator in ["/", "%"] {
            let literal = format!("(3 as {spelling})");
            for divisor in ["w", literal.as_str()] {
                let equality = fixture.lower(&format!("x == (z {operator} {divisor})"));
                for reverse in [false, true] {
                    for (guards, arm) in [
                        (&["flag", "not flag"][..], "x"),
                        (&["x < y", "x == y", "y <= x", "y != x"][..], "z"),
                    ] {
                        for guard in guards {
                            let original = fixture.goal(guard, reverse, arm);
                            fixture.check(&original, &equality, guard, reverse);
                        }
                    }
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.9s in the parallel gate"]
fn literal_divisors_in_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling, boundary) in [
        (T::UInt32, "uint32", u64::from(u32::MAX)),
        (T::UInt64, "uint64", u64::MAX),
    ] {
        for (op, value) in ["/", "%"]
            .into_iter()
            .flat_map(|op| [3, 7, boundary].map(|value| (op, value)))
        {
            let equality = format!("x == (z {op} ({value} as {spelling}))");
            for reverse in [false, true] {
                for guard in ["flag", "not flag"] {
                    check_conditional_round_trip_using_equality(
                        format, spelling, guard, reverse, &equality,
                    );
                }
                for guard in ["x < y", "x == y", "y <= x", "y != x"] {
                    check_conditional_round_trip_with_arm(
                        format, spelling, guard, reverse, &equality, "z",
                    );
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.9s in the parallel gate"]
fn signed_literal_divisors_in_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling) in [(T::Int32, "int32"), (T::Int64, "int64")] {
        let fixture = ConditionalRoundTrip::new(format, spelling);
        for op in ["/", "%"] {
            for divisor in [3, 7, -3, -7] {
                let equality = fixture.lower(&format!("x == (z {op} (({divisor}) as {spelling}))"));
                for reverse in [false, true] {
                    for (guards, then_value) in [
                        (&["flag", "not flag"][..], "x"),
                        (&["x < y", "x == y", "y <= x", "y != x"][..], "z"),
                    ] {
                        for guard in guards {
                            let original = fixture.goal(guard, reverse, then_value);
                            fixture.check(&original, &equality, guard, reverse);
                        }
                    }
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3.0s in the parallel gate"]
fn wrapping_product_in_conditionals_round_trip_after_rewrite() {
    use crate::kernel::MachineIntegerType as T;
    for (format, spelling, boundary) in [
        (T::UInt32, "uint32", u64::from(u32::MAX)),
        (T::UInt64, "uint64", u64::MAX),
    ] {
        for value in [3, 7, boundary] {
            for product in [
                format!("z * ({value} as {spelling})"),
                format!("({value} as {spelling}) * z"),
            ] {
                let equality = format!("x == ({product})");
                for reverse in [false, true] {
                    for guard in ["flag", "not flag"] {
                        check_conditional_round_trip_using_equality(
                            format, spelling, guard, reverse, &equality,
                        );
                    }
                    for guard in ["x < y", "x == y", "y <= x", "y != x"] {
                        check_conditional_round_trip_with_arm(
                            format, spelling, guard, reverse, &equality, "z",
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn a_reflexive_pointer_equality_raises_as_contract_equality_that_lowers_back() {
    use crate::kernel::Pointer;
    let _session = crate::kernel::VerificationSession::enter();
    let node = Pointer::new(
        Address::symbolic(Variable(999977)),
        ProgramType::Int32Pointer,
    );
    let parameters = [crate::languages::interface::ImportedParameter::new(
        InterfaceType::Int32Pointer,
        "node".into(),
        None,
    )];
    let arguments = [ProgramExpression::Value(ProgramValue::Pointer(
        node.clone(),
    ))];
    let binding = ParameterBinding::new(&parameters, &arguments);
    let state = ExecutionState::new().with_local("node", ProgramValue::Pointer(node.clone()));
    // A fold of `fact p == identity` with both sides `node` owes this
    // pointer equality. It raises as contract `==`, not as the weaker
    // address-word equality, and lowering keeps its node.
    for (held, expected) in [(true, "node == node"), (false, "node != node")] {
        let equality = Proposition::condition_is(
            OldConditionTerm::AddressEqual(
                Box::new(node.address().clone()),
                Box::new(node.address().clone()),
            ),
            held,
        );
        let surface = synthesize_surface_proposition(&equality, binding, &state).unwrap();
        assert_eq!(
            crate::surface::printing::source_click_proposition(&surface),
            expected
        );
        assert_eq!(
            relower_written_proposition(&surface, &state).unwrap(),
            equality,
            "{expected}"
        );
    }
}

#[test]
fn call_capture_names_the_selected_result_at_its_declared_type() {
    use crate::kernel::{LocalBindingId, LocalFunctionId};
    use crate::languages::interface::ImportedFunction;

    let capture = LocalBindingId::temporary(LocalFunctionId::new(None, "f".into()), 0);
    capture.initialize_program_type(ProgramType::Int32);
    let capture = crate::kernel::BindingName::from(capture);
    let (call, result) = crate::kernel::program_call_value(0, "get", Vec::new());
    let function = ImportedFunction::external(InterfaceType::Int32, "f".into(), Vec::new())
        .with_prelowered_kernel_function(crate::kernel::program_function(
            ProgramType::Int32,
            "f",
            Vec::new(),
            crate::kernel::program_seq(call, crate::kernel::program_assign(&capture, result)),
        ));
    let layout = crate::surface::lowering::SourceExecutionLayout::for_function(&function).unwrap();
    let term = OldMachineTerm::Variable(Variable(977_921));
    let value = ProgramValue::Int32(term.clone());
    let state = ExecutionState::new().with_local(&capture, value.clone());
    let mut points = RecordedStates::new().with_source_layout(layout);
    let expected = SyntaxTerm::RegionResult(CodeRegionRef::Path(vec![SourcePathStep::Call(
        "get".into(),
        0,
    )]));

    let raise = |points: &RecordedStates, sought: &OldMachineTerm, state: &ExecutionState| {
        let _scope = SynthesisRecordedPointsScope::enter(points);
        synthesize_surface_bitvector(sought, ParameterBinding::default(), state, &BTreeMap::new())
    };
    let before = ProgramPointSelector::Mark("before".into());
    points.insert(before.clone(), ExecutionState::new());
    points.record_call_result(0, Some(value.clone()));
    assert_eq!(raise(&points, &term, &state), Some(expected.clone()));
    let saved = ProgramPointSelector::Mark("saved".into());
    points.insert(saved.clone(), state.clone());

    // The same static call runs again and its capture is assigned a new
    // symbolic value. The earlier value is still named at the proof mark.
    let newer = OldMachineTerm::Variable(Variable(977_922));
    let newer_value = ProgramValue::Int32(newer.clone());
    let current = state.clone().with_local(&capture, newer_value.clone());
    points.record_call_result(0, Some(newer_value.clone()));
    let historical = SyntaxTerm::At {
        selector: saved,
        expression: Box::new(expected.clone()),
    };
    assert_eq!(raise(&points, &newer, &current), Some(expected.clone()));
    assert_eq!(raise(&points, &term, &current), Some(historical.clone()));

    let lower = |expression| {
        crate::surface::lowering::elaborate_fixed_state_expression(
            expression,
            BTreeMap::new(),
            &current,
            ProgramValueBindings::new(),
            ProgramValueBindings::new(),
            None,
            &points,
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(&[]),
            ),
            BTreeSet::new(),
            BTreeMap::new(),
        )
    };
    assert_eq!(lower(&historical).unwrap(), SpecExpression::Value(value));
    assert_eq!(
        lower(&expected).unwrap(),
        SpecExpression::Value(newer_value)
    );
    let missing = SyntaxTerm::At {
        selector: before,
        expression: Box::new(expected.clone()),
    };
    assert!(lower(&missing).unwrap_err().contains("at `before`"));

    points.record_call_result(0, Some(ProgramValue::UInt32(term.clone())));
    assert_ne!(raise(&points, &term, &state), Some(expected));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn widening_casts_in_conditionals_round_trip_after_rewrite() {
    use MachineIntegerType as T;
    for (destination, spelling) in [(T::Int64, "int64"), (T::UInt64, "uint64")] {
        for source in [T::Int32, T::UInt32] {
            let mut fixture = ConditionalRoundTrip::new(destination, spelling);
            fixture.state = fixture.state.with_local(
                "w",
                source.value_from_term(OldMachineTerm::Variable(Variable(999712))),
            );
            let equality = fixture.lower(&format!("x == (w as {spelling})"));
            for reverse in [false, true] {
                for (guard, arm) in [
                    ("flag", "x"),
                    ("not flag", "x"),
                    ("x < y", "z"),
                    ("x == y", "z"),
                    ("y <= x", "z"),
                    ("y != x", "z"),
                ] {
                    fixture.check(
                        &fixture.goal(guard, reverse, arm),
                        &equality,
                        guard,
                        reverse,
                    );
                }
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn signedness_casts_in_conditionals_round_trip_after_rewrite() {
    use MachineIntegerType as T;
    for (source, destination, spelling) in [
        (T::UInt32, T::Int32, "int32"),
        (T::Int32, T::UInt32, "uint32"),
        (T::UInt64, T::Int64, "int64"),
        (T::Int64, T::UInt64, "uint64"),
    ] {
        let mut fixture = ConditionalRoundTrip::new(destination, spelling);
        fixture.state = fixture.state.with_local(
            "w",
            source.value_from_term(OldMachineTerm::Variable(Variable(999712))),
        );
        let equality = fixture.lower(&format!("x == (w as {spelling})"));
        for reverse in [false, true] {
            for (guard, arm) in [
                ("flag", "x"),
                ("not flag", "x"),
                ("x < y", "z"),
                ("x == y", "z"),
                ("y <= x", "z"),
                ("y != x", "z"),
            ] {
                fixture.check(
                    &fixture.goal(guard, reverse, arm),
                    &equality,
                    guard,
                    reverse,
                );
            }
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn low_word_casts_in_conditionals_round_trip_after_rewrite() {
    use MachineIntegerType as T;
    for (destination, spelling) in [(T::Int32, "int32"), (T::UInt32, "uint32")] {
        for source in [T::Int64, T::UInt64] {
            let mut fixture = ConditionalRoundTrip::new(destination, spelling);
            fixture.state = fixture.state.with_local(
                "w",
                source.value_from_term(OldMachineTerm::Variable(Variable(999712))),
            );
            let equality = fixture.lower(&format!("x == (w as {spelling})"));
            for reverse in [false, true] {
                for (guard, arm) in [
                    ("flag", "x"),
                    ("not flag", "x"),
                    ("x < y", "z"),
                    ("x == y", "z"),
                    ("y <= x", "z"),
                    ("y != x", "z"),
                ] {
                    fixture.check(
                        &fixture.goal(guard, reverse, arm),
                        &equality,
                        guard,
                        reverse,
                    );
                }
            }
        }
    }
}

#[test]
fn recorded_volatile_read_slots_retain_the_producer_value() {
    let _session = crate::kernel::VerificationSession::enter();
    let root = crate::kernel::KernelTerm::variable(
        crate::kernel::KernelType::Program(ProgramType::Float32),
        Variable(10993674),
    );
    let mut points = RecordedStates::new();
    points.record_read_retained_event_values(3, std::iter::once(root.clone().into()));
    assert_eq!(
        points.read_event_results.get(&(3, 0)).unwrap().root(),
        Some(&root)
    );
    let branch = points.clone();
    assert_eq!(
        branch.read_event_results.get(&(3, 0)).unwrap().root(),
        Some(&root)
    );
}

/// Lowering keeps a comparison of two identical or literal machine words,
/// `address(p) + 3u64 == address(p) + 3u64`, rather than deciding it;
/// checking decides it. A comparison its operands' type range decides,
/// `0u64 <= w`, keeps its established decision.
#[test]
fn identical_word_comparisons_keep_their_comparison_through_lowering() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = crate::kernel::Pointer::new(
        Address::symbolic(Variable(999_962)),
        ProgramType::Int32Pointer,
    );
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::Pointer(pointer))
        .with_local(
            "w",
            ProgramValue::UInt64(OldMachineTerm::Variable(Variable(999_961))),
        );
    let lower = |text: &str| {
        let file = parser::parse(&format!(
            "theorem probe() {{ requires {text}; ensures true; }}"
        ))
        .unwrap();
        let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
            panic!("requirement")
        };
        relower_written_proposition(written, &state).unwrap()
    };
    let Proposition::ConditionIs(condition, true) = lower("address(p) + 3u64 == address(p) + 3u64")
    else {
        panic!("a held comparison")
    };
    assert!(
        matches!(condition.old_form(), OldConditionTerm::Compare { .. }),
        "{condition:?}"
    );
    assert_eq!(condition.old_form().reflexive_value(), Some(true));
    let Proposition::ConditionIs(range, true) = lower("0u64 <= w") else {
        panic!("a held comparison")
    };
    assert!(
        matches!(range.old_form(), OldConditionTerm::Constant(true)),
        "{range:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn pure_machine_conditional_operands_round_trip_after_rewrite() {
    use MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        let mut fixture = ConditionalRoundTrip::new(format, spelling);
        fixture.state = fixture.state.with_local(
            "inner",
            ProgramValue::of_bool(OldConditionTerm::Variable(Variable(999712))),
        );
        for replacement in [
            "y",
            "if inner { y } else { z }",
            "if y < z { y } else { z }",
        ] {
            let equality = fixture.lower(&format!("x == ({replacement})"));
            for (guards, arm) in [
                (&["flag", "not flag"][..], "x"),
                (&["x < y", "y <= x", "x == y", "y != x"][..], "z"),
            ] {
                for guard in guards {
                    for reverse in [false, true] {
                        let original = fixture.goal(guard, reverse, arm);
                        fixture.check(&original, &equality, guard, reverse);
                    }
                }
            }
        }
    }
}

#[test]
fn exact_rewrite_keeps_equal_scalar_conditional_arms_through_lowering() {
    use crate::kernel::proof::PureFactStore;
    let fixture = ConditionalRoundTrip::new(MachineIntegerType::Int32, "int32");
    let equality = fixture.lower("to_integer(y) + 1 == to_integer(z) + 1");
    for written in [
        "to_integer(if flag { to_int32(to_integer(y) + 1) } else { to_int32(to_integer(z) + 1) }) + 1 <= 100",
        "(if flag { if to_integer(y) + 1 < 0 { true } else { false } } else { if to_integer(z) + 1 < 0 { true } else { false } }) == true",
    ] {
        let original = fixture.lower(written);
        let proof = PureFactStore::from_ordered(std::slice::from_ref(&equality))
            .check_equality_rewrite(&original, &equality)
            .unwrap();
        let expected = proof.proposition();
        assert_ne!(expected, &original);
        let raised =
            synthesize_surface_proposition(expected, ParameterBinding::default(), &fixture.state)
                .unwrap();
        let text = crate::surface::printing::source_click_proposition(&raised);
        assert!(text.contains("if flag"), "{text}");
        assert_eq!(
            relower_written_proposition(&raised, &fixture.state).unwrap(),
            *expected,
            "{text}"
        );
        assert_eq!(fixture.lower(&text), *expected, "{text}");
    }
}

#[test]
fn comparisons_of_conditionals_with_integer_conversions_round_trip_after_rewrite() {
    use MachineIntegerType as T;
    for (format, spelling) in [
        (T::Int32, "int32"),
        (T::UInt32, "uint32"),
        (T::Int64, "int64"),
        (T::UInt64, "uint64"),
    ] {
        let fixture = ConditionalRoundTrip::new(format, spelling);
        let equality = fixture.lower("to_integer(y) + 1 == to_integer(z) + 1");
        let conditional = format!(
            "to_integer(if flag {{ to_{spelling}(to_integer(y) + 1) }} else {{ to_{spelling}(to_integer(z) + 1) }})"
        );
        let mut comparisons = vec![(format!("{conditional} <= 100"), false)];
        if format == T::Int32 {
            comparisons.push((format!("100 < {conditional}"), true));
            comparisons.push((format!("{conditional} == to_integer(x)"), false));
            comparisons.push((
                format!("{conditional} == to_integer(to_int32(to_integer(x) + 1))"),
                false,
            ));
        }
        if format == T::UInt64 {
            comparisons.push((format!("{conditional} == 18446744073709551615"), false));
        }
        for (written, reverse) in comparisons {
            let original = fixture.lower(&written);
            assert!(
                matches!(
                    original.old_condition(),
                    Some((OldConditionTerm::Compare { .. }, true))
                ),
                "{written}: {original:?}"
            );
            fixture.check(&original, &equality, "flag", reverse);
        }
    }
}

#[test]
fn reflexive_boolean_comparisons_round_trip_after_exact_rewrite() {
    use crate::kernel::proof::PureFactStore;
    let fixture = ConditionalRoundTrip::new(MachineIntegerType::Int32, "int32");
    let equality = fixture.lower("to_integer(y) + 1 == to_integer(z) + 1");
    let facts = PureFactStore::from_ordered(std::slice::from_ref(&equality));
    let left = "(if to_integer(y) + 1 < 0 { true } else { false })";
    let right = "(if to_integer(z) + 1 < 0 { true } else { false })";
    for (operator, truth) in [("==", true), ("!=", false)] {
        let original = fixture.lower(&format!("{left} {operator} {right}"));
        let proof = facts.check_equality_rewrite(&original, &equality).unwrap();
        let expected = proof.proposition();
        let Some((condition @ OldConditionTerm::BoolEqual(left, right), polarity)) =
            expected.old_condition()
        else {
            panic!("expected a Boolean comparison, got {expected:?}");
        };
        assert_eq!(left, right);
        assert_eq!(*polarity, truth);
        assert_eq!(PureFactContext::new().decide(condition), Some(true));
        let direct = fixture.lower(&format!("flag {operator} flag"));
        assert!(matches!(
            direct.old_condition(),
            Some((OldConditionTerm::BoolEqual(left, right), polarity))
                if left == right && *polarity == truth
        ));
        let raised =
            synthesize_surface_proposition(expected, ParameterBinding::default(), &fixture.state)
                .unwrap();
        let text = crate::surface::printing::source_click_proposition(&raised);
        assert_eq!(
            relower_written_proposition(&raised, &fixture.state).unwrap(),
            *expected,
            "{text}"
        );
        assert_eq!(fixture.lower(&text), *expected, "{text}");
    }
}

#[test]
fn literal_float_comparisons_preserve_ieee_truth_and_round_trip() {
    use crate::kernel::{ComparisonOperator as C, KernelFloatType as F};
    let fixture = ConditionalRoundTrip::new(MachineIntegerType::Int32, "int32");
    for (format, width, negative_zero, nan, negative_one, one) in [
        (
            F::Float32,
            32,
            0x80000000,
            0x7fc00123,
            0xbf800000,
            0x3f800000,
        ),
        (
            F::Float64,
            64,
            0x8000000000000000,
            0x7ff8000000000123,
            0xbff0000000000000,
            0x3ff0000000000000,
        ),
    ] {
        let literal = |bits: u64| format!("float{width}_from_bits(0x{bits:x}u{width})");
        for (left, operator, right, token, truth) in [
            (negative_zero, C::Equal, 0, "==", true),
            (nan, C::Equal, nan, "==", false),
            (nan, C::NotEqual, nan, "!=", true),
            (nan, C::LessEqual, one, "<=", false),
            (negative_one, C::LessThan, one, "<", true),
            (one, C::GreaterThan, 0, ">", true),
            (negative_zero, C::GreaterEqual, 0, ">=", true),
        ] {
            let written = format!("{} {token} {}", literal(left), literal(right));
            let Proposition::ConditionIs(condition, true) = fixture.lower(&written) else {
                panic!("expected a comparison: {written}");
            };
            let (actual_format, actual_operator, operands) =
                condition.operand_view().float_comparison().expect(&written);
            assert_eq!(actual_format, format, "{written}");
            assert_eq!(actual_operator, operator, "{written}");
            assert_eq!(
                operands.map(|operand| operand.literal_bits()),
                [Some(left), Some(right)],
                "{written}"
            );
            assert_eq!(
                PureFactContext::new().decide(condition.old_form()),
                Some(truth),
                "{written}"
            );
            for polarity in [true, false] {
                let expected = Proposition::condition_is(condition.clone(), polarity);
                let raised = synthesize_surface_proposition(
                    &expected,
                    ParameterBinding::default(),
                    &fixture.state,
                )
                .unwrap();
                let text = crate::surface::printing::source_click_proposition(&raised);
                assert_eq!(
                    relower_written_proposition(&raised, &fixture.state).unwrap(),
                    expected,
                    "{text}"
                );
                assert_eq!(fixture.lower(&text), expected, "{text}");
            }
        }
    }
}

#[test]
fn integer_match_on_written_constructor_round_trips() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new();
    let declarations = "spec enum Choice { Empty, Full(Integer) }";
    let written = "(match Choice::Full(7) { Choice::Empty => 0, Choice::Full(n) => n + 1 }) == 8";
    let parse = |text: &str| {
        parser::parse(&format!(
            "{declarations} theorem probe() {{ requires {text}; ensures true; }}"
        ))
        .unwrap()
    };
    let file = parse(written);
    let functions = ClickFunctionEnvironment::with_algebraic_types(
        file.click_function_definitions(),
        file.algebraic_type_definitions(),
    );
    let lower = |proposition: &SyntaxProposition| {
        crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
            proposition,
            &PureFactContext::new(),
            ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            SpecDefinitions::new(&PredicateEnvironment::new(&[]), &functions),
            FixedStateLoweringOptions::default(),
        )
        .unwrap()
        .0
    };
    let Requirement::Proposition(proposition) = &file.theorem_definitions()[0].requires()[0] else {
        panic!("expected a proposition");
    };
    let original = lower(proposition);
    assert!(matches!(
        original.old_condition(),
        Some((OldConditionTerm::IntegerEqual(left, _), true))
            if matches!(left.as_ref(), crate::kernel::IntegerTerm::AlgebraicMatch { .. })
    ));
    let raised =
        synthesize_surface_proposition(&original, ParameterBinding::default(), &state).unwrap();
    let text = crate::surface::printing::source_click_proposition(&raised);
    assert!(text.contains("match Choice::Full"), "{text}");
    assert!(
        crate::kernel::proof::propositions_are_alpha_equal(&lower(&raised), &original),
        "{text}"
    );
    let reparsed = parse(&text);
    let Requirement::Proposition(proposition) = &reparsed.theorem_definitions()[0].requires()[0]
    else {
        panic!("expected a proposition: {text}");
    };
    assert!(
        crate::kernel::proof::propositions_are_alpha_equal(&lower(proposition), &original),
        "{text}"
    );
}

#[test]
fn literal_integer_conversions_round_trip_after_exact_rewrite() {
    use crate::kernel::proof::PureFactStore;
    let fixture = ConditionalRoundTrip::new(MachineIntegerType::Int32, "int32");
    for (conversion, literal, incremented) in [
        ("to_int32", "7", "8"),
        ("to_uint32", "4294967295", "4294967296"),
        ("to_uint64", "18446744073709551615", "18446744073709551616"),
    ] {
        let input = "to_integer(y) + 1";
        let equality = fixture.lower(&format!("{input} == {literal}"));
        let original = fixture.lower(&format!(
            "to_integer({conversion}({input})) + 1 == {incremented}"
        ));
        let proof = PureFactStore::from_ordered(std::slice::from_ref(&equality))
            .check_equality_rewrite(&original, &equality)
            .unwrap();
        let expected = proof.proposition();
        let written = format!("to_integer({conversion}({literal})) + 1 == {incremented}");
        assert_eq!(fixture.lower(&written), *expected, "{written}");
        assert!(
            crate::kernel::proof::fact_reasoning::computes_leaf(expected),
            "{written}"
        );
        let raised =
            synthesize_surface_proposition(expected, ParameterBinding::default(), &fixture.state)
                .unwrap();
        let text = crate::surface::printing::source_click_proposition(&raised);
        assert!(text.contains(conversion), "{text}");
        assert_eq!(
            relower_written_proposition(&raised, &fixture.state).unwrap(),
            *expected,
            "{text}"
        );
        assert_eq!(fixture.lower(&text), *expected, "{text}");
    }
}

#[test]
fn an_abstract_local_read_raises_at_its_defining_point() {
    use crate::kernel::{
        AggregateDeclarationKind, AggregateLayout, AlgebraicTerm, AlgebraicTermNode,
        KernelTermImport, TypeParameterName,
    };
    let _session = crate::kernel::VerificationSession::enter();
    let ty = TypeParameterName::intern("AbstractLocalRaise");
    let declare = crate::kernel::prove_execution_statement_execution(
        ExecutionState::new(),
        crate::kernel::ProgramStatement::DeclareAggregate {
            name: "item".into(),
            layout: AggregateLayout::holding_value(ProgramType::Parameter(ty)),
            kind: AggregateDeclarationKind::Local,
            declared_class: None,
        },
    )
    .unwrap();
    let Proposition::ProgramStatementVerifies {
        outcome: crate::kernel::StatementOutcome::Normal(state),
        ..
    } = declare.proposition()
    else {
        panic!("declared local object");
    };
    let (_, pointer) = state.locals().held_value_local("item").unwrap();
    let store = |state: &ExecutionState, variable| {
        state.clone().with_memory(state.memory().clone().store(
            pointer.clone(),
            ProgramValue::Parameter(Box::new(AlgebraicTerm {
                algebraic_type: ty.algebraic_type(),
                node: AlgebraicTermNode::Variable(Variable(variable)),
            })),
        ))
    };
    let earlier = store(state, 1008301);
    let current = store(&earlier, 1008302);
    let ProgramValue::Parameter(value) = earlier.held_local_value("item").unwrap() else {
        panic!("abstract local");
    };
    let root = KernelTermImport::default().algebraic(&value);
    let raise = |state: &ExecutionState| {
        raise_kernel_term(&root, ParameterBinding::default(), state, &BTreeMap::new())
    };
    let variable = SyntaxTerm::ProgramExpression(ProgramExpression::Variable("item".into()));
    assert_eq!(raise(&earlier), Some(variable.clone()));
    assert_eq!(raise(&current), None);

    let selector = ProgramPointSelector::Mark("before_write".into());
    let mut points = RecordedStates::new();
    points.insert(selector.clone(), earlier);
    let _points = SynthesisRecordedPointsScope::enter(&points);
    assert_eq!(
        raise(&current),
        Some(SyntaxTerm::At {
            selector,
            expression: Box::new(variable)
        })
    );
}

#[test]
fn declared_predicate_array_raises_and_lowers_its_entry_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let entry = ExecutionState::new()
        .with_local(
            "p",
            ProgramValue::typed_pointer(address.clone(), ProgramType::Int32Pointer),
        )
        .begin_function_entry_memory();
    let post = entry.clone().with_memory(entry.memory().clone().store(
        address.clone(),
        ProgramValue::Int32(OldMachineTerm::constant(9)),
    ));
    let entry_view = entry.clone().with_materialized_memory_at_current_point(
        entry.memory().clone().materialize_cell_at(
            address,
            ProgramType::Int32,
            &entry.program_point(),
        ),
    );
    assert_eq!(
        entry_view.observation_point_id(),
        entry.observation_point_id()
    );
    assert_ne!(
        entry_view.program_point().shared_memory().arena_id(),
        entry.program_point().shared_memory().arena_id()
    );
    let file = crate::surface::parse(
        "predicate first_is(p: int32[], value: int32) { p[0] == value }
         theorem probe(p: int32*) { requires first_is(old(p), 7); ensures true; }",
    )
    .unwrap();
    let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
        panic!("predicate premise");
    };
    let points = RecordedStates::new();
    let predicates = PredicateEnvironment::new(file.predicate_definitions());
    let functions = ClickFunctionEnvironment::new(&[]);
    let lower = |surface: &SyntaxProposition, entry: &ExecutionState| {
        crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
            surface,
            &PureFactContext::new(),
            ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
            FixedStateFrame::new(entry, &post, None, &points),
            SpecDefinitions::new(&predicates, &functions),
            FixedStateLoweringOptions::default(),
        )
        .map(|(proposition, _, _, _)| proposition)
    };
    let original = lower(written, &entry).unwrap();
    let Proposition::Predicate { arguments, .. } = &original else {
        panic!("declared predicate");
    };
    assert!(matches!(
        arguments.get(1),
        Some(Term::ArrayReadPoint(point))
            if point.read_version_id() == entry.observation_point_id()
    ));
    let raised = synthesize_surface_proposition_at_entry_and_post(
        &original,
        ParameterBinding::default(),
        &entry_view,
        &post,
    )
    .expect("the indexed array argument has a spelling");
    assert!(
        matches!(&raised, SyntaxProposition::PredicateCall { arguments, .. }
        if matches!(arguments.first(), Some(SyntaxTerm::Old(_))))
    );
    assert_eq!(lower(&raised, &entry_view), Ok(original));
}

#[test]
fn declared_predicate_array_raises_at_its_write_point() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let entry = ExecutionState::new()
        .with_local(
            "p",
            ProgramValue::typed_pointer(address.clone(), ProgramType::Int32Pointer),
        )
        .begin_function_entry_memory();
    let write = |state: &ExecutionState| {
        state.clone().with_memory(state.memory().clone().store(
            address.clone(),
            ProgramValue::Int32(OldMachineTerm::constant(7)),
        ))
    };
    let first = write(&entry);
    let second = write(&first);
    assert_eq!(first.memory(), second.memory());

    let file = crate::surface::parse(
        "predicate first_is(p: int32[], value: int32) { p[0] == value }
         theorem probe(p: int32*) { requires first_is(p, 7); ensures true; }",
    )
    .unwrap();
    let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
        panic!("predicate premise");
    };
    let selector = ProgramPointSelector::Mark("first".into());
    let mut points = RecordedStates::new();
    points.insert(selector.clone(), first.clone());
    let predicates = PredicateEnvironment::new(file.predicate_definitions());
    let functions = ClickFunctionEnvironment::new(&[]);
    let lower = |surface: &SyntaxProposition, current: &ExecutionState| {
        crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
            surface,
            &PureFactContext::new(),
            ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
            FixedStateFrame::new(&entry, current, None, &points),
            SpecDefinitions::new(&predicates, &functions),
            FixedStateLoweringOptions::default(),
        )
        .map(|(proposition, _, _, _)| proposition)
    };
    let original = lower(written, &first).unwrap();
    let Proposition::Predicate { arguments, .. } = &original else {
        panic!("declared predicate");
    };
    assert!(matches!(
        arguments.get(1),
        Some(Term::ArrayReadPoint(point))
            if point.read_version_id() == first.observation_point_id()
    ));
    assert_ne!(lower(written, &second).unwrap(), original);

    let _points = SynthesisRecordedPointsScope::enter(&points);
    let raised = synthesize_surface_proposition(&original, ParameterBinding::default(), &second)
        .expect("the array reference retains its write point");
    assert!(
        matches!(&raised, SyntaxProposition::PredicateCall { arguments, .. }
        if matches!(arguments.first(), Some(SyntaxTerm::At { selector: at, .. }) if at == &selector))
    );
    assert_eq!(lower(&raised, &second), Ok(original));
}

#[test]
fn fixed_width_opaque_field_observation_round_trips_its_store_point() {
    use crate::kernel::{AlgebraicTerm, AlgebraicTermNode, ExpressionOutcome, TypeParameterName};

    let _session = crate::kernel::VerificationSession::enter();
    let parameter = TypeParameterName::of(&crate::surface::generics::primitive_instance_type(
        "Vec",
        &[crate::kernel::AlgebraicValueType::Program(
            ProgramType::UInt32,
        )],
    ));
    let ty = ProgramType::Parameter(parameter);
    let block = local_read_test_address("record");
    let field = block.offset_by_bytes(8);
    let pointer =
        ProgramValue::typed_pointer(field.clone(), ProgramType::ParameterPointer(parameter));
    let parameters = [crate::languages::interface::ImportedParameter::new(
        InterfaceType::ParameterPointer(parameter),
        "p".into(),
        None,
    )];
    let arguments = [ProgramExpression::Value(pointer.clone())];
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block(block.base.clone(), 16))
        .with_local("p", pointer);
    let opaque = |parameter: TypeParameterName, id| {
        ProgramValue::Parameter(Box::new(AlgebraicTerm {
            algebraic_type: parameter.algebraic_type(),
            node: AlgebraicTermNode::Variable(Variable(id)),
        }))
    };
    let store = |state: &ExecutionState, address: &Address, value| {
        state
            .clone()
            .with_memory(state.memory().clone().store(address.clone(), value))
    };
    let first = store(&state, &field, opaque(parameter, 1008403));
    let observe = |state: &ExecutionState| {
        let memory =
            SymbolicMemory::new().materialize_cell_at(field.clone(), ty, &state.program_point());
        let ExpressionOutcome::Value(ProgramValue::Parameter(term)) = memory.load(&field) else {
            panic!("expected a named opaque resource cell");
        };
        term
    };
    let first_read = observe(&first);
    assert!(
        matches!(&first_read.node, AlgebraicTermNode::MemoryLoad { point, .. }
        if point.read_version_id() == first.program_point_id())
    );

    let mut current = first.clone();
    let mut samples = Vec::new();
    for count in [4, 16, 64, 256] {
        for value in 0..count {
            current = local_read_test_store(&current, &block, ProgramType::Int32, value);
        }
        let ((version, read), work) = crate::instrumentation::measure_deterministic_work(|| {
            (
                current.program_point().ordinary_typed_version(&field, ty),
                observe(&current),
            )
        });
        assert_eq!(
            version.and_then(|point| point.read_version_id()),
            first.program_point_id()
        );
        assert_eq!(read, first_read);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|&work| work <= samples[0] + 8),
        "{samples:?}"
    );

    let second = store(&current, &field, opaque(parameter, 1008404));
    let second_read = observe(&second);
    assert!(
        matches!(&second_read.node, AlgebraicTermNode::MemoryLoad { point, .. }
        if point.read_version_id() == second.program_point_id())
    );
    assert_ne!(first_read, second_read);

    let goal = Proposition::Equal(
        Term::Algebraic((*first_read).into()),
        Term::Algebraic((*second_read).into()),
    );
    let selector = ProgramPointSelector::Mark("before".into());
    let mut points = RecordedStates::new();
    points.insert(selector.clone(), first);
    let _points = SynthesisRecordedPointsScope::enter(&points);
    let raised = synthesize_surface_proposition(
        &goal,
        ParameterBinding::new(&parameters, &arguments),
        &second,
    )
    .expect("the indexed field reads have a Click spelling");
    assert!(matches!(&raised, SyntaxProposition::Comparison { left, .. }
        if matches!(left, SyntaxTerm::At { selector: point, .. } if *point == selector)));
    assert_eq!(
        relower_written_proposition_with_states(&raised, &state, &second, &points),
        Ok(goal),
    );

    let generic = TypeParameterName::intern("UnknownOpaqueField");
    assert!(generic.has_abstract_size());
    let unknown_overlap = store(&second, &block, opaque(generic, 1008405));
    assert!(
        unknown_overlap
            .program_point()
            .ordinary_typed_version(&field, ty)
            .is_none()
    );
}

#[test]
fn generic_parameter_cell_raises_and_lowers_its_entry_version() {
    use crate::kernel::{AlgebraicTermNode, TypeParameterName};

    let _session = crate::kernel::VerificationSession::enter();
    let ty = TypeParameterName::intern("GenericEntryRead");
    let address = |id| {
        Address::new(
            AddressBase::ExternalArgument,
            AddressOffset::variable(Variable(id)),
        )
    };
    let left = address(1008401);
    let right = address(1008402);
    let argument =
        |address| ProgramValue::typed_pointer(address, ProgramType::ParameterPointer(ty));
    let parameters = ["p", "q"].map(|name| {
        crate::languages::interface::ImportedParameter::new(
            InterfaceType::ParameterPointer(ty),
            name.into(),
            None,
        )
    });
    let arguments =
        [left.clone(), right.clone()].map(|address| ProgramExpression::Value(argument(address)));
    let entry = ExecutionState::new()
        .with_local("p", argument(left.clone()))
        .with_local("q", argument(right))
        .begin_function_entry_memory();
    let post = entry.clone().with_memory(
        entry
            .memory()
            .clone()
            .store(left, ProgramValue::Int32(OldMachineTerm::constant(9))),
    );
    let file = crate::surface::parse(
        "theorem probe<GenericEntryRead>(p: GenericEntryRead*, q: GenericEntryRead*) {
             requires old(*p) == old(*q);
             ensures true;
         }",
    )
    .unwrap();
    let Requirement::Proposition(written) = &file.theorem_definitions()[0].requires()[0] else {
        panic!("generic read premise");
    };
    let points = RecordedStates::new();
    let predicates = PredicateEnvironment::new(&[]);
    let functions = ClickFunctionEnvironment::new(&[]);
    let lower = |surface: &SyntaxProposition| {
        crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
            surface,
            &PureFactContext::new(),
            ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
            FixedStateFrame::new(&entry, &post, None, &points),
            SpecDefinitions::new(&predicates, &functions),
            FixedStateLoweringOptions::default(),
        )
        .map(|(proposition, _, _, _)| proposition)
    };
    let original = lower(written).unwrap();
    let Some((OldConditionTerm::AlgebraicEqual(left, right), true)) = original.old_condition()
    else {
        panic!("generic value equality: {original:?}");
    };
    for term in [left, right] {
        assert!(matches!(
            &term.node,
            AlgebraicTermNode::MemoryLoad { point, .. }
                if point.read_version_id() == entry.observation_point_id()
        ));
    }
    let raised = synthesize_surface_proposition_at_entry_and_post(
        &original,
        ParameterBinding::new(&parameters, &arguments),
        &entry,
        &post,
    )
    .expect("the generic entry read has a spelling");
    assert_eq!(lower(&raised), Ok(original));
}

/// A definedness fact about one operation whose operand is itself an
/// operation raises to Surface text that lowers back to that same fact.
/// `defined(...)` claims its root operation's domain with its operands taken
/// as values, so `defined((a + b) + c)` is the outer addition's domain alone,
/// as the kernel files it, and not also the inner addition's.
#[test]
fn nested_operand_definedness_round_trips() {
    let format = MachineIntegerType::Int32;
    let a = OldMachineTerm::Variable(Variable(973_001));
    let b = OldMachineTerm::Variable(Variable(973_002));
    let c = OldMachineTerm::Variable(Variable(973_003));
    let state = ExecutionState::new()
        .with_local("a", ProgramValue::Int32(a.clone()))
        .with_local("b", ProgramValue::Int32(b.clone()))
        .with_local("c", ProgramValue::Int32(c.clone()));
    let inner = OldMachineTerm::machine_binary(format, MachineBinaryOp::Add, a, b);
    let range = Proposition::signed_arithmetic_domain(format, MachineBinaryOp::Add, &inner, &c);
    let flat_atom = Proposition::condition_is(
        OldConditionTerm::Overflows {
            format,
            op: OverflowOperation::Add,
            left: Box::new(OldMachineTerm::Variable(Variable(973_001))),
            right: Box::new(OldMachineTerm::Variable(Variable(973_002))),
        },
        false,
    );
    let atom = Proposition::condition_is(
        OldConditionTerm::Overflows {
            format,
            op: OverflowOperation::Add,
            left: Box::new(inner),
            right: Box::new(c),
        },
        false,
    );
    // Shallow `defined((a + b) + c)` claims the outer addition's domain
    // alone: the same kernel fact as evaluating that addition owes.
    let spelled = |atom: &Proposition| match synthesize_surface_proposition(
        atom,
        ParameterBinding::default(),
        &state,
    ) {
        Some(SyntaxProposition::Defined { expression }) => expression,
        other => panic!("an overflow atom raises as `defined`: {other:?}"),
    };
    let ab = spelled(&flat_atom);
    let ac = spelled(&Proposition::condition_is(
        OldConditionTerm::Overflows {
            format,
            op: OverflowOperation::Add,
            left: Box::new(OldMachineTerm::Variable(Variable(973_001))),
            right: Box::new(OldMachineTerm::Variable(Variable(973_003))),
        },
        false,
    ));
    let SyntaxTerm::Add(_, c_term) = &ac else {
        panic!("`a + c`: {ac:?}");
    };
    let nested = SyntaxProposition::Defined {
        expression: SyntaxTerm::Add(Box::new(ab), c_term.clone()),
    };
    assert_eq!(
        relower_written_proposition(&nested, &state).as_ref(),
        Ok(&range),
        "shallow `defined(a + b + c)` is the outer addition's domain"
    );
    // Each fact raises to Surface text that lowers to the domain the kernel
    // files for its operation. The overflow atom is the search's private
    // query for that domain; its spelling lowers to the filed range form.
    let flat_range = Proposition::signed_arithmetic_domain(
        format,
        MachineBinaryOp::Add,
        &OldMachineTerm::Variable(Variable(973_001)),
        &OldMachineTerm::Variable(Variable(973_002)),
    );
    let mut failures = Vec::new();
    for (name, fact, expected) in [
        ("range", range.clone(), range.clone()),
        ("overflow atom", atom, range),
        ("flat atom", flat_atom, flat_range),
    ] {
        for (polarity, fact, expected) in [
            ("", fact.clone(), expected.clone()),
            (
                "not ",
                Proposition::Not(Box::new(fact)),
                Proposition::Not(Box::new(expected)),
            ),
        ] {
            let Some(raised) =
                synthesize_surface_proposition(&fact, ParameterBinding::default(), &state)
            else {
                failures.push(format!("{polarity}{name}: no spelling"));
                continue;
            };
            let lowered = relower_written_proposition(&raised, &state);
            if lowered.as_ref() != Ok(&expected) {
                failures.push(format!(
                    "{polarity}{name}:\n  raised:   {}\n  lowered:  {lowered:?}\n  expected: {expected:?}",
                    crate::surface::printing::source_click_proposition(&raised),
                ));
            }
            // The printed spelling is what a user or an expansion writes:
            // parsed back as a requirement, it lowers to the same fact.
            let printed = crate::surface::printing::source_click_proposition(&raised);
            let reparsed = match parser::parse(&format!(
                "void probe(int32 a, int32 b, int32 c) {{ requires {printed}; ensures true; }}"
            )) {
                Ok(file) => match file.function_blocks()[0].requires()[0].clone() {
                    Requirement::Proposition(proposition) => proposition,
                    other => panic!("`{printed}` parses as a proposition: {other:?}"),
                },
                Err(error) => {
                    failures.push(format!(
                        "{polarity}{name}: `{printed}` does not parse: {error}"
                    ));
                    continue;
                }
            };
            let relowered = relower_written_proposition(&reparsed, &state);
            if relowered.as_ref() != Ok(&expected) {
                failures.push(format!(
                    "{polarity}{name}:\n  printed:  {printed}\n  lowered:  {relowered:?}\n  expected: {expected:?}",
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn retained_integer_comparison_raises_without_native_output() {
    use crate::kernel::{KernelTermExport, KernelTermNode};
    let fixture = ConditionalRoundTrip::new(MachineIntegerType::Int32, "int32");
    for operator in ["==", "!=", "<", "<=", ">", ">="] {
        let expected = fixture.lower(&format!("to_integer(x) + 1 {operator} to_integer(y)"));
        let Proposition::ConditionIs(condition, _) = &expected else {
            panic!("expected a retained comparison: {operator}");
        };
        let root = condition.root().unwrap();
        assert!(matches!(root.node(), KernelTermNode::IntegerCompare { .. }));
        assert!(!root.has_cached_native_argument());
        let exports = KernelTermExport::integer_export_count();
        let surface =
            synthesize_surface_proposition(&expected, ParameterBinding::default(), &fixture.state)
                .unwrap();
        assert_eq!(KernelTermExport::integer_export_count(), exports);
        assert!(!root.has_cached_native_argument());
        let text = crate::surface::printing::source_click_proposition(&surface);
        assert_eq!(
            relower_written_proposition(&surface, &fixture.state).unwrap(),
            expected,
            "{text}"
        );
        assert_eq!(fixture.lower(&text), expected, "{text}");
    }
}

#[test]
fn guarded_algebraic_matches_on_written_constructors_round_trip() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new();
    let written = "(match Input::Hold(true, 7) { Input::Hold(flag, n) =>
        if flag { Box::Value(n) } else { Box::Value(0) } })
        == (match Input::Hold(false, 8) { Input::Hold(flag, n) =>
        if flag { Box::Value(0) } else { Box::Value(n - 1) } })";
    let parse = |text: &str| {
        parser::parse(&format!(
            "spec enum Input {{ Hold(Bool, Integer) }} spec enum Box {{ Value(Integer) }}
             theorem probe() {{ requires {text}; ensures true; }}"
        ))
        .unwrap()
    };
    let file = parse(written);
    let functions = ClickFunctionEnvironment::with_algebraic_types(
        file.click_function_definitions(),
        file.algebraic_type_definitions(),
    );
    let lower = |proposition: &SyntaxProposition| {
        crate::surface::proof::fixed_state_proofs::lower_fixed_state_proposition_retaining_requirements(
            proposition,
            &PureFactContext::new(),
            ContractEnvironment::new(&ProgramValueBindings::new(), &BTreeMap::new()),
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            SpecDefinitions::new(&PredicateEnvironment::new(&[]), &functions),
            FixedStateLoweringOptions::default(),
        )
        .unwrap()
        .0
    };
    let lower_written = |file: &crate::surface::ClickFile| {
        let Requirement::Proposition(proposition) = &file.theorem_definitions()[0].requires()[0]
        else {
            panic!("expected a proposition");
        };
        lower(proposition)
    };
    let expected = lower_written(&file);
    let Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) = &expected else {
        panic!("expected two algebraic operands");
    };
    for operand in [left, right] {
        assert!(matches!(
            operand.root().unwrap().node(),
            crate::kernel::KernelTermNode::Match(_)
        ));
    }
    let surface =
        synthesize_surface_proposition(&expected, ParameterBinding::default(), &state).unwrap();
    let text = crate::surface::printing::source_click_proposition(&surface);
    for actual in [lower(&surface), lower_written(&parse(&text))] {
        assert!(
            crate::kernel::proof::propositions_are_alpha_equal(&expected, &actual),
            "{text}\nlowered: {actual:?}"
        );
    }
}

/// A slice application's count raises as `f(x).len()` of the application
/// that names it (`design/rust-slice-values.md`, step 2b-iii-c-ii), never
/// as an integer application of the same name or any placeholder; the
/// slice itself raises as the application.
#[test]
fn a_slice_application_and_its_count_raise_from_the_application() {
    let _session = crate::kernel::VerificationSession::enter();
    let application = crate::kernel::SharedPureApplication::intern(
        "bytes_of".into(),
        vec![crate::kernel::PureFunctionArgument::Value(
            ProgramValue::Int32(OldMachineTerm::constant(3)),
        )],
    );
    let count = synthesize_surface_bitvector(
        &OldMachineTerm::pure_application_count(application.clone()),
        ParameterBinding::default(),
        &ExecutionState::new(),
        &BTreeMap::new(),
    );
    let Some(SyntaxTerm::Call { name, arguments }) = count else {
        panic!("a slice application's count raises as a call: {count:?}");
    };
    assert_eq!(name, crate::surface::RUST_SLICE_LEN);
    let [SyntaxTerm::Call { name: slice, .. }] = arguments.as_slice() else {
        panic!("`len` reads the application: {arguments:?}");
    };
    assert_eq!(slice, "bytes_of");
    let value = crate::kernel::pure_slice_application_value(
        &application,
        crate::kernel::SliceElement::UInt8,
        ProgramType::SlicePointer(crate::kernel::SliceElement::UInt8),
    );
    let raised = slices::raise_slice(
        &value,
        ParameterBinding::default(),
        &ExecutionState::new(),
        &BTreeMap::new(),
    );
    assert!(
        matches!(&raised, Some(SyntaxTerm::Call { name, .. }) if name == "bytes_of"),
        "{raised:?}"
    );
}

/// A slice no one value names raises as its construction,
/// `slice::from_raw_parts(p, n)`, of its spelled components.
#[test]
fn an_unnamed_slice_raises_as_its_construction() {
    let _session = crate::kernel::VerificationSession::enter();
    let ProgramValue::Pointer(data) =
        ProgramValue::typed_pointer(crate::kernel::Address::null(), ProgramType::UInt8Pointer)
    else {
        unreachable!("a typed pointer is a pointer")
    };
    let slice = data.with_element_count(OldMachineTerm::uint64_constant(4));
    let raised = slices::raise_slice(
        &slice,
        ParameterBinding::default(),
        &ExecutionState::new(),
        &BTreeMap::new(),
    );
    let Some(SyntaxTerm::Call { name, arguments }) = raised else {
        panic!("an unnamed slice raises as a call: {raised:?}");
    };
    assert_eq!(name, crate::surface::RUST_SLICE_FROM_RAW_PARTS);
    assert_eq!(arguments.len(), 2);
}

/// A string slice raises with `str`'s own operations
/// (`design/rust-slice-values.md`, "String slices"): the slice as its name,
/// its count as `str::len` and its data pointer as `str::as_ptr` of that
/// name, the same slice at the byte slice type as `str::as_bytes` of it,
/// and an unnamed string slice as `str::from_utf8_unchecked` of its
/// construction. Each spelling lowers back to the same type.
#[test]
fn a_string_slice_raises_with_its_own_operations() {
    let _session = crate::kernel::VerificationSession::enter();
    let string = ProgramType::SlicePointer(crate::kernel::SliceElement::Str);
    let variable = Variable(961_000);
    let ProgramValue::Pointer(text) = crate::kernel::symbolic_call_result(string, variable) else {
        unreachable!("a slice result is a pointer")
    };
    let _name = folds::Binding::enter(
        (folds::BinderCarrier::Program, variable),
        SurfaceBinder::Written("s".into()),
    );
    let _slice = folds::SliceBinding::enter(variable, crate::kernel::SliceElement::Str);
    let raise = |slice: &crate::kernel::Pointer| {
        slices::raise_slice(
            slice,
            ParameterBinding::default(),
            &ExecutionState::new(),
            &BTreeMap::new(),
        )
    };
    let name = SyntaxTerm::ProgramExpression(ProgramExpression::Variable("s".into()));
    let call = |name: &str, arguments: Vec<SyntaxTerm>| SyntaxTerm::Call {
        name: name.to_string(),
        arguments,
    };
    assert_eq!(raise(&text), Some(name.clone()));
    assert_eq!(
        raise(&text.clone().with_type(ProgramType::SlicePointer(
            crate::kernel::SliceElement::UInt8
        ))),
        Some(call(crate::surface::RUST_STR_AS_BYTES, vec![name.clone()]))
    );
    assert_eq!(
        synthesize_surface_bitvector(
            text.len().unwrap(),
            ParameterBinding::default(),
            &ExecutionState::new(),
            &BTreeMap::new(),
        ),
        Some(call(crate::surface::RUST_STR_LEN, vec![name.clone()]))
    );
    assert_eq!(
        slices::raise_slice_data(
            text.as_ptr().address(),
            ParameterBinding::default(),
            &ExecutionState::new(),
            &BTreeMap::new(),
        ),
        Some(call(crate::surface::RUST_STR_AS_PTR, vec![name]))
    );
    let ProgramValue::Pointer(data) =
        ProgramValue::typed_pointer(crate::kernel::Address::null(), ProgramType::UInt8Pointer)
    else {
        unreachable!("a typed pointer is a pointer")
    };
    let unnamed = data
        .with_element_count(OldMachineTerm::uint64_constant(4))
        .with_type(string);
    let Some(SyntaxTerm::Call { name, arguments }) = raise(&unnamed) else {
        panic!("an unnamed string slice raises as a call");
    };
    assert_eq!(name, crate::surface::RUST_STR_FROM_UTF8_UNCHECKED);
    assert!(
        matches!(arguments.as_slice(), [SyntaxTerm::Call { name, .. }] if name == crate::surface::RUST_SLICE_FROM_RAW_PARTS),
        "{arguments:?}"
    );
}

/// A read through a Rust slice parameter's data pointer names that pointer
/// as `bytes.as_ptr()`, never the slice's own name
/// (`design/rust-slice-values.md`, step 3c-i's known limit): the parameter is
/// the one wide value, so `*(bytes as (uint8 *))` reads through no pointer
/// and does not lower. The read raises as `*bytes.as_ptr()`, a byte read at
/// the slice's element type, and lowers back to the same read.
#[test]
fn a_read_through_a_slice_parameter_names_its_data_pointer() {
    let _session = crate::kernel::VerificationSession::enter();
    let data = Address::new(AddressBase::ExternalArgument, AddressOffset::constant(0));
    let ProgramValue::Pointer(thin) =
        ProgramValue::typed_pointer(data.clone(), ProgramType::UInt8Pointer)
    else {
        unreachable!("a typed pointer is a pointer")
    };
    let slice = ProgramValue::Pointer(thin.with_element_count(OldMachineTerm::uint64_constant(4)));
    let parameters = [crate::languages::interface::ImportedParameter::new(
        InterfaceType::Slice(crate::kernel::SliceElement::UInt8),
        "bytes".into(),
        None,
    )];
    let arguments = [ProgramExpression::Value(slice.clone())];
    let state = ExecutionState::new()
        .with_memory(SymbolicMemory::new().with_block(AddressBase::ExternalArgument, 4))
        .with_local("bytes", slice);
    let naming = std::sync::Arc::new(crate::surface::ParameterNaming::new(
        &parameters,
        &arguments,
    ));
    let data_pointer =
        ProgramExpression::SliceData(Box::new(ProgramExpression::Variable("bytes".into())));
    for binding in [
        ParameterBinding::new(&parameters, &arguments),
        ParameterBinding::new(&parameters, &arguments).with_naming(&naming),
    ] {
        assert_eq!(
            synthesize_surface_pointer(&data, binding, &state, &BTreeMap::new()),
            Some(data_pointer.clone())
        );
    }
    let load = OldMachineTerm::read_named(
        crate::kernel::ProgramPoint::at(&(crate::kernel::intern_memory_ref(state.memory()))),
        Box::new(data),
        crate::kernel::LoadKind::UInt8,
    );
    let binding = ParameterBinding::new(&parameters, &arguments).with_naming(&naming);
    let raised = synthesize_surface_bitvector(&load, binding, &state, &BTreeMap::new());
    assert!(
        matches!(&raised, Some(SyntaxTerm::ProgramExpression(ProgramExpression::TypedLoad {
            pointer,
            value_type: ProgramType::UInt8,
            ..
        })) if **pointer == data_pointer),
        "{raised:?}"
    );
    let OldMachineTerm::MemoryLoad(memory, address, kind) = load else {
        unreachable!("a named read is a load")
    };
    let read = crate::kernel::canonical_form_of_load(
        crate::kernel::ProgramPoint::from(memory).into_shared_memory(),
        address.into(),
        kind,
    );
    let requirement = Proposition::condition_is(
        OldConditionTerm::Compare {
            format: MachineIntegerType::UInt8,
            relation: CompareRelation::Equal,
            left: Box::new(read.clone()),
            right: Box::new(read),
        },
        true,
    );
    let spelled = synthesize_surface_proposition(&requirement, binding, &state)
        .expect("a read through a slice parameter has a Click spelling");
    assert_eq!(
        relower_written_proposition(&spelled, &state)
            .map(|fact| crate::kernel::canonical_condition_fact(&fact)),
        Ok(crate::kernel::canonical_condition_fact(&requirement)),
    );
}
