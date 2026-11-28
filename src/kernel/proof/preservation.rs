//! Preserve one selected observation across an explicitly separated footprint.
//! No history, read reconstruction, or premise discovery belongs here.
use crate::kernel::eval::typed_reads::{self, ReadType};
use crate::kernel::prelude::*;
use crate::kernel::{IntegerComparisonOperator, KernelTerm, KernelTermImport, StoredConditionTerm};

pub(crate) fn apply(
    separation: &Proposition,
    field: Option<typed_reads::FieldSelection>,
    result: &Proposition,
    return_state: Option<&ExecutionState>,
    available: impl Fn(&Proposition) -> bool,
) -> Result<(), String> {
    crate::instrumentation::record_deterministic_work(1);
    // The public arguments select a resource and a region, so either written
    // orientation of that exact separation is sufficient. Both keys come
    // solely from those arguments; no fact or resource bucket is traversed.
    let separation_available = available(separation)
        || if let Proposition::ResourceSeparate { left, right } = separation {
            crate::instrumentation::record_deterministic_work(1);
            available(&Proposition::ResourceSeparate {
                left: right.clone(),
                right: left.clone(),
            })
        } else {
            false
        };
    if !separation_available {
        return Err("preserve separation is not exactly available".into());
    }
    let derived = if let Proposition::MemoryLoadable { memory, point, .. } = result {
        let (before, after) = preserve_viewability(separation, memory, point)?;
        if !available(&before) {
            return Err("preserve requires viewability at the footprint entry".into());
        }
        after
    } else if let Proposition::MemoryReadDefined { value_type, .. } = result {
        let (before, after) = preserve_definedness(separation, *value_type, return_state, result)
            .ok_or(
            "preserve definedness requires a footprint separated from a complete typed cell",
        )?;
        if !available(&before) {
            return Err("preserve requires definedness at the footprint entry".into());
        }
        after
    } else if let Some(field) = field {
        preserve_field(separation, field).ok_or(
            "preserve requires the selected field of a resource separated from the footprint",
        )?
    } else if result.literal_condition() == Some((true, true)) {
        result.clone()
    } else {
        preserve_footprint(
            separation,
            read_type(result).ok_or("unsupported footprint observation")?,
            result,
        )
        .ok_or(
            "preserve requires a region footprint separated from the selected complete observation",
        )?
    };
    if &derived != result {
        return Err("preserve's constructed result does not match the goal".into());
    }
    Ok(())
}

fn preserve_viewability(
    separation: &Proposition,
    goal_memory: &SymbolicMemory,
    goal_point: &crate::kernel::program_point::PathLink,
) -> Result<(Proposition, Proposition), String> {
    let Proposition::ResourceSeparate { left, right } = separation else {
        return Err("preserve viewability requires footprint separation".into());
    };
    let (footprint, range) = match (left.as_ref(), right.as_ref()) {
        (Resource::Footprint(fp), Resource::Memory(range))
        | (Resource::Memory(range), Resource::Footprint(fp)) => (fp, range),
        _ => return Err("preserve viewability requires a separated memory range".into()),
    };
    if !footprint.preserves_separate_viewability {
        return Err(
            "preserve viewability requires a complete automatic-storage-only footprint".into(),
        );
    }
    let (after, after_point) =
        if footprint.viewability_survives_return_cleanup(goal_memory, range.base()) {
            (goal_memory, goal_point.clone())
        } else {
            (&footprint.after, footprint.after_point.path_link().clone())
        };
    Ok((
        range.loadable_fact(
            &footprint.before,
            footprint.before_point.path_link().clone(),
        ),
        range.loadable_fact(after, after_point),
    ))
}

// The written result selects only the observation's type. Its endpoints are
// never used to manufacture the primitive's conclusion.
fn read_type(result: &Proposition) -> Option<ReadType> {
    use crate::kernel::{BooleanOperandView, IntegerComparisonOperator, KernelTermNode};
    let Proposition::ConditionIs(condition, true) = result else {
        return None;
    };
    let view = condition.operand_view();
    if view.equality().is_some() {
        return Some(ReadType::Boolean);
    }
    if view.pointer_addresses().is_some() {
        return Some(ReadType::IntegerAddress);
    }
    if let Some([left, right]) = view.pointer_values() {
        let ty = left.node().program_type;
        return (ty == right.node().program_type).then_some(ReadType::Pointer(ty));
    }
    if let Some((format, relation, _)) = view.comparison() {
        return (relation == CompareRelation::Equal
            && !matches!(
                format,
                MachineIntegerType::Int128 | MachineIntegerType::UInt128
            ))
        .then_some(ReadType::Integer(format));
    }
    if let Some((IntegerComparisonOperator::Equal, operands)) =
        crate::kernel::machine_integer::comparison::written_integer_comparison(view)
    {
        let [left, right] = operands
            .each_ref()
            .map(|operand| match operand.root().node() {
                KernelTermNode::MachineObservation { format, .. } => Some(*format),
                _ => None,
            });
        let format = left?;
        return (right == Some(format)
            && matches!(
                format,
                MachineIntegerType::Int128 | MachineIntegerType::UInt128
            ))
        .then_some(ReadType::Integer(format));
    }
    match view {
        BooleanOperandView::Native(OldConditionTerm::AlgebraicEqual(a, b)) => {
            (a.algebraic_type == b.algebraic_type).then_some(ReadType::Abstract)
        }
        BooleanOperandView::Shared(root) => match root.node() {
            KernelTermNode::AlgebraicEqual { arguments: [a, b] } => {
                (a.ty() == b.ty()).then_some(ReadType::Abstract)
            }
            _ => None,
        },
        _ => None,
    }
}

/// Interpret an explicitly bounded logical range as a physical observation.
/// A modular byte count is insufficient: reversed or oversized ranges can
/// wrap to the width of a scalar. Use the actual signed endpoint difference
/// and checked scaling instead. Symbolic spans need an explicit reduction
/// to a complete cell before this primitive can use them.
fn observation_footprint(range: &MemoryRange) -> Option<(Address, u32)> {
    let start = range.signed_constant_start()?;
    let end = range.signed_constant_end()?;
    let elements = u32::try_from(end.checked_sub(start)?).ok()?;
    let bytes = elements.checked_mul(range.element_width())?;
    (bytes > 0).then(|| (range.start_pointer(), bytes))
}

fn preserve_footprint(
    separation: &Proposition,
    kind: ReadType,
    result: &Proposition,
) -> Option<Proposition> {
    let Proposition::ResourceSeparate { left, right } = separation else {
        return None;
    };
    let (footprint, kept) = match (left.as_ref(), right.as_ref()) {
        (Resource::Footprint(fp), Resource::Memory(kept))
        | (Resource::Memory(kept), Resource::Footprint(fp)) => (fp, kept),
        _ => return None,
    };
    if kept.wide_bounds().is_some() {
        return None;
    }
    let (address, bytes) = observation_footprint(kept)?;
    let observed = observation_type(kind, bytes, result)?;
    observation_equality(footprint, address, observed, kind)
}

/// The footprint and separated cell determine the typed observation. A
/// published return can supply its endpoint when checked cleanup follows.
fn preserve_definedness(
    separation: &Proposition,
    value_type: ProgramType,
    outcome_state: Option<&ExecutionState>,
    result: &Proposition,
) -> Option<(Proposition, Proposition)> {
    crate::instrumentation::record_deterministic_work(1);
    let Proposition::ResourceSeparate { left, right } = separation else {
        return None;
    };
    let (footprint, kept) = match (left.as_ref(), right.as_ref()) {
        (Resource::Footprint(fp), Resource::Memory(kept))
        | (Resource::Memory(kept), Resource::Footprint(fp)) => (fp, kept),
        _ => return None,
    };
    if kept.wide_bounds().is_some() {
        return None;
    }
    let (pointer, bytes) = observation_footprint(kept)?;
    if bytes != value_type.byte_width() {
        return None;
    }
    let defined = |point: &ProgramPoint, memory: &SymbolicMemory| Proposition::MemoryReadDefined {
        at: point.id(),
        memory: memory.clone(),
        point: point.path_link().clone(),
        pointer: pointer.clone(),
        value_type,
    };
    let before = defined(&footprint.before_point, &footprint.before);
    let after = defined(&footprint.after_point, &footprint.after);
    if &after != result
        && let Some(outcome) = outcome_state
        && footprint.viewability_survives_return_cleanup(outcome.memory(), &pointer)
    {
        // The focused return judgment supplies its observation point. The
        // memory derivation checks that cleanup retired a distinct object.
        return Some((
            before,
            Proposition::MemoryReadDefined {
                point: outcome.memory_point(),
                at: outcome.observation_point_id(),
                memory: outcome.memory().clone(),
                pointer,
                value_type,
            },
        ));
    }
    Some((before, after))
}

// Resource field values are retained by the persistent resource contexts.
// Select one identity and one field from each endpoint; never unfold the
// resource, enumerate its other fields, or replay its modifications.
fn preserve_field(
    separation: &Proposition,
    field: typed_reads::FieldSelection,
) -> Option<Proposition> {
    let Proposition::ResourceSeparate { left, right } = separation else {
        return None;
    };
    let (footprint, kept) = match (left.as_ref(), right.as_ref()) {
        (Resource::Footprint(fp), Resource::Instance(kept))
        | (Resource::Instance(kept), Resource::Footprint(fp)) => (fp, kept),
        _ => return None,
    };
    if kept.identity() != field.identity {
        return None;
    }
    crate::instrumentation::record_deterministic_work(2);
    let before = footprint.before_resources.owned_instance(field.identity)?;
    let after = footprint.after_resources.owned_instance(field.identity)?;
    if let Some(a) = after.fields().integer_term(field.index) {
        let b = before.fields().integer_term(field.index)?;
        return Some(Proposition::condition_is(
            StoredConditionTerm::integer_comparison(
                IntegerComparisonOperator::Equal,
                a.into_shared(),
                b.into_shared(),
            ),
            true,
        ));
    }
    let a = after.fields().get(field.index)?;
    let b = before.fields().get(field.index)?;
    let condition = match (a, b) {
        (
            crate::kernel::ResourceFieldValue::Algebraic(a),
            crate::kernel::ResourceFieldValue::Algebraic(b),
        ) if a.algebraic_type == b.algebraic_type => {
            return Some(Proposition::Equal(
                Term::Algebraic(a.clone().into()),
                Term::Algebraic(b.clone().into()),
            ));
        }
        (
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Parameter(a)),
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Parameter(b)),
        ) if a.algebraic_type == b.algebraic_type => StoredConditionTerm::algebraic_equal(a, b),
        (
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(a)),
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Pointer(b)),
        ) => StoredConditionTerm::logical_pointer_equal(a, b),
        (
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Int32(a)),
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Int32(b)),
        ) => integer_equality(MachineIntegerType::Int32, a.clone(), b.clone())?,
        // An 8-bit field value is native: its equality is at its own format.
        (
            crate::kernel::ResourceFieldValue::Program(ProgramValue::UInt8(a)),
            crate::kernel::ResourceFieldValue::Program(ProgramValue::UInt8(b)),
        ) => integer_equality(MachineIntegerType::UInt8, a.clone(), b.clone())?,
        (
            crate::kernel::ResourceFieldValue::Program(ProgramValue::UInt32(a)),
            crate::kernel::ResourceFieldValue::Program(ProgramValue::UInt32(b)),
        ) => integer_equality(MachineIntegerType::UInt32, a.clone(), b.clone())?,
        (
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Int64(a)),
            crate::kernel::ResourceFieldValue::Program(ProgramValue::Int64(b)),
        ) => integer_equality(MachineIntegerType::Int64, a.clone(), b.clone())?,
        (
            crate::kernel::ResourceFieldValue::Program(ProgramValue::UInt64(a)),
            crate::kernel::ResourceFieldValue::Program(ProgramValue::UInt64(b)),
        ) => integer_equality(MachineIntegerType::UInt64, a.clone(), b.clone())?,
        _ => return None,
    };
    Some(Proposition::condition_is(condition, true))
}

// A native comparison selects its own format. A promoted byte or halfword
// comparison must name two widenings of the same type, since the footprint's
// width alone cannot distinguish signed from unsigned reads.
fn observation_type(comparison: ReadType, bytes: u32, result: &Proposition) -> Option<ReadType> {
    match (comparison, bytes) {
        (ReadType::Integer(MachineIntegerType::Int32), 1 | 2) => {
            let Proposition::ConditionIs(condition, true) = result else {
                return None;
            };
            let (_, _, [left, right]) = condition.operand_view().comparison()?;
            let (left, _) = left.narrow_widening32_operand()?;
            let (right, _) = right.narrow_widening32_operand()?;
            (left == right && left.program_type().byte_width() == bytes)
                .then_some(ReadType::Integer(left))
        }
        (kind, bytes) if kind.bytes() == bytes => Some(kind),
        _ => None,
    }
}

fn observation_equality(
    footprint: &crate::kernel::RegionFootprint,
    address: Address,
    kind: ReadType,
    comparison: ReadType,
) -> Option<Proposition> {
    let after = typed_reads::get_at(&footprint.after_point, &address, kind)?;
    let before = typed_reads::get_at(&footprint.before_point, &address, kind)?;
    // A promoted comparison compares the narrow reads' widenings.
    if let (ReadType::Integer(narrow), ReadType::Integer(MachineIntegerType::Int32)) =
        (kind, comparison)
        && narrow != MachineIntegerType::Int32
    {
        let comparison = MachineIntegerType::Int32;
        let mut import = KernelTermImport::for_exact_field_inputs();
        let operands = [integer_bits(after)?, integer_bits(before)?].map(|word| {
            import
                .machine(narrow, &word)
                .promote_narrow_to_int32(narrow)
        });
        return Some(Proposition::condition_is(
            stored_word_equality(comparison, operands),
            true,
        ));
    }
    let condition = match (kind, after, before) {
        (ReadType::Boolean, ProgramValue::Bool(a), ProgramValue::Bool(b)) => {
            let mut import = KernelTermImport::for_exact_field_inputs();
            let root = KernelTerm::boolean_equal([
                import.truth_of_bool_word(&a),
                import.truth_of_bool_word(&b),
            ]);
            StoredConditionTerm::from_root(root).expect("Boolean equality")
        }
        (ReadType::Pointer(_), ProgramValue::Pointer(a), ProgramValue::Pointer(b)) => {
            StoredConditionTerm::logical_pointer_equal(&a, &b)
        }
        (ReadType::IntegerAddress, ProgramValue::Pointer(a), ProgramValue::Pointer(b)) => {
            StoredConditionTerm::address_equal(a.address(), b.address())
        }
        (ReadType::Abstract, ProgramValue::Parameter(a), ProgramValue::Parameter(b))
            if a.algebraic_type == b.algebraic_type =>
        {
            StoredConditionTerm::algebraic_equal(&a, &b)
        }
        (ReadType::Integer(format), a, b) => {
            integer_equality(format, integer_bits(a)?, integer_bits(b)?)?
        }
        _ => return None,
    };
    Some(Proposition::condition_is(condition, true))
}

fn integer_bits(value: ProgramValue) -> Option<OldMachineTerm> {
    match value {
        ProgramValue::Int8(t)
        | ProgramValue::UInt8(t)
        | ProgramValue::Int16(t)
        | ProgramValue::UInt16(t)
        | ProgramValue::Int32(t)
        | ProgramValue::UInt32(t)
        | ProgramValue::Int64(t)
        | ProgramValue::UInt64(t)
        | ProgramValue::Int128(t)
        | ProgramValue::UInt128(t) => Some(t),
        _ => None,
    }
}

fn stored_word_equality(
    format: MachineIntegerType,
    operands: [KernelTerm; 2],
) -> StoredConditionTerm {
    let root = KernelTerm::boolean_comparison(format, CompareRelation::Equal, operands);
    StoredConditionTerm::from_root(root).expect("machine word equality")
}

fn integer_equality(
    format: MachineIntegerType,
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> Option<StoredConditionTerm> {
    Some(match format {
        MachineIntegerType::Int8
        | MachineIntegerType::UInt8
        | MachineIntegerType::Int16
        | MachineIntegerType::UInt16
        | MachineIntegerType::Int32
        | MachineIntegerType::UInt32 => {
            let mut import = KernelTermImport::for_exact_field_inputs();
            stored_word_equality(
                format,
                [
                    import.machine(format, &left),
                    import.machine(format, &right),
                ],
            )
        }
        MachineIntegerType::Int64 | MachineIntegerType::UInt64 => {
            // The produced equality must have the same shape as its logical
            // goal, including reflexive variables and closed literal operands.
            StoredConditionTerm::logical_word64_equality(format, left, right, false)
        }
        MachineIntegerType::Int128 | MachineIntegerType::UInt128 => {
            StoredConditionTerm::integer_comparison(
                IntegerComparisonOperator::Equal,
                IntegerTerm::from_machine(format, left)?.into(),
                IntegerTerm::from_machine(format, right)?.into(),
            )
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserved_wide_integer_equalities_keep_the_observation_format() {
        use crate::kernel::{IntegerComparisonOperator, KernelTermNode, MachineIntegerConstant};
        let _session = crate::kernel::VerificationSession::enter();
        for format in [MachineIntegerType::Int128, MachineIntegerType::UInt128] {
            let word = OldMachineTerm::Variable(Variable(983424));
            let symbolic = integer_equality(format, word.clone(), word.clone()).unwrap();
            let root = symbolic.root().unwrap();
            assert!(!root.has_cached_native_argument());
            let KernelTermNode::IntegerCompare {
                operator: IntegerComparisonOperator::Equal,
                arguments,
            } = root.node()
            else {
                panic!("expected structural Integer equality");
            };
            assert_eq!(arguments[0], arguments[1]);
            assert!(
                matches!(arguments[0].node(), KernelTermNode::MachineObservation { format: ty, .. } if *ty == format)
            );
            let literal = |bits| {
                OldMachineTerm::machine_constant(
                    MachineIntegerConstant::from_bits(format.format(), bits).unwrap(),
                )
            };
            for (right, expected) in [(1u128 << 127, true), (0, false)] {
                let folded =
                    integer_equality(format, literal(1u128 << 127), literal(right)).unwrap();
                assert_eq!(folded.operand_view().constant(), Some(expected));
            }
            assert!(integer_equality(format, word, OldMachineTerm::constant(0)).is_none());
        }
    }

    #[test]
    fn promoted_preservation_reads_exact_widenings_without_exporting_the_goal() {
        use MachineIntegerType as T;
        let _session = crate::kernel::VerificationSession::enter();
        let widen = |source, variable| {
            OldMachineTerm::machine_integer_cast(
                source,
                T::Int32,
                OldMachineTerm::Variable(variable),
            )
        };
        for (right_type, expected) in [
            (T::UInt8, Some(ReadType::Integer(T::UInt8))),
            (T::Int8, None),
        ] {
            let written = OldConditionTerm::equal(
                widen(T::UInt8, Variable(983411)),
                widen(right_type, Variable(983412)),
            );
            let root = KernelTermImport::default().condition(&written);
            let stored = StoredConditionTerm::from_root(root.clone()).unwrap();
            for condition in [StoredConditionTerm::from(written), stored] {
                let goal = Proposition::condition_is(condition.clone(), true);
                let comparison = read_type(&goal).unwrap();
                assert_eq!(comparison, ReadType::Integer(T::Int32));
                assert_eq!(observation_type(comparison, 1, &goal), expected);
                assert_eq!(observation_type(comparison, 2, &goal), None);
                assert_eq!(
                    read_type(&Proposition::condition_is(condition, false)),
                    None
                );
            }
            assert!(!root.has_cached_native_argument());
        }
    }

    #[test]
    fn return_preservation_refuses_a_view_of_the_retired_local() {
        let _session = crate::kernel::VerificationSession::enter();
        let state = ExecutionState::new()
            .with_local("selected", int32(5))
            .with_memory(SymbolicMemory::new().with_block("local:selected", 4));
        let local = state.locals().slot("selected").unwrap().clone();
        let range = MemoryRange::new(local.clone(), 0u32.into(), 4u32.into());
        let footprint = crate::kernel::RegionFootprint::statement_transition(
            "return".into(),
            &crate::kernel::program_return(ProgramExpression::Value(int32(0))),
            &state,
            &state,
            &ExecutionFacts::new(),
        );
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Footprint(footprint)),
            right: Box::new(Resource::Memory(range.clone())),
        };
        let entry_view = range.loadable_fact(state.memory(), state.memory_point());
        let goal = range.loadable_fact(
            &state.memory().without_local_block(&local.base),
            Default::default(),
        );
        assert_eq!(
            apply(&separation, None, &goal, None, |fact| {
                fact == &separation || fact == &entry_view
            }),
            Err("preserve's constructed result does not match the goal".into())
        );
    }

    #[derive(Clone)]
    pub(super) struct Preservation {
        pub separation: Proposition,
        pub field: Option<typed_reads::FieldSelection>,
        pub result: Proposition,
    }
    impl Preservation {
        pub fn apply(
            &self,
            available: impl Fn(&Proposition) -> bool,
        ) -> Result<Proposition, String> {
            super::apply(&self.separation, self.field, &self.result, None, available)?;
            Ok(self.result.clone())
        }
        pub fn points(&self) -> (&ProgramPoint, &ProgramPoint) {
            let Proposition::ResourceSeparate { left, .. } = &self.separation else {
                unreachable!()
            };
            let Resource::Footprint(fp) = left.as_ref() else {
                unreachable!()
            };
            (&fp.before_point, &fp.after_point)
        }
    }

    pub(super) fn definedness_fixture(
        history: u64,
        ty: ProgramType,
    ) -> (Preservation, Proposition, Proposition, Proposition) {
        let pointer = Address::symbolic(Variable(8_410_000));
        let mut memory = SymbolicMemory::new();
        for i in 0..history {
            // Grow both related history and unrelated memory.
            memory = memory.store(
                pointer.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(i as u32)),
            );
            memory = memory.store(
                Address::symbolic(Variable(8_420_000 + i)),
                ProgramValue::Int32(OldMachineTerm::constant(i as u32)),
            );
        }
        let before = ExecutionState::new().with_memory(memory.clone());
        let after = ExecutionState::new().with_memory(memory.store(
            Address::symbolic(Variable(8_430_000)),
            ProgramValue::Int32(1u32.into()),
        ));
        let footprint = crate::kernel::RegionFootprint::transition(
            "selected".into(),
            &before,
            &after,
            &Vec::<ExecutionPureFact>::new(),
        );
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Footprint(footprint)),
            right: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                pointer.clone(),
                0u32.into(),
                1u32.into(),
                ty.byte_width(),
            ))),
        };
        let old = Proposition::MemoryReadDefined {
            point: Default::default(),
            at: before.program_point().id(),
            memory: before.memory().clone(),
            pointer: pointer.clone(),
            value_type: ty,
        };
        let goal = Proposition::MemoryReadDefined {
            point: Default::default(),
            at: after.program_point().id(),
            memory: after.memory().clone(),
            pointer,
            value_type: ty,
        };
        (
            Preservation {
                separation: separation.clone(),
                field: None,
                result: goal.clone(),
            },
            separation,
            old,
            goal,
        )
    }

    #[test]
    fn observation_footprint_uses_nonwrapping_signed_span() {
        let _session = crate::kernel::VerificationSession::enter();
        for (start, end, width, expected) in [
            (0i32, 1i32, 4, Some(4)),
            (-1, 0, 4, Some(4)),
            (0, 0, 4, None),
            (0, -1073741823, 4, None),
            (0, 1073741825, 4, None),
            (i32::MAX, i32::MIN, 4, None),
            (i32::MIN, i32::MAX, 4, None),
        ] {
            let range = MemoryRange::new_with_element_width(
                Address::symbolic(Variable(8_499_100)),
                OldMachineTerm::constant(start as u32),
                OldMachineTerm::constant(end as u32),
                width,
            );
            assert_eq!(
                observation_footprint(&range).map(|(_, bytes)| bytes),
                expected
            );
        }
    }

    #[test]
    fn preserve_definedness_requires_exact_entry_evidence_and_complete_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        for ty in [
            ProgramType::UInt8,
            ProgramType::Int32,
            ProgramType::UInt64,
            ProgramType::Int32Pointer,
        ] {
            let (mut preservation, separation, old, goal) = definedness_fixture(4, ty);
            let available = |p: &Proposition| p == &separation || p == &old;
            assert_eq!(preservation.apply(available).unwrap(), goal);
            assert!(
                preservation
                    .apply(|p| p == &separation)
                    .unwrap_err()
                    .contains("footprint entry")
            );
            assert!(preservation.apply(|p| p == &old).is_err());
            for corruption in 0..4 {
                let mut bad = goal.clone();
                let Proposition::MemoryReadDefined {
                    at,
                    memory,
                    pointer,
                    value_type,
                    ..
                } = &mut bad
                else {
                    unreachable!()
                };
                match corruption {
                    0 => *memory = SymbolicMemory::new(),
                    1 => *pointer = Address::symbolic(Variable(8_499_000)),
                    2 => {
                        *at = ExecutionState::new()
                            .with_memory(memory.clone())
                            .program_point()
                            .id()
                    }
                    _ => {
                        *value_type = if ty == ProgramType::UInt8 {
                            ProgramType::Int32
                        } else {
                            ProgramType::UInt8
                        }
                    }
                }
                let result = &mut preservation.result;
                *result = bad;
                assert!(
                    preservation.apply(available).is_err(),
                    "corruption {corruption}"
                );
            }
            let mut swapped = separation.clone();
            let Proposition::ResourceSeparate { left, right } = &mut swapped else {
                unreachable!()
            };
            std::mem::swap(left, right);
            assert_eq!(
                preserve_definedness(&swapped, ty, None, &goal),
                Some((old, goal))
            );
        }
    }

    pub(super) fn resource_fixture(size: u64) -> (Preservation, Proposition) {
        resource_fixture_with_values(
            size,
            MachineIntegerType::Int32,
            OldMachineTerm::Variable(Variable(8_390_901)),
            OldMachineTerm::Variable(Variable(8_390_902)),
        )
    }

    pub(super) fn resource_fixture_with_values(
        size: u64,
        format: MachineIntegerType,
        before_value: OldMachineTerm,
        after_value: OldMachineTerm,
    ) -> (Preservation, Proposition) {
        let schema = ResourceFieldSchema::new(vec![(
            "value".into(),
            ResourceFieldType::Program(format.program_type()),
        )])
        .unwrap();
        let instance = |identity, value| {
            ResourceInstance::new(
                InstanceId::from_variable(Variable(identity)),
                "model".into(),
                vec![].into(),
                schema.clone(),
                vec![AlgebraicValue::Program(format.value_from_term(value))].into(),
            )
            .unwrap()
        };
        let kept = instance(8_390_900, before_value.clone());
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources =
                resources.unchecked_with_fact(ResourceFact::own(Resource::Instance(instance(
                    9_000_000 + i,
                    OldMachineTerm::Variable(Variable(10_000_000 + i)),
                ))));
        }
        let before = ExecutionState::new().with_resource_context(
            resources
                .clone()
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(kept.clone()))),
        );
        let after = ExecutionState::new().with_resource_context(resources.unchecked_with_fact(
            ResourceFact::own(Resource::Instance(instance(8_390_900, after_value.clone()))),
        ));
        // A supplied frame premise relates these symbolic endpoint values.
        // As with the memory fixture, establishing the premise is a separate
        // obligation, never performed by preservation application.
        let footprint = crate::kernel::RegionFootprint::transition(
            "selected".into(),
            &before,
            &after,
            &Vec::<ExecutionPureFact>::new(),
        );
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Footprint(footprint)),
            right: Box::new(Resource::Instance(kept)),
        };
        let goal = Proposition::condition_is(
            match format {
                MachineIntegerType::Int64 | MachineIntegerType::UInt64 => {
                    OldConditionTerm::Compare {
                        format: MachineIntegerType::Int64,
                        relation: CompareRelation::Equal,
                        left: Box::new(after_value),
                        right: Box::new(before_value),
                    }
                }
                _ => OldConditionTerm::equal(after_value, before_value),
            },
            true,
        );
        (
            Preservation {
                separation,
                field: Some(typed_reads::FieldSelection {
                    identity: InstanceId::from_variable(Variable(8_390_900)),
                    index: 0,
                }),
                result: goal.clone(),
            },
            goal,
        )
    }

    #[test]
    fn wide_resource_field_equalities_retain_their_selected_endpoints() {
        for format in [MachineIntegerType::Int64, MachineIntegerType::UInt64] {
            let _session = crate::kernel::VerificationSession::enter();
            let variable = OldMachineTerm::Variable(Variable(8_390_901));
            let literal = if format == MachineIntegerType::Int64 {
                OldMachineTerm::int64_constant(7)
            } else {
                OldMachineTerm::uint64_constant(7)
            };
            for (before, after) in [
                (variable.clone(), variable.clone()),
                (literal.clone(), literal.clone()),
                (
                    variable.clone(),
                    OldMachineTerm::Variable(Variable(8_390_902)),
                ),
                (literal, variable),
            ] {
                let (mut preservation, goal) =
                    resource_fixture_with_values(4, format, before, after);
                let separation = preservation.separation.clone();
                assert_eq!(preservation.apply(|p| p == &separation).unwrap(), goal);
                assert!(preservation.apply(|_| false).is_err());
                let (condition, truth) =
                    preservation.result.old_condition().expect("wide equality");
                let mut condition = condition.clone();
                let truth = *truth;
                let OldConditionTerm::Compare { left, .. } = &mut condition else {
                    panic!("wide equality")
                };
                **left = OldMachineTerm::Variable(Variable(8_390_999));
                preservation.result = Proposition::condition_is(condition, truth);
                assert!(preservation.apply(|p| p == &separation).is_err());
            }
        }
    }

    pub(super) fn resource_history_fixture(history: u64) -> (Preservation, Proposition) {
        let (mut preservation, goal) = resource_fixture(1);
        let proposition = &mut preservation.separation;
        let Proposition::ResourceSeparate { left, right } = proposition else {
            unreachable!()
        };
        let Resource::Footprint(fp) = left.as_ref() else {
            unreachable!()
        };
        let Resource::Instance(kept) = right.as_ref() else {
            unreachable!()
        };
        let mut resources = fp.before_resources.clone();
        for _ in 0..history {
            let fact = ResourceFact::own(Resource::Instance(kept.clone()));
            resources = resources
                .without_exact_representation(&fact)
                .unwrap()
                .unchecked_with_fact(fact);
        }
        let before = ExecutionState::new().with_resource_context(resources);
        let after = ExecutionState::new().with_resource_context(fp.after_resources.clone());
        **left = Resource::Footprint(crate::kernel::RegionFootprint::transition(
            "selected".into(),
            &before,
            &after,
            &Vec::<ExecutionPureFact>::new(),
        ));
        (preservation, goal)
    }

    #[test]
    fn resource_preservation_selects_exact_identity_field_and_values() {
        let (preservation, goal) = resource_fixture(8);
        assert_eq!(preservation.apply(|_| true).unwrap(), goal);
        assert!(
            preservation.apply(|_| false).is_err(),
            "separation must be available"
        );
        for field in [
            typed_reads::FieldSelection {
                identity: InstanceId::from_variable(Variable(8_390_999)),
                index: 0,
            },
            typed_reads::FieldSelection {
                identity: InstanceId::from_variable(Variable(8_390_900)),
                index: 1,
            },
        ] {
            let (mut preservation, _) = resource_fixture(8);
            let selected = &mut preservation.field;
            *selected = Some(field);
            assert!(preservation.apply(|_| true).is_err());
        }
        let (mut preservation, _) = resource_fixture(8);
        let result = &mut preservation.result;
        *result = Proposition::condition_is(
            OldConditionTerm::equal(OldMachineTerm::Variable(Variable(8_390_902)), 99u32.into()),
            true,
        );
        assert!(
            preservation.apply(|_| true).is_err(),
            "the annotation cannot invent a value"
        );
    }

    pub(super) fn observe(
        memory: &SymbolicMemory,
        address: &Address,
        ty: ProgramType,
    ) -> ProgramValue {
        let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            memory,
            address.clone(),
            ty,
            Default::default(),
            Vec::new(),
            &PureFactContext::new(),
        );
        let [path] = paths.as_slice() else {
            panic!("one logical read");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!("logical value");
        };
        value.clone()
    }

    pub(super) fn observe_point(
        point: &ProgramPoint,
        address: &Address,
        ty: ProgramType,
    ) -> ProgramValue {
        let value = observe(point.memory(), address, ty);
        typed_reads::record_at(point, address, &value);
        value
    }

    pub(super) fn fixture(history: u64, cached: bool) -> (Preservation, Proposition) {
        let address = Address::symbolic(Variable(8_310_000));
        let changed = Address::symbolic(Variable(8_310_001));
        let mut before = SymbolicMemory::new();
        for i in 0..history {
            before = before.store(
                Address::symbolic(Variable(8_320_000 + i)),
                ProgramValue::Int32(OldMachineTerm::constant(i as u32)),
            );
        }
        if cached {
            before = before.store(
                address.clone(),
                ProgramValue::typed_pointer(
                    Address::symbolic(Variable(8_310_002)),
                    ProgramType::Int32Pointer,
                ),
            );
        }
        let after = before
            .clone()
            .without_possible_aliasing_cells(&changed, 4, &PureFactContext::new())
            .store(
                changed.clone(),
                ProgramValue::Int32(OldMachineTerm::constant(1)),
            );
        let resource = |p, bytes| {
            Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                p,
                0u32.into(),
                1u32.into(),
                bytes,
            )))
        };
        let entry = ExecutionState::new().with_memory(before.clone());
        let exit = entry.clone().with_memory(after.clone());
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Footprint(
                crate::kernel::RegionFootprint::transition(
                    "selected".into(),
                    &entry,
                    &exit,
                    &Vec::<ExecutionPureFact>::new(),
                ),
            )),
            right: resource(address.clone(), C_POINTER_BYTE_WIDTH),
        };
        let ProgramValue::Pointer(before_value) =
            observe_point(&entry.program_point(), &address, ProgramType::Int32Pointer)
        else {
            unreachable!()
        };
        let ProgramValue::Pointer(after_value) =
            observe_point(&exit.program_point(), &address, ProgramType::Int32Pointer)
        else {
            unreachable!()
        };
        let result = Proposition::condition_is(
            OldConditionTerm::pointer_equal(after_value, before_value),
            true,
        );
        (
            Preservation {
                separation,
                field: None,
                result: result.clone(),
            },
            result,
        )
    }

    pub(super) fn abstract_fixture(history: u64) -> (Preservation, Proposition) {
        let (mut preservation, _) = fixture(history, false);
        let (before, after) = preservation.points();
        let address = Address::symbolic(Variable(8_310_000));
        let ty = ProgramType::Parameter(TypeParameterName::intern("TransportValue"));
        let ProgramValue::Parameter(a) = observe_point(after, &address, ty) else {
            unreachable!()
        };
        let ProgramValue::Parameter(b) = observe_point(before, &address, ty) else {
            unreachable!()
        };
        let goal = Proposition::condition_is(OldConditionTerm::AlgebraicEqual(a, b), true);
        let result = &mut preservation.result;
        *result = goal.clone();
        (preservation, goal)
    }

    #[test]
    fn boolean_preservation_compares_the_truth_of_each_recorded_word() {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (preservation, _) = fixture(0, false);
        let Proposition::ResourceSeparate { left, .. } = &preservation.separation else {
            unreachable!()
        };
        let Resource::Footprint(footprint) = left.as_ref() else {
            unreachable!()
        };
        let address = Address::symbolic(Variable(983421));
        let word = OldMachineTerm::Variable(Variable(983422));
        let cast = OldMachineTerm::bool_cast(
            MachineIntegerType::UInt8,
            OldConditionTerm::Variable(Variable(983423)),
        );
        for before in [cast, word.clone()] {
            typed_reads::record_at(
                &footprint.before_point,
                &address,
                &ProgramValue::Bool(before.clone()),
            );
            typed_reads::record_at(
                &footprint.after_point,
                &address,
                &ProgramValue::Bool(word.clone()),
            );
            let kind = ReadType::Boolean;
            let Some(Proposition::ConditionIs(condition, true)) =
                observation_equality(footprint, address.clone(), kind, kind)
            else {
                panic!("expected Boolean observation equality");
            };
            let expected = OldConditionTerm::bool_equal(
                OldConditionTerm::truth_of_bool_word(&word),
                OldConditionTerm::truth_of_bool_word(&before),
            );
            assert_eq!(condition, StoredConditionTerm::from(expected));
            assert!(!condition.root().unwrap().has_cached_native_argument());
        }
    }

    #[test]
    fn abstract_memory_preservation_uses_recorded_typed_values() {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (mut preservation, goal) = abstract_fixture(8);
        assert_eq!(preservation.apply(|_| true).unwrap(), goal);
        let result = &mut preservation.result;
        let Some((condition, true)) = result.old_condition() else {
            unreachable!()
        };
        let mut condition = condition.clone();
        let OldConditionTerm::AlgebraicEqual(_, old) = &mut condition else {
            unreachable!()
        };
        old.algebraic_type = TypeParameterName::intern("WrongTransportValue").algebraic_type();
        *result = Proposition::condition_is(condition, true);
        assert!(
            preservation.apply(|_| true).is_err(),
            "abstract types must agree"
        );
        let (preservation, _) = abstract_fixture(8);
        let _empty_reads = typed_reads::ReadScope::enter();
        assert!(
            preservation.apply(|_| true).is_err(),
            "no reconstruction when observations are absent"
        );
    }

    #[test]
    fn preserve_constructs_its_result_independently_of_the_annotation() {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let (mut preservation, goal) = fixture(8, false);
        assert_eq!(
            preserve_footprint(&preservation.separation, read_type(&goal).unwrap(), &goal),
            Some(goal)
        );
        let mut wrong_domain = preservation.clone();
        let Some((condition, true)) = wrong_domain.result.old_condition() else {
            panic!("distinct complete read domains");
        };
        let mut condition = condition.clone();
        let OldConditionTerm::PointerEqual(left, _) = &mut condition else {
            panic!("distinct complete read domains");
        };
        **left = (**left)
            .clone()
            .with_provenance(Address::symbolic(Variable(8_399_099)));
        wrong_domain.result = Proposition::condition_is(condition, true);
        assert!(
            wrong_domain
                .apply(|_| true)
                .unwrap_err()
                .contains("constructed result")
        );
        let result = &mut preservation.result;
        *result = Proposition::condition_is(
            OldConditionTerm::AddressEqual(
                Box::new(Address::symbolic(Variable(8_399_000))),
                Box::new(Address::symbolic(Variable(8_399_001))),
            ),
            true,
        );
        assert!(
            preservation
                .apply(|_| true)
                .unwrap_err()
                .contains("constructed result")
        );
    }

    #[test]
    fn an_observation_does_not_transfer_to_an_equal_memory_at_another_point() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let first = ExecutionState::new().with_memory(memory.clone());
        let second = ExecutionState::new().with_memory(memory);
        assert_eq!(first.memory(), second.memory());
        assert_ne!(first.program_point_id(), second.program_point_id());
        let address = Address::symbolic(Variable(8_399_011));
        let read = ProgramValue::bool_constant(true);
        let _scope = typed_reads::ReadScope::enter();
        typed_reads::record_at(&first.program_point(), &address, &read);
        assert_eq!(
            typed_reads::get_at(&first.program_point(), &address, ReadType::Boolean),
            Some(read)
        );
        assert!(
            typed_reads::get_at(&second.program_point(), &address, ReadType::Boolean).is_none()
        );
    }

    #[test]
    fn typed_read_observations_are_scoped_and_keep_the_selected_width() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = SymbolicMemory::new();
        let address = Address::symbolic(Variable(8_399_010));
        let kind = ReadType::Integer(MachineIntegerType::Int64);
        observe(&memory, &address, ProgramType::UInt64);
        assert!(typed_reads::get(&memory, &address, kind).is_none());
        {
            let _outer = typed_reads::ReadScope::enter();
            let value = observe(&memory, &address, ProgramType::UInt64);
            assert_eq!(
                typed_reads::get(&memory, &address, kind),
                Some(value.numeric_value().clone())
            );
            assert!(typed_reads::get(&memory, &address, ReadType::IntegerAddress).is_none());
            assert!(
                typed_reads::get(
                    &memory,
                    &address,
                    ReadType::Integer(MachineIntegerType::Int32)
                )
                .is_none()
            );
            {
                let _inner = typed_reads::ReadScope::enter();
                assert!(typed_reads::get(&memory, &address, kind).is_none());
                observe(&memory, &address, ProgramType::Int32);
            }
            assert_eq!(
                typed_reads::get(&memory, &address, kind),
                Some(value.numeric_value().clone())
            );
            assert!(
                typed_reads::get(
                    &memory,
                    &address,
                    ReadType::Integer(MachineIntegerType::Int32)
                )
                .is_none()
            );
        }
        assert!(typed_reads::get(&memory, &address, kind).is_none());
    }

    #[test]
    fn preserve_uses_the_indexed_integer_version_of_each_selected_endpoint() {
        for (kind, format) in [
            (LoadKind::Int128, MachineIntegerType::Int128),
            (LoadKind::UInt128, MachineIntegerType::UInt128),
        ] {
            let value = format
                .constant_value(
                    crate::kernel::MachineIntegerConstant::from_bits(format.format(), 1u128 << 127)
                        .unwrap(),
                )
                .unwrap();
            check_indexed_preservation(kind, format, 16, value);
        }
        check_indexed_preservation(
            LoadKind::Bits64,
            MachineIntegerType::Int64,
            8,
            ProgramValue::Int64(OldMachineTerm::int64_constant(i64::MIN)),
        );
        check_indexed_preservation(
            LoadKind::Bits64,
            MachineIntegerType::UInt64,
            8,
            ProgramValue::UInt64(OldMachineTerm::uint64_constant(1u64 << 63)),
        );
        check_indexed_preservation(
            LoadKind::UInt32,
            MachineIntegerType::UInt32,
            4,
            ProgramValue::UInt32(OldMachineTerm::uint32_constant(0x8000_0000)),
        );
        check_indexed_preservation(
            LoadKind::Int16,
            MachineIntegerType::Int16,
            2,
            ProgramValue::Int16(OldMachineTerm::narrow_constant(
                MachineIntegerType::Int16,
                0x8000,
            )),
        );
        check_indexed_preservation(
            LoadKind::UInt16,
            MachineIntegerType::UInt16,
            2,
            ProgramValue::UInt16(OldMachineTerm::narrow_constant(
                MachineIntegerType::UInt16,
                0x8000,
            )),
        );
        check_indexed_preservation(
            LoadKind::Int8,
            MachineIntegerType::Int8,
            1,
            ProgramValue::Int8(OldMachineTerm::narrow_constant(
                MachineIntegerType::Int8,
                0x80,
            )),
        );
        check_indexed_preservation(
            LoadKind::UInt8,
            MachineIntegerType::UInt8,
            1,
            ProgramValue::UInt8(OldMachineTerm::narrow_constant(
                MachineIntegerType::UInt8,
                0x80,
            )),
        );
    }

    fn check_indexed_preservation(
        load_kind: LoadKind,
        format: MachineIntegerType,
        bytes: u32,
        stored: ProgramValue,
    ) {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        let address = |name: &str| {
            Address::new(
                AddressBase::Concrete(name.into()),
                AddressOffset::constant(0),
            )
        };
        let slot = address("local:unsigned");
        let other = address("local:signed");
        let start = ExecutionState::new().with_memory(
            SymbolicMemory::new()
                .with_block("local:unsigned", bytes)
                .with_block("local:signed", 4),
        );
        let before = start
            .clone()
            .with_memory(start.memory().clone().store(slot.clone(), stored));
        let after = before.clone().with_memory(
            before
                .memory()
                .clone()
                .store(other, ProgramValue::Int32(OldMachineTerm::constant(1))),
        );
        let read = |state: &ExecutionState| {
            let version = state
                .program_point()
                .indexed_integer_version(&slot, load_kind)
                .unwrap();
            let path = crate::kernel::eval::evaluate_indexed_read(
                version,
                &state.program_point(),
                slot.clone(),
                format.program_type(),
                Default::default(),
                Vec::new(),
            );
            let ExpressionOutcome::Value(value) = path.outcome else {
                panic!("expected a typed integer read");
            };
            typed_reads::record_at(&state.program_point(), &slot, &value);
            integer_bits(value).unwrap()
        };
        let before_read = read(&before);
        let after_read = read(&after);
        assert_eq!(before_read, after_read);
        let footprint = crate::kernel::RegionFootprint::transition(
            "signed store".into(),
            &before,
            &after,
            &Vec::<ExecutionPureFact>::new(),
        );
        let comparison = match bytes {
            1 | 2 => MachineIntegerType::Int32,
            8 => MachineIntegerType::Int64,
            _ => format,
        };
        let comparison_type = ReadType::Integer(comparison);
        let operand = |bits| OldMachineTerm::machine_integer_cast(format, comparison, bits);
        let condition = match bytes {
            16 => OldConditionTerm::integer_equal(
                IntegerTerm::from_machine(format, after_read.clone()).unwrap(),
                IntegerTerm::from_machine(format, before_read.clone()).unwrap(),
            ),
            8 => OldConditionTerm::Compare {
                format: comparison,
                relation: CompareRelation::Equal,
                left: Box::new(after_read.clone()),
                right: Box::new(before_read.clone()),
            },
            _ => OldConditionTerm::machine_compare(
                comparison,
                CompareRelation::Equal,
                operand(after_read.clone()),
                operand(before_read.clone()),
            ),
        };
        let expected = Proposition::condition_is(condition, true);
        let observed = observation_type(comparison_type, bytes, &expected).unwrap();
        let observed_format = if bytes == 8 { comparison } else { format };
        assert_eq!(observed, ReadType::Integer(observed_format));
        if bytes <= 8 {
            let derived =
                observation_equality(&footprint, slot.clone(), observed, comparison_type).unwrap();
            let Proposition::ConditionIs(stored, true) = &derived else {
                panic!("expected stored word equality");
            };
            assert!(!stored.root().unwrap().has_cached_native_argument());
            assert_eq!(derived, expected);
        }
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Footprint(footprint)),
            right: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                slot,
                0u32.into(),
                1u32.into(),
                bytes,
            ))),
        };
        assert_eq!(
            apply(&separation, None, &expected, None, |fact| fact
                == &separation),
            Ok(())
        );
        if bytes < 4 {
            let other_format = match format {
                MachineIntegerType::Int8 => MachineIntegerType::UInt8,
                MachineIntegerType::UInt8 => MachineIntegerType::Int8,
                MachineIntegerType::Int16 => MachineIntegerType::UInt16,
                MachineIntegerType::UInt16 => MachineIntegerType::Int16,
                _ => unreachable!("narrow test format"),
            };
            let mixed = Proposition::condition_is(
                OldConditionTerm::equal(
                    operand(after_read),
                    OldMachineTerm::machine_integer_cast(other_format, comparison, before_read),
                ),
                true,
            );
            assert_eq!(observation_type(comparison_type, bytes, &mixed), None);
            assert!(apply(&separation, None, &mixed, None, |fact| fact == &separation).is_err());
        }
    }

    #[test]
    fn preserve_checks_exact_footprint_endpoints_and_available_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = typed_reads::ReadScope::enter();
        for cached in [false, true] {
            let (preservation, goal) = fixture(8, cached);
            assert_eq!(preservation.apply(|_| true).unwrap(), goal);
            assert!(preservation.apply(|_| false).is_err());
            let mut partial = preservation.clone();
            let Proposition::ResourceSeparate { right, .. } = &mut partial.separation else {
                unreachable!()
            };
            let Resource::Memory(range) = right.as_ref() else {
                unreachable!()
            };
            let (address, _) = range.byte_footprint();
            **right = Resource::Memory(MemoryRange::new_with_element_width(
                address,
                0u32.into(),
                1u32.into(),
                1,
            ));
            assert!(partial.apply(|_| true).is_err());
            for corruption in 0..3 {
                let mut broken = preservation.clone();
                let Proposition::ResourceSeparate { left, right } = &mut broken.separation else {
                    unreachable!()
                };
                if corruption == 0 {
                    **right = Resource::Memory(MemoryRange::new_with_element_width(
                        Address::symbolic(Variable(8_310_099)),
                        0u32.into(),
                        1u32.into(),
                        C_POINTER_BYTE_WIDTH,
                    ));
                } else {
                    let Resource::Footprint(fp) = left.as_ref() else {
                        unreachable!()
                    };
                    let mut before = fp.before.clone();
                    let mut after = fp.after.clone();
                    if corruption == 1 {
                        before = SymbolicMemory::new();
                    } else {
                        after = SymbolicMemory::new();
                    }
                    let entry = ExecutionState::new().with_memory(before);
                    let exit = entry.clone().with_memory(after);
                    **left = Resource::Footprint(crate::kernel::RegionFootprint::transition(
                        "wrong endpoint".into(),
                        &entry,
                        &exit,
                        &Vec::<ExecutionPureFact>::new(),
                    ));
                }
                assert!(
                    broken.apply(|_| true).is_err(),
                    "corruption {corruption}, cached={cached}"
                );
            }
        }
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/proof/preservation.rs");
}
