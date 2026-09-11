use super::*;

#[cfg(test)]
mod tests;

const SURFACE_SYNTHESIS_WORK_LIMIT: usize = 16_384;
pub(super) const SURFACE_SYNTHESIS_DEPTH_LIMIT: usize = 128;

#[derive(Clone, Copy)]
struct SurfaceSynthesisBudget {
    remaining_work: usize,
    depth: usize,
    exhausted_category: Option<&'static str>,
}

thread_local! {
    static SYNTHESIS_QUALIFIED_SOURCES: std::cell::RefCell<Option<SurfacePropositionMap>> = const { std::cell::RefCell::new(None) };
    static SYNTHESIS_ENTRY_STATE: std::cell::RefCell<Option<CState>> = const { std::cell::RefCell::new(None) };
    /// A second reference state, named by its own recorded snapshot selector
    /// rather than by `old(...)`. A loop back edge needs this: the iteration
    /// entry is neither the function entry nor the current state, and the
    /// ranking members compare the two ends of one iteration.
    static SYNTHESIS_SNAPSHOT_STATE: std::cell::RefCell<Option<(CState, SnapshotSelector)>> = const { std::cell::RefCell::new(None) };
    static SURFACE_SYNTHESIS_BUDGET: std::cell::RefCell<Option<SurfaceSynthesisBudget>> =
        const { std::cell::RefCell::new(None) };
    static LAST_SURFACE_SYNTHESIS_EXHAUSTION: std::cell::Cell<Option<&'static str>> =
        const { std::cell::Cell::new(None) };
    static SURFACE_SYNTHESIS_BITVECTOR_NESTING: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

pub(super) struct QualifiedSynthesisScope(Option<SurfacePropositionMap>);

impl QualifiedSynthesisScope {
    pub(super) fn enter(sources: &SurfacePropositionMap) -> Self {
        Self(SYNTHESIS_QUALIFIED_SOURCES.with(|slot| slot.replace(Some(sources.clone()))))
    }
}

impl Drop for QualifiedSynthesisScope {
    fn drop(&mut self) {
        SYNTHESIS_QUALIFIED_SOURCES.with(|slot| slot.replace(self.0.take()));
    }
}

struct SynthesisEntryScope(Option<CState>);
impl Drop for SynthesisEntryScope {
    fn drop(&mut self) {
        SYNTHESIS_ENTRY_STATE.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

pub(in crate::surface) fn synthesize_surface_proposition_at_entry_and_post(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    entry: &CState,
    post: &CState,
) -> Option<ClickProposition> {
    let _entry =
        SynthesisEntryScope(SYNTHESIS_ENTRY_STATE.with(|slot| slot.replace(Some(entry.clone()))));
    synthesize_surface_proposition(proposition, parameters, arguments, post)
}

/// As above, plus one further reference state addressed by a recorded
/// snapshot selector. A value the current state no longer holds but the
/// snapshot state does reads as `at(<selector>, name)`, which is the same
/// spelling loop-body premises already use, so the synthesized form lowers
/// back to exactly this term at the snapshot the selector names.
pub(in crate::surface) fn synthesize_surface_proposition_at_entry_post_and_snapshot(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    entry: &CState,
    post: &CState,
    snapshot: Option<(&CState, &SnapshotSelector)>,
) -> Option<ClickProposition> {
    let _snapshot = SynthesisSnapshotScope(SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
        slot.replace(snapshot.map(|(state, selector)| (state.clone(), selector.clone())))
    }));
    synthesize_surface_proposition_at_entry_and_post(
        proposition,
        parameters,
        arguments,
        entry,
        post,
    )
}

struct SynthesisSnapshotScope(Option<(CState, SnapshotSelector)>);
impl Drop for SynthesisSnapshotScope {
    fn drop(&mut self) {
        SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

/// The `at(<selector>, name)` spelling of a term the snapshot state's own
/// scalar local holds exactly. Only a term the current state cannot name
/// reaches this, so the snapshot spelling never shadows a current name.
fn synthesize_snapshot_local(term: &Bitvector32Term) -> Option<ContractExpression> {
    SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
        let slot = slot.borrow();
        let (state, selector) = slot.as_ref()?;
        let (name, _) = state.locals().object_values().find(|(_, value)| {
            matches!(
                value,
                CValue::Int16(local)
                    | CValue::Int32(local)
                    | CValue::UInt8(local)
                    | CValue::UInt16(local)
                    | CValue::UInt32(local)
                    | CValue::Int64(local)
                    | CValue::UInt64(local)
                    if local == term
            )
        })?;
        Some(ContractExpression::At {
            selector: selector.clone(),
            expression: Box::new(ContractExpression::CFragment(CExpression::Variable(
                name.to_string(),
            ))),
        })
    })
}

struct SurfaceSynthesisScope(Option<SurfaceSynthesisBudget>);

impl SurfaceSynthesisScope {
    fn enter() -> Self {
        LAST_SURFACE_SYNTHESIS_EXHAUSTION.with(|last| last.set(None));
        let previous = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            slot.replace(Some(SurfaceSynthesisBudget {
                remaining_work: SURFACE_SYNTHESIS_WORK_LIMIT,
                depth: 0,
                exhausted_category: None,
            }))
        });
        Self(previous)
    }
}

impl Drop for SurfaceSynthesisScope {
    fn drop(&mut self) {
        let exhausted = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let current = slot.replace(self.0.take());
            current.and_then(|budget| budget.exhausted_category)
        });
        if exhausted.is_some() {
            LAST_SURFACE_SYNTHESIS_EXHAUSTION.with(|last| last.set(exhausted));
        }
    }
}

struct SurfaceSynthesisFrame {
    counted: bool,
}

struct SurfaceBitvectorFrame {
    outermost: bool,
}

impl SurfaceBitvectorFrame {
    fn enter() -> Self {
        let outermost = SURFACE_SYNTHESIS_BITVECTOR_NESTING.with(|depth| {
            let outermost = depth.get() == 0;
            depth.set(depth.get() + 1);
            outermost
        });
        Self { outermost }
    }

    fn is_outermost(&self) -> bool {
        self.outermost
    }
}

impl Drop for SurfaceBitvectorFrame {
    fn drop(&mut self) {
        SURFACE_SYNTHESIS_BITVECTOR_NESTING.with(|depth| {
            depth.set(depth.get().saturating_sub(1));
        });
    }
}

impl SurfaceSynthesisFrame {
    fn enter(category: &'static str) -> Option<Self> {
        let counted = SURFACE_SYNTHESIS_BUDGET.with(|slot| {
            let mut slot = slot.borrow_mut();
            let Some(budget) = slot.as_mut() else {
                return Some(false);
            };
            if budget.remaining_work == 0 || budget.depth >= SURFACE_SYNTHESIS_DEPTH_LIMIT {
                budget.exhausted_category.get_or_insert(category);
                return None;
            }
            budget.remaining_work -= 1;
            budget.depth += 1;
            Some(true)
        })?;
        Some(Self { counted })
    }
}

impl Drop for SurfaceSynthesisFrame {
    fn drop(&mut self) {
        if self.counted {
            SURFACE_SYNTHESIS_BUDGET.with(|slot| {
                if let Some(budget) = slot.borrow_mut().as_mut() {
                    budget.depth = budget.depth.saturating_sub(1);
                }
            });
        }
    }
}

fn consume_surface_synthesis_work(category: &'static str) -> bool {
    SURFACE_SYNTHESIS_BUDGET.with(|slot| {
        let mut slot = slot.borrow_mut();
        let Some(budget) = slot.as_mut() else {
            return true;
        };
        if budget.remaining_work == 0 {
            budget.exhausted_category.get_or_insert(category);
            return false;
        }
        budget.remaining_work -= 1;
        true
    })
}

fn record_surface_synthesis_exhaustion(category: &'static str) {
    SURFACE_SYNTHESIS_BUDGET.with(|slot| {
        if let Some(budget) = slot.borrow_mut().as_mut() {
            budget.exhausted_category.get_or_insert(category);
        }
    });
}

fn bitvector_term_exceeds_depth_limit(root: &Bitvector32Term) -> bool {
    let mut pending = vec![(root, 0usize)];
    while let Some((term, depth)) = pending.pop() {
        if depth >= SURFACE_SYNTHESIS_DEPTH_LIMIT.saturating_sub(1) {
            return true;
        }
        match term {
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::UnsignedDivide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::UnsignedRemainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::LogicalShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right)
            | Bitvector32Term::Int64Add(left, right)
            | Bitvector32Term::Int64Subtract(left, right)
            | Bitvector32Term::Int64Multiply(left, right)
            | Bitvector32Term::Int64Divide(left, right)
            | Bitvector32Term::Int64Remainder(left, right)
            | Bitvector32Term::Int64ShiftLeft(left, right)
            | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
            | Bitvector32Term::Int64BitwiseAnd(left, right)
            | Bitvector32Term::Int64BitwiseOr(left, right)
            | Bitvector32Term::Int64BitwiseXor(left, right)
            | Bitvector32Term::UInt64Add(left, right)
            | Bitvector32Term::UInt64Subtract(left, right)
            | Bitvector32Term::UInt64Multiply(left, right)
            | Bitvector32Term::UInt64Divide(left, right)
            | Bitvector32Term::UInt64Remainder(left, right)
            | Bitvector32Term::UInt64ShiftLeft(left, right)
            | Bitvector32Term::UInt64LogicalShiftRight(left, right)
            | Bitvector32Term::UInt64BitwiseAnd(left, right)
            | Bitvector32Term::UInt64BitwiseOr(left, right)
            | Bitvector32Term::UInt64BitwiseXor(left, right) => {
                pending.push((left, depth + 1));
                pending.push((right, depth + 1));
            }
            Bitvector32Term::Float32Binary { left, right, .. }
            | Bitvector32Term::Float64Binary { left, right, .. } => {
                pending.push((left, depth + 1));
                pending.push((right, depth + 1));
            }
            Bitvector32Term::BitwiseNot(value)
            | Bitvector32Term::Float32Negate(value)
            | Bitvector32Term::Float64Negate(value)
            | Bitvector32Term::Int64From32(value)
            | Bitvector32Term::Int64FromUInt32(value)
            | Bitvector32Term::UInt64From32(value)
            | Bitvector32Term::UInt32From64(value)
            | Bitvector32Term::UInt64FromInt32(value)
            | Bitvector32Term::UInt64FromInt64(value)
            | Bitvector32Term::Int64BitwiseNot(value)
            | Bitvector32Term::UInt64BitwiseNot(value) => {
                pending.push((value, depth + 1));
            }
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => {
                pending.push((then_term, depth + 1));
                pending.push((else_term, depth + 1));
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                pending.push((start, depth + 1));
                pending.push((end, depth + 1));
                pending.push((initial, depth + 1));
                pending.push((body, depth + 1));
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments.iter().map(|argument| (argument, depth + 1)));
            }
            Bitvector32Term::ClickFunctionApplication { .. }
            | Bitvector32Term::AlgebraicMatch { .. }
            | Bitvector32Term::IntegerToMachine { .. } => {}
            Bitvector32Term::MemoryLoad(_, pointer) => {
                if let PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. } = &pointer.offset
                {
                    pending.push((value, depth + 1));
                }
            }
            Bitvector32Term::PointerAddress(pointer) => {
                if let PointerOffsetTerm::Int32Scaled { value, .. }
                | PointerOffsetTerm::Int64Scaled { value, .. } = &pointer.offset
                {
                    pending.push((value, depth + 1));
                }
            }
            Bitvector32Term::Constant(_)
            | Bitvector32Term::Int64Constant(_)
            | Bitvector32Term::UInt64Constant(_)
            | Bitvector32Term::Variable(_) => {}
        }
    }
    false
}

pub(super) fn surface_synthesis_exhaustion_description() -> Option<String> {
    LAST_SURFACE_SYNTHESIS_EXHAUSTION.with(|last| {
        last.get().map(|category| {
            format!("Surface Click reconstruction exhausted its bounded {category} search")
        })
    })
}

pub(super) fn surface_synthesis_failure(prefix: &str, kernel: &Proposition) -> String {
    surface_synthesis_exhaustion_description()
        .map(|exhaustion| format!("{prefix}: {exhaustion}"))
        .unwrap_or_else(|| format!("{prefix}: {kernel:?}"))
}

pub(in crate::surface) fn synthesize_surface_proposition(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Option<ClickProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    synthesize_surface_proposition_with_bound_variables(
        proposition,
        parameters,
        arguments,
        state,
        &BTreeMap::new(),
    )
}

pub(in crate::surface) fn synthesize_surface_proposition_with_bound_variable_names(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    synthesize_surface_proposition_with_bound_variables(
        proposition,
        parameters,
        arguments,
        state,
        bound_variables,
    )
}

#[inline(never)]
fn synthesize_surface_proposition_with_bound_variables(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    let _frame = SurfaceSynthesisFrame::enter("proposition")?;
    match proposition {
        Proposition::And(left, right)
        | Proposition::Or(left, right)
        | Proposition::Implies(left, right) => {
            let construct: fn(Box<ClickProposition>, Box<ClickProposition>) -> ClickProposition =
                match proposition {
                    Proposition::And(..) => ClickProposition::And,
                    Proposition::Or(..) => ClickProposition::Or,
                    Proposition::Implies(..) => ClickProposition::Implies,
                    _ => unreachable!(),
                };
            Some(construct(
                Box::new(synthesize_surface_proposition_with_bound_variables(
                    left,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?),
                Box::new(synthesize_surface_proposition_with_bound_variables(
                    right,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?),
            ))
        }
        Proposition::ForAll { .. } | Proposition::Exists { .. } => {
            synthesize_surface_quantified_proposition(
                proposition,
                parameters,
                arguments,
                state,
                bound_variables,
            )
        }
        _ => synthesize_surface_atomic_proposition(
            proposition,
            parameters,
            arguments,
            state,
            bound_variables,
        ),
    }
}

#[inline(never)]
fn synthesize_surface_quantified_proposition(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    match proposition {
        Proposition::ForAll { var, sort, body }
        | Proposition::Exists {
            var, sort, body, ..
        } => {
            if *sort != Sort::CInt32 {
                return None;
            }
            let mut suffix = bound_variables.len();
            let name = loop {
                let candidate = format!("__click_q{suffix}");
                let conflicts = parameters
                    .iter()
                    .any(|parameter| parameter.name() == candidate)
                    || state
                        .locals()
                        .object_values()
                        .any(|(name, _)| name == candidate)
                    || bound_variables.values().any(|name| name == &candidate);
                if !conflicts {
                    break candidate;
                }
                suffix += 1;
            };
            let mut body_variables = bound_variables.clone();
            body_variables.insert(*var, name.clone());
            let body = Box::new(synthesize_surface_proposition_with_bound_variables(
                body,
                parameters,
                arguments,
                state,
                &body_variables,
            )?);
            Some(match proposition {
                Proposition::ForAll { .. } => ClickProposition::ForAll {
                    click_type: ClickType::C(C0Type::Int32),
                    name,
                    body,
                },
                Proposition::Exists { .. } => ClickProposition::Exists {
                    click_type: ClickType::C(C0Type::Int32),
                    name,
                    body,
                },
                _ => unreachable!(),
            })
        }
        _ => unreachable!("non-quantified proposition dispatched to binder synthesis"),
    }
}

/// `loadable(<base>[0..n])`: the whole named region, its byte count a
/// multiple of the `int32` cell the segment counts in. The start index is
/// zero, so the pointer's own offset is folded into the printed base.
fn synthesize_zero_based_loadable_segment(
    base: &Pointer,
    bytes: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    let element_count = if let Some(byte_count) = bytes.as_const() {
        if !byte_count.is_multiple_of(4) {
            return None;
        }
        CExpression::Value(int32(byte_count / 4))
    } else if let Bitvector32Term::Multiply(left, right) = bytes {
        let elements = if right.as_const() == Some(4) {
            left.as_ref()
        } else if left.as_const() == Some(4) {
            right.as_ref()
        } else {
            return None;
        };
        contract_expression_to_c_fragment(&synthesize_surface_bitvector(
            elements,
            parameters,
            arguments,
            state,
            bound_variables,
        )?)?
    } else {
        return None;
    };
    let semantic_base =
        synthesize_surface_pointer(base, parameters, arguments, state, bound_variables)?;
    let surface_base = synthesize_surface_pointer_offset(
        &base.offset,
        parameters,
        arguments,
        state,
        bound_variables,
    )
    .unwrap_or_else(|| ContractExpression::CFragment(semantic_base.clone()));
    Some(ClickProposition::Loadable {
        segment: ContractSegment {
            state: ContractSegmentState::Current,
            base: semantic_base,
            start: CExpression::Value(int32(0)),
            end: element_count.clone(),
            surface: ContractSegmentSurface::Range {
                base: surface_base,
                start: ContractExpression::CFragment(CExpression::Value(int32(0))),
                end: ContractExpression::CFragment(element_count),
            },
        },
    })
}

/// `loadable(p[a..b])`: a range of one named pointer, the form a contract
/// writes when neither end of the range is the object's own start.
///
/// A call requirement lowered from such a clause keeps the written ends: its
/// byte count is `(b - a)` scaled by the element, and its base pointer is
/// `p` displaced by `a` elements. Both survive only if the range is spelled
/// back over the same named pointer, so this reads `a` out of the pointer
/// offset rather than folding it into the base as the zero-based form does.
/// A spelling whose ends differ re-lowers to a different byte count, which
/// is exactly what the caller's round-trip check rejects.
fn synthesize_named_range_loadable_segment(
    base: &Pointer,
    bytes: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    // The byte count as the segment lowering builds it: the element span,
    // scaled by the element width when that is not one byte.
    let (span, scale) = match bytes {
        Bitvector32Term::Multiply(left, right) => match (left.as_const(), right.as_const()) {
            (_, Some(scale)) => (left.as_ref(), scale),
            (Some(scale), _) => (right.as_ref(), scale),
            _ => return None,
        },
        span => (span, 1),
    };
    let Bitvector32Term::Subtract(end, start) = span else {
        return None;
    };
    // The named pointer this range starts from, and the element index the
    // requirement's base pointer sits at within it.
    let named =
        named_pointer_bases(parameters, arguments, state).find_map(|(name, pointer, width)| {
            (width == scale && base.element_index_from_base_with_width(&pointer, width)? == **start)
                .then_some(name)
        })?;
    let start = contract_expression_to_c_fragment(&synthesize_surface_bitvector(
        start,
        parameters,
        arguments,
        state,
        bound_variables,
    )?)?;
    let end = contract_expression_to_c_fragment(&synthesize_surface_bitvector(
        end,
        parameters,
        arguments,
        state,
        bound_variables,
    )?)?;
    let named = CExpression::Variable(named);
    Some(ClickProposition::Loadable {
        segment: ContractSegment {
            state: ContractSegmentState::Current,
            base: named.clone(),
            start: start.clone(),
            end: end.clone(),
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::CFragment(named),
                start: ContractExpression::CFragment(start),
                end: ContractExpression::CFragment(end),
            },
        },
    })
}

/// Every pointer this proof context can name, with the element width its
/// declared type steps by: the call's own parameters first, then the state's
/// pointer locals. The walk is over those two named lists only.
fn named_pointer_bases<'a>(
    parameters: &'a [syntax::C0Parameter],
    arguments: &'a [CExpression],
    state: &'a CState,
) -> impl Iterator<Item = (String, crate::kernel::CPointerValue, u32)> + 'a {
    parameters
        .iter()
        .zip(arguments)
        .filter_map(|(parameter, argument)| {
            let CExpression::Value(CValue::Pointer(base)) = argument else {
                return None;
            };
            let width = parameter
                .c_type()
                .pointee_type()?
                .to_kernel_type()
                .byte_width();
            Some((parameter.name().to_string(), base.clone(), width))
        })
        .chain(state.locals().object_values().filter_map(|(name, value)| {
            let CValue::Pointer(base) = value else {
                return None;
            };
            let width = base.c_type().pointee_type()?.byte_width();
            Some((name.to_string(), base.clone(), width))
        }))
}

/// Synthesize the internal equation emitted when a memory read is assigned a
/// registered load identity. The variable is not a source-level identifier;
/// spell both sides through the registered pointer, anchored at the snapshot
/// named by the load.  Keeping this separate from ordinary bitvector
/// synthesis is important: the latter may deliberately resolve a load to a
/// current-state value, while this equation must retain its memory epoch.
fn synthesize_load_defining_equation(
    variable: &Variable,
    memory: &crate::kernel::SharedCMemory,
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    let (registered_memory, registered_pointer) =
        crate::kernel::registered_load_for_variable(variable)?;
    // The defining equation carries the canonical snapshot that was recorded
    // with this variable. A merely equivalent load from another memory would
    // erase the epoch the equation is required to preserve.
    if registered_memory != *memory || registered_pointer != *pointer {
        return None;
    }

    let synthesize_at = |snapshot: &CState| {
        let load = registered_load_in_state(variable, snapshot)?;
        // Let the ordinary load spelling select a qualified source, an exact
        // local cell, a field, or the pointer/load fallback. It receives the
        // snapshot-specific load above, so the selected source cannot drift
        // to another epoch while the defining equation is presented.
        let left = synthesize_surface_bitvector(
            &Bitvector32Term::Variable(*variable),
            parameters,
            arguments,
            snapshot,
            bound_variables,
        )?;
        let right =
            synthesize_surface_bitvector(&load, parameters, arguments, snapshot, bound_variables)?;
        Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        })
    };

    if registered_load_in_state(variable, state).is_some() {
        return synthesize_at(state);
    }
    if let Some(entry) = SYNTHESIS_ENTRY_STATE.with(|slot| slot.borrow().clone())
        && registered_load_in_state(variable, &entry).is_some()
    {
        return synthesize_at(&entry).map(|proposition| ClickProposition::At {
            selector: SnapshotSelector::ProgramPoint(ProgramPointRef {
                region: CodeRegionRef::Function,
                kind: ProgramPointKind::Entry,
            }),
            proposition: Box::new(proposition),
        });
    }
    SYNTHESIS_SNAPSHOT_STATE.with(|slot| {
        let slot = slot.borrow();
        let (snapshot, selector) = slot.as_ref()?;
        registered_load_in_state(variable, snapshot)?;
        synthesize_at(snapshot).map(|proposition| ClickProposition::At {
            selector: selector.clone(),
            proposition: Box::new(proposition),
        })
    })
}

// Large leaf temporaries must not occupy every recursive connective frame.
#[inline(never)]
fn synthesize_surface_atomic_proposition(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ClickProposition> {
    if let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
        proposition
        && let (Bitvector32Term::Variable(variable), Bitvector32Term::MemoryLoad(memory, pointer)) =
            (left.as_ref(), right.as_ref())
        && crate::kernel::is_load_variable(variable)
    {
        return synthesize_load_defining_equation(
            variable,
            memory,
            pointer,
            parameters,
            arguments,
            state,
            bound_variables,
        );
    }
    if let Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) = proposition {
        fn sequence(
            value: &crate::kernel::SequenceTerm,
            parameters: &[syntax::C0Parameter],
            arguments: &[CExpression],
            state: &CState,
            bound: &BTreeMap<Variable, String>,
        ) -> Option<ContractExpression> {
            let _frame = SurfaceSynthesisFrame::enter("sequence")?;
            Some(match value.node.as_ref() {
                crate::kernel::SequenceTermNode::Literal(values) => {
                    ContractExpression::SequenceLiteral(
                        values
                            .iter()
                            .map(|value| {
                                let CValue::Int32(value) = value else {
                                    return None;
                                };
                                synthesize_surface_bitvector(
                                    value, parameters, arguments, state, bound,
                                )
                            })
                            .collect::<Option<Vec<_>>>()?,
                    )
                }
                crate::kernel::SequenceTermNode::Concat(left, right) => {
                    ContractExpression::SequenceConcat(
                        Box::new(sequence(left, parameters, arguments, state, bound)?),
                        Box::new(sequence(right, parameters, arguments, state, bound)?),
                    )
                }
            })
        }
        return Some(ClickProposition::Comparison {
            left: sequence(left, parameters, arguments, state, bound_variables)?,
            operator: ComparisonOperator::Equal,
            right: sequence(right, parameters, arguments, state, bound_variables)?,
        });
    }
    // A declared predicate call starts with its hidden logical resource-state
    // snapshot. Its source call does not write that argument. Each array-ref
    // argument then lowers to a (memory, pointer) term pair and each value
    // argument to a single value term, so the remaining kernel argument list
    // reads back unambiguously: a `CMemory` term always opens an array-ref
    // pair. The snapshot the pair names is not written here — the current
    // memory needs no form, and every caller re-lowers the candidate and
    // compares it to the kernel fact, so a candidate built against the wrong
    // snapshot is rejected by that round trip rather than by a guess made
    // here.
    if let Proposition::Predicate {
        name,
        arguments: kernel_arguments,
    } = proposition
    {
        let mut call_arguments = Vec::new();
        let mut index = usize::from(matches!(kernel_arguments.first(), Some(Term::CState(_))));
        while index < kernel_arguments.len() {
            match &kernel_arguments[index] {
                Term::CMemory(_) => {
                    let Some(Term::CValue(CValue::Pointer(pointer))) =
                        kernel_arguments.get(index + 1)
                    else {
                        return None;
                    };
                    call_arguments.push(ContractExpression::CFragment(synthesize_surface_pointer(
                        pointer,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?));
                    index += 2;
                }
                Term::CValue(CValue::Pointer(pointer)) => {
                    call_arguments.push(ContractExpression::CFragment(synthesize_surface_pointer(
                        pointer,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?));
                    index += 1;
                }
                Term::CValue(
                    CValue::Int16(value)
                    | CValue::Int32(value)
                    | CValue::UInt8(value)
                    | CValue::UInt16(value),
                ) => {
                    call_arguments.push(synthesize_surface_bitvector(
                        value,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?);
                    index += 1;
                }
                _ => return None,
            }
        }
        return Some(ClickProposition::PredicateCall {
            name: name.clone(),
            arguments: call_arguments,
        });
    }
    if let Proposition::CResourceSeparate { left, right } = proposition {
        return Some(ClickProposition::Separate {
            left: synthesize_surface_resource_subject(
                left,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
            right: synthesize_surface_resource_subject(
                right,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
        });
    }
    if let Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
    } = proposition
    {
        let loadable = synthesize_zero_based_loadable_segment(
            base,
            bytes,
            parameters,
            arguments,
            state,
            bound_variables,
        )
        .or_else(|| {
            synthesize_named_range_loadable_segment(
                base,
                bytes,
                parameters,
                arguments,
                state,
                bound_variables,
            )
        })?;
        let at_entry = SYNTHESIS_ENTRY_STATE.with(|slot| {
            slot.borrow()
                .as_ref()
                .is_some_and(|entry| entry.memory() == memory && state.memory() != entry.memory())
        });
        return Some(if at_entry {
            ClickProposition::At {
                selector: SnapshotSelector::ProgramPoint(ProgramPointRef {
                    region: CodeRegionRef::Function,
                    kind: ProgramPointKind::Entry,
                }),
                proposition: Box::new(loadable),
            }
        } else {
            loadable
        });
    }
    if let Proposition::Not(body) = proposition {
        return Some(ClickProposition::Not(Box::new(
            synthesize_surface_proposition_with_bound_variables(
                body,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
        )));
    }
    let Proposition::ConditionIs(condition, value) = proposition else {
        return None;
    };
    if let ConditionTerm::Bitvector32SignedAddOverflows(left, right) = condition
        && !value
    {
        return Some(ClickProposition::Defined {
            expression: synthesize_surface_bitvector(
                &Bitvector32Term::Add(left.clone(), right.clone()),
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
        });
    }
    if let ConditionTerm::Constant(condition) = condition {
        return Some(ClickProposition::Comparison {
            left: ContractExpression::CFragment(CExpression::Value(int32(0))),
            operator: if condition == value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: ContractExpression::CFragment(CExpression::Value(int32(0))),
        });
    }
    if let ConditionTerm::PointerOffsetEqual(left, right) = condition {
        return Some(ClickProposition::Comparison {
            left: synthesize_surface_pointer_offset(
                left,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: synthesize_surface_pointer_offset(
                right,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
        });
    }
    if let ConditionTerm::PointerEqual(left, right) = condition {
        return Some(ClickProposition::Comparison {
            left: synthesize_surface_pointer_expression(
                left,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
            operator: if *value {
                ComparisonOperator::Equal
            } else {
                ComparisonOperator::NotEqual
            },
            right: synthesize_surface_pointer_expression(
                right,
                parameters,
                arguments,
                state,
                bound_variables,
            )?,
        });
    }
    let (left, operator, right) = match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector64SignedLessThan(left, right)
        | ConditionTerm::Bitvector64UnsignedLessThan(left, right) => {
            (left, ComparisonOperator::LessThan, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64SignedLessEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => {
            (left, ComparisonOperator::LessEqual, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => {
            (left, ComparisonOperator::GreaterThan, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => {
            (left, ComparisonOperator::GreaterEqual, right)
        }
        ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector64Equal(left, right) => (left, ComparisonOperator::Equal, right),
        _ => return None,
    };
    let surface_left =
        synthesize_surface_bitvector(left, parameters, arguments, state, bound_variables);
    let surface_right =
        synthesize_surface_bitvector(right, parameters, arguments, state, bound_variables);
    let comparison = ClickProposition::Comparison {
        left: surface_left?,
        operator,
        right: surface_right?,
    };
    if *value {
        Some(comparison)
    } else if operator == ComparisonOperator::Equal {
        let ClickProposition::Comparison { left, right, .. } = comparison else {
            unreachable!()
        };
        Some(ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::NotEqual,
            right,
        })
    } else {
        Some(ClickProposition::Not(Box::new(comparison)))
    }
}

fn synthesize_surface_resource_subject(
    resource: &CResource,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ResourceSubject> {
    let _frame = SurfaceSynthesisFrame::enter("resource")?;
    let CResource::Memory(range) = resource else {
        return None;
    };
    let semantic_base =
        synthesize_surface_pointer(range.base(), parameters, arguments, state, bound_variables)?;
    let surface_base = synthesize_surface_pointer_offset(
        &range.base().offset,
        parameters,
        arguments,
        state,
        bound_variables,
    )
    .unwrap_or_else(|| ContractExpression::CFragment(semantic_base.clone()));
    let surface_start =
        synthesize_surface_bitvector(range.start(), parameters, arguments, state, bound_variables)?;
    let surface_end =
        synthesize_surface_bitvector(range.end(), parameters, arguments, state, bound_variables)?;
    let start = contract_expression_to_c_fragment(&surface_start)?;
    let end = contract_expression_to_c_fragment(&surface_end)?;
    Some(ResourceSubject::Memory(ContractSegment {
        state: ContractSegmentState::Current,
        base: semantic_base,
        start,
        end,
        surface: ContractSegmentSurface::Range {
            base: surface_base,
            start: surface_start,
            end: surface_end,
        },
    }))
}

/// Spells one certified equality whose operands were read from different
/// snapshots, such as a callee postcondition relating a cell after
/// the call to its value before it. Each operand is anchored at the first
/// listed point where it denotes a source expression; the caller lists the
/// recorded statement entries nearest first and must re-lower the result to
/// confirm it denotes exactly this kernel fact.
pub(in crate::surface) fn synthesize_surface_equality_across_points(
    proposition: &Proposition,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    points: &[(ProgramPointRef, &CState)],
) -> Option<ClickProposition> {
    let _scope = SurfaceSynthesisScope::enter();
    let Proposition::ConditionIs(condition, true) = proposition else {
        return None;
    };
    let bound_variables = BTreeMap::new();
    let anchored = |synthesize: &dyn Fn(&CState) -> Option<ContractExpression>| {
        points.iter().find_map(|(point, state)| {
            let expression = synthesize(state)?;
            Some(ContractExpression::At {
                selector: SnapshotSelector::ProgramPoint(point.clone()),
                expression: Box::new(expression),
            })
        })
    };
    let (left, right) = match condition {
        ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector64Equal(left, right) => (
            anchored(&|state| {
                synthesize_surface_bitvector(left, parameters, arguments, state, &bound_variables)
            })?,
            anchored(&|state| {
                synthesize_surface_bitvector(right, parameters, arguments, state, &bound_variables)
            })?,
        ),
        ConditionTerm::PointerOffsetEqual(left, right) => (
            anchored(&|state| {
                synthesize_surface_pointer_offset(
                    left,
                    parameters,
                    arguments,
                    state,
                    &bound_variables,
                )
            })?,
            anchored(&|state| {
                synthesize_surface_pointer_offset(
                    right,
                    parameters,
                    arguments,
                    state,
                    &bound_variables,
                )
            })?,
        ),
        _ => return None,
    };
    Some(ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    })
}

pub(super) fn synthesize_surface_pointer_offset(
    term: &PointerOffsetTerm,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("pointer-offset")?;
    for (parameter, argument) in parameters.iter().zip(arguments) {
        if let CExpression::Value(CValue::Pointer(pointer)) = argument
            && pointer.offset == *term
        {
            return Some(ContractExpression::CFragment(CExpression::Variable(
                parameter.name().to_string(),
            )));
        }
    }
    if let Some(field) =
        synthesize_parameter_field_pointer_value(term, parameters, arguments, state)
    {
        return Some(field);
    }
    match term {
        // A pointer-width load variable denotes a pointer field read at any
        // point in its epoch; spell it through that load so the form keeps
        // its pointer type.
        PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: 4,
        } if matches!(value.as_ref(), Bitvector32Term::Variable(_)) => {
            let Bitvector32Term::Variable(variable) = value.as_ref() else {
                unreachable!()
            };
            let load = registered_load_in_state(variable, state)?;
            synthesize_surface_pointer_offset(
                &PointerOffsetTerm::Int32Scaled {
                    value: Box::new(load),
                    byte_width: 4,
                },
                parameters,
                arguments,
                state,
                bound_variables,
            )
        }
        PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: 4,
        } if matches!(value.as_ref(), Bitvector32Term::MemoryLoad(_, _)) => {
            let Bitvector32Term::MemoryLoad(_, pointer) = value.as_ref() else {
                unreachable!()
            };
            if let Some(field) =
                synthesize_parameter_field_load(pointer, CType::Int32Pointer, parameters, arguments)
            {
                Some(field)
            } else {
                Some(ContractExpression::CFragment(CExpression::TypedLoad {
                    pointer: Box::new(synthesize_surface_pointer(
                        pointer,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?),
                    value_type: CType::Int32Pointer,
                    volatile: false,
                }))
            }
        }
        PointerOffsetTerm::Add(left, right) => {
            let indexed_pointer = |base: &PointerOffsetTerm, byte_offset: &PointerOffsetTerm| {
                let PointerOffsetTerm::Constant(byte_offset) = byte_offset else {
                    return None;
                };
                if byte_offset % 4 != 0 {
                    return None;
                }
                let ContractExpression::CFragment(base) = synthesize_surface_pointer_offset(
                    base,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                )?
                else {
                    return None;
                };
                Some(ContractExpression::CFragment(CExpression::Add(
                    Box::new(base),
                    Box::new(CExpression::Value(CValue::Int32(
                        Bitvector32Term::Constant((byte_offset / 4) as u32),
                    ))),
                )))
            };
            let dynamically_indexed_pointer =
                |base: &PointerOffsetTerm, index: &PointerOffsetTerm| {
                    let PointerOffsetTerm::Int32Scaled {
                        value: index,
                        byte_width: 4,
                    } = index
                    else {
                        return None;
                    };
                    let base =
                        contract_expression_to_c_fragment(&synthesize_surface_pointer_offset(
                            base,
                            parameters,
                            arguments,
                            state,
                            bound_variables,
                        )?)?;
                    let index = contract_expression_to_c_fragment(&synthesize_surface_bitvector(
                        index,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?)?;
                    Some(ContractExpression::CFragment(CExpression::Add(
                        Box::new(base),
                        Box::new(index),
                    )))
                };
            indexed_pointer(left, right)
                .or_else(|| indexed_pointer(right, left))
                .or_else(|| dynamically_indexed_pointer(left, right))
                .or_else(|| dynamically_indexed_pointer(right, left))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } if matches!(*byte_width, 1 | 4) => {
            synthesize_surface_bitvector(value, parameters, arguments, state, bound_variables)
        }
        PointerOffsetTerm::Constant(_)
        | PointerOffsetTerm::Variable(_)
        | PointerOffsetTerm::Int32Scaled { .. }
        | PointerOffsetTerm::Int64Scaled { .. } => None,
    }
}

/// Names a canonical pointer value through a currently readable pointer field
/// of a struct parameter. Allocation identity conditions compare canonical
/// allocation offsets, not the memory-load syntax that produced them; this
/// reverse lookup recovers stable source syntax at each recorded snapshot.
fn synthesize_parameter_field_pointer_value(
    term: &PointerOffsetTerm,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Option<ContractExpression> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let (Some(layout), CExpression::Value(CValue::Pointer(base))) =
            (parameter.struct_layout(), argument)
        else {
            continue;
        };
        for (field_name, field) in layout.fields() {
            let value_type = field.c_type().to_kernel_type();
            if !value_type.is_pointer() {
                continue;
            }
            let field_pointer = base.offset_by_bytes(field.offset_bytes());
            let loaded_offset = match state.memory().load(&field_pointer) {
                CExpressionOutcome::Value(CValue::Pointer(value)) => value.offset.clone(),
                // Struct pointer fields are represented in contract memory
                // by their pointer-width scalar offset.
                CExpressionOutcome::Value(CValue::Int32(value)) => PointerOffsetTerm::scale_int32(
                    value,
                    i64::from(value_type.pointee_type()?.byte_width()),
                ),
                _ => continue,
            };
            if !crate::kernel::offsets_have_same_canonical_form(&loaded_offset, term) {
                continue;
            }
            let base_expression = CExpression::Variable(parameter.name().to_string());
            let lowered_pointer = if field.offset_bytes() == 0 {
                base_expression.clone()
            } else {
                CExpression::PointerOffsetBytes {
                    pointer: Box::new(base_expression.clone()),
                    bytes: field.offset_bytes(),
                }
            };
            return Some(ContractExpression::Field {
                base: Box::new(ContractExpression::CFragment(base_expression)),
                field: field_name.clone(),
                lowered: CExpression::TypedLoad {
                    pointer: Box::new(lowered_pointer),
                    value_type,
                    volatile: false,
                },
            });
        }
    }
    None
}

/// The source load a load variable denotes at this state: the cell it
/// names, when this state's memory lies in the variable's epoch. The
/// kernel's own naming law decides membership, so a spelling built from
/// the returned load lowers back to exactly this variable here.
fn registered_load_in_state(variable: &Variable, state: &CState) -> Option<Bitvector32Term> {
    if !crate::kernel::is_load_variable(variable) {
        return None;
    }
    let (_, pointer) = crate::kernel::registered_load_for_variable(variable)?;
    let memory = crate::kernel::intern_c_memory_ref(state.memory());
    let Bitvector32Term::Variable(named) =
        crate::kernel::canonical_form_of_load(memory.clone(), pointer.clone())
    else {
        return None;
    };
    (named == *variable).then(|| Bitvector32Term::MemoryLoad(memory, Box::new(pointer)))
}

fn synthesize_surface_bitvector(
    term: &Bitvector32Term,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("bitvector")?;
    let bitvector_frame = SurfaceBitvectorFrame::enter();
    if bitvector_frame.is_outermost() && bitvector_term_exceeds_depth_limit(term) {
        record_surface_synthesis_exhaustion("bitvector");
        return None;
    }
    if let Bitvector32Term::Variable(variable) = term
        && let Some(name) = bound_variables.get(variable)
    {
        return Some(ContractExpression::CFragment(CExpression::Variable(
            name.clone(),
        )));
    }
    if let Bitvector32Term::Constant(_) = term {
        return Some(ContractExpression::CFragment(CExpression::Value(
            CValue::Int32(term.clone()),
        )));
    }
    if let Some((name, _)) = state.locals().object_values().find(|(_, value)| {
        matches!(
            value,
            CValue::Int16(local)
                | CValue::Int32(local)
                | CValue::UInt8(local)
                | CValue::UInt16(local)
                | CValue::UInt32(local)
                | CValue::Int64(local)
                | CValue::UInt64(local)
                if local == term
        )
    }) {
        return Some(if name == "result" {
            ContractExpression::CBinding(name.to_string())
        } else {
            ContractExpression::CFragment(CExpression::Variable(name.to_string()))
        });
    }
    if let Some(name) = describe_parameter_bitvector(term, parameters, arguments) {
        return Some(if name == "result" {
            ContractExpression::CBinding(name)
        } else {
            ContractExpression::CFragment(CExpression::Variable(name))
        });
    }
    if let Some(field) = synthesize_local_aggregate_field(term, state) {
        return Some(field);
    }
    if let Some(snapshot) = synthesize_snapshot_local(term) {
        return Some(snapshot);
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        Some((
            Box::new(synthesize_surface_bitvector(
                left,
                parameters,
                arguments,
                state,
                bound_variables,
            )?),
            Box::new(synthesize_surface_bitvector(
                right,
                parameters,
                arguments,
                state,
                bound_variables,
            )?),
        ))
    };
    match term {
        Bitvector32Term::Constant(_) => unreachable!("constants returned above"),
        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Add(left, right))
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Subtract(left, right))
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Multiply(left, right))
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Divide(left, right))
        }
        Bitvector32Term::UnsignedDivide(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Divide(left, right))
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Remainder(left, right))
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Remainder(left, right))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftLeft(left, right))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftRight(left, right))
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftRight(left, right))
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseAnd(left, right))
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseOr(left, right))
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseXor(left, right))
        }
        Bitvector32Term::BitwiseNot(value) => Some(ContractExpression::BitwiseNot(Box::new(
            synthesize_surface_bitvector(value, parameters, arguments, state, bound_variables)?,
        ))),
        // Floating-point operation terms are not integer surface fragments;
        // callers that need them retain the original C expression instead.
        Bitvector32Term::Float32Negate(_)
        | Bitvector32Term::Float32Binary { .. }
        | Bitvector32Term::Float64Negate(_)
        | Bitvector32Term::Float64Binary { .. } => None,
        Bitvector32Term::PointerAddress(pointer) => {
            let pointer =
                synthesize_surface_pointer(pointer, parameters, arguments, state, bound_variables)?;
            Some(ContractExpression::CFragment(CExpression::Cast {
                expression: Box::new(pointer),
                target_type: CType::UInt64,
                pointee_volatile: false,
                pointee_constant: false,
            }))
        }
        Bitvector32Term::MemoryLoad(memory, kernel_pointer) => {
            if let Some(source) = SYNTHESIS_QUALIFIED_SOURCES.with(|slot| {
                slot.borrow()
                    .as_ref()?
                    .storage
                    .qualified_load_sources
                    .get(kernel_pointer.as_ref())
                    .cloned()
            }) {
                return Some(source);
            }
            let old = SYNTHESIS_ENTRY_STATE.with(|slot| {
                let slot = slot.borrow();
                let entry = slot.as_ref()?;
                if entry.memory() == state.memory() {
                    return None;
                }
                let Bitvector32Term::Variable(variable) = crate::kernel::canonical_form_of_load(
                    memory.clone(),
                    kernel_pointer.as_ref().clone(),
                ) else {
                    return None;
                };
                let load = registered_load_in_state(&variable, entry)?;
                if registered_load_in_state(&variable, state).is_some() {
                    return None;
                }
                Some(ContractExpression::Old(Box::new(
                    synthesize_surface_bitvector(
                        &load,
                        parameters,
                        arguments,
                        entry,
                        bound_variables,
                    )?,
                )))
            });
            if old.is_some() {
                return old;
            }
            if let PointerBlock::Concrete(block) = &kernel_pointer.block
                && let Some(name) = block.strip_prefix("local:")
                && kernel_pointer.offset == PointerOffsetTerm::Constant(0)
            {
                // A memory-resident scalar local reads as its own name.
                Some(ContractExpression::CFragment(CExpression::Variable(
                    name.to_string(),
                )))
            } else if let Some(field) =
                synthesize_parameter_field_load(kernel_pointer, CType::Int32, parameters, arguments)
            {
                Some(field)
            } else if let Some(indexed_field) = synthesize_parameter_field_indexed_int32_load(
                kernel_pointer,
                parameters,
                arguments,
                state,
                bound_variables,
            ) {
                Some(indexed_field)
            } else if let Some(indexed_local) = synthesize_local_indexed_int32_load(
                kernel_pointer,
                parameters,
                arguments,
                state,
                bound_variables,
            ) {
                Some(indexed_local)
            } else {
                let value_type =
                    parameters
                        .iter()
                        .zip(arguments)
                        .find_map(|(parameter, argument)| {
                            let CExpression::Value(CValue::Pointer(base)) = argument else {
                                return None;
                            };
                            let element_type = parameter.c_type().pointee_type()?;
                            kernel_pointer.element_index_from_base_with_width(
                                base,
                                element_type.to_kernel_type().byte_width(),
                            )?;
                            Some(element_type.to_kernel_type())
                        });
                let pointer = synthesize_surface_pointer(
                    kernel_pointer,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                );
                let pointer = pointer?;
                Some(ContractExpression::CFragment(match value_type {
                    Some(CType::UInt8) => CExpression::TypedLoad {
                        pointer: Box::new(pointer),
                        value_type: CType::UInt8,
                        volatile: false,
                    },
                    _ => CExpression::Load(Box::new(pointer)),
                }))
            }
        }
        // A load variable names one cell of one memory epoch. It denotes
        // the source load of that cell from any snapshot whose memory
        // lies in the same epoch; the kernel's own naming law decides that,
        // so the spelling lowers back to exactly this variable there.
        Bitvector32Term::Variable(variable) => {
            // A memory-resident scalar local holding exactly this variable
            // reads as its own name here.
            if let Some((name, _)) = state.local_cell_values().find(|(_, value)| {
                matches!(
                    value,
                    CValue::Int16(held)
                        | CValue::Int32(held)
                        | CValue::UInt8(held)
                        | CValue::UInt16(held)
                        | CValue::UInt32(held)
                        | CValue::Int64(held)
                        | CValue::UInt64(held)
                        if held == term
                )
            }) {
                return Some(ContractExpression::CFragment(CExpression::Variable(
                    name.to_string(),
                )));
            }
            if let Some(load) = registered_load_in_state(variable, state) {
                return synthesize_surface_bitvector(
                    &load,
                    parameters,
                    arguments,
                    state,
                    bound_variables,
                );
            }
            SYNTHESIS_ENTRY_STATE.with(|slot| {
                let slot = slot.borrow();
                let entry = slot.as_ref()?;
                let load = registered_load_in_state(variable, entry)?;
                Some(ContractExpression::Old(Box::new(
                    synthesize_surface_bitvector(
                        &load,
                        parameters,
                        arguments,
                        entry,
                        bound_variables,
                    )?,
                )))
            })
        }
        Bitvector32Term::Int64Constant(value) => Some(ContractExpression::CFragment(
            CExpression::Value(CValue::Int64(Bitvector32Term::Int64Constant(*value))),
        )),
        Bitvector32Term::UInt64Constant(value) => Some(ContractExpression::CFragment(
            CExpression::Value(CValue::UInt64(Bitvector32Term::UInt64Constant(*value))),
        )),
        Bitvector32Term::Int64From32(value) | Bitvector32Term::Int64FromUInt32(value) => {
            Some(ContractExpression::CFragment(CExpression::Cast {
                expression: Box::new(contract_expression_to_c_fragment(
                    &synthesize_surface_bitvector(
                        value,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?,
                )?),
                target_type: CType::Int64,
                pointee_volatile: false,
                pointee_constant: false,
            }))
        }
        Bitvector32Term::UInt64From32(value)
        | Bitvector32Term::UInt64FromInt32(value)
        | Bitvector32Term::UInt64FromInt64(value) => {
            Some(ContractExpression::CFragment(CExpression::Cast {
                expression: Box::new(contract_expression_to_c_fragment(
                    &synthesize_surface_bitvector(
                        value,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?,
                )?),
                target_type: CType::UInt64,
                pointee_volatile: false,
                pointee_constant: false,
            }))
        }
        Bitvector32Term::UInt32From64(value) => {
            Some(ContractExpression::CFragment(CExpression::Cast {
                expression: Box::new(contract_expression_to_c_fragment(
                    &synthesize_surface_bitvector(
                        value,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?,
                )?),
                target_type: CType::UInt32,
                pointee_volatile: false,
                pointee_constant: false,
            }))
        }
        Bitvector32Term::Int64Add(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Add(left, right))
        }
        Bitvector32Term::Int64Subtract(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Subtract(left, right))
        }
        Bitvector32Term::Int64Multiply(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Multiply(left, right))
        }
        Bitvector32Term::Int64Divide(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Divide(left, right))
        }
        Bitvector32Term::Int64Remainder(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Remainder(left, right))
        }
        Bitvector32Term::UInt64Add(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Add(left, right))
        }
        Bitvector32Term::UInt64Subtract(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Subtract(left, right))
        }
        Bitvector32Term::UInt64Multiply(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Multiply(left, right))
        }
        Bitvector32Term::UInt64Divide(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Divide(left, right))
        }
        Bitvector32Term::UInt64Remainder(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::Remainder(left, right))
        }
        Bitvector32Term::Int64ShiftLeft(left, right)
        | Bitvector32Term::UInt64ShiftLeft(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftLeft(left, right))
        }
        Bitvector32Term::Int64ArithmeticShiftRight(left, right)
        | Bitvector32Term::UInt64LogicalShiftRight(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::ShiftRight(left, right))
        }
        Bitvector32Term::Int64BitwiseAnd(left, right)
        | Bitvector32Term::UInt64BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseAnd(left, right))
        }
        Bitvector32Term::Int64BitwiseOr(left, right)
        | Bitvector32Term::UInt64BitwiseOr(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseOr(left, right))
        }
        Bitvector32Term::Int64BitwiseXor(left, right)
        | Bitvector32Term::UInt64BitwiseXor(left, right) => {
            let (left, right) = binary(left, right)?;
            Some(ContractExpression::BitwiseXor(left, right))
        }
        Bitvector32Term::Int64BitwiseNot(value) | Bitvector32Term::UInt64BitwiseNot(value) => {
            Some(ContractExpression::BitwiseNot(Box::new(
                synthesize_surface_bitvector(value, parameters, arguments, state, bound_variables)?,
            )))
        }
        Bitvector32Term::If { .. } | Bitvector32Term::RangeFold { .. } => None,
        Bitvector32Term::PureFunctionApplication {
            name,
            arguments: values,
        } => Some(ContractExpression::Call {
            name: name.clone(),
            arguments: values
                .iter()
                .map(|value| {
                    synthesize_surface_bitvector(
                        value,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )
                })
                .collect::<Option<Vec<_>>>()?,
        }),
        Bitvector32Term::ClickFunctionApplication {
            name,
            arguments: values,
        } => synthesize_surface_call(name, values, parameters, arguments, state, bound_variables),
        Bitvector32Term::AlgebraicMatch { .. } | Bitvector32Term::IntegerToMachine { .. } => None,
    }
}

/// Restore explicit calls in invariant-body goals so their defining equations
/// can be opened by ordinary `unfold`. Array snapshots are named only when
/// they are exactly the current or function-entry snapshot; no frame search
/// or memory-content comparison is used to choose the spelling.
#[inline(never)]
fn synthesize_surface_call(
    name: &str,
    values: &[crate::kernel::PureFunctionArgument],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("function-call")?;
    let mut result = Vec::with_capacity(values.len());
    for value in values {
        if !consume_surface_synthesis_work("function-argument") {
            return None;
        }
        let expression = match value {
            crate::kernel::PureFunctionArgument::Value(CValue::Int32(value)) => {
                synthesize_surface_bitvector(value, parameters, arguments, state, bound_variables)?
            }
            crate::kernel::PureFunctionArgument::ArrayRef {
                memory,
                pointer: CValue::Pointer(pointer),
                ..
            } => {
                let snapshot = crate::kernel::intern_c_memory_ref(memory);
                if snapshot == crate::kernel::intern_c_memory_ref(state.memory()) {
                    synthesize_surface_pointer_expression(
                        pointer,
                        parameters,
                        arguments,
                        state,
                        bound_variables,
                    )?
                } else {
                    SYNTHESIS_ENTRY_STATE.with(|slot| {
                        let entry = slot.borrow();
                        let entry = entry.as_ref()?;
                        if snapshot != crate::kernel::intern_c_memory_ref(entry.memory()) {
                            return None;
                        }
                        Some(ContractExpression::Old(Box::new(
                            synthesize_surface_pointer_expression(
                                pointer,
                                parameters,
                                arguments,
                                entry,
                                bound_variables,
                            )?,
                        )))
                    })?
                }
            }
            _ => return None,
        };
        result.push(expression);
    }
    Some(ContractExpression::Call {
        name: name.into(),
        arguments: result,
    })
}

fn synthesize_parameter_field_indexed_int32_load(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("indexed-field")?;
    let pointer_field_and_index = |base: &PointerOffsetTerm,
                                   index: Option<&PointerOffsetTerm>|
     -> Option<(ContractExpression, ContractExpression)> {
        let PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: 4,
        } = base
        else {
            return None;
        };
        let Bitvector32Term::MemoryLoad(_, field_pointer) = value.as_ref() else {
            return None;
        };
        let field = synthesize_parameter_field_load(
            field_pointer,
            CType::Int32Pointer,
            parameters,
            arguments,
        )?;
        let index = match index {
            None => ContractExpression::CFragment(CExpression::Value(int32(0))),
            Some(PointerOffsetTerm::Int32Scaled {
                value,
                byte_width: 4,
            }) => {
                synthesize_surface_bitvector(value, parameters, arguments, state, bound_variables)?
            }
            Some(_) => return None,
        };
        Some((field, index))
    };
    let (field, index) = match &pointer.offset {
        base @ (PointerOffsetTerm::Int32Scaled { .. } | PointerOffsetTerm::Int64Scaled { .. }) => {
            pointer_field_and_index(base, None)?
        }
        PointerOffsetTerm::Add(left, right) => pointer_field_and_index(left, Some(right))
            .or_else(|| pointer_field_and_index(right, Some(left)))?,
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => return None,
    };
    Some(ContractExpression::Index(Box::new(field), Box::new(index)))
}

fn synthesize_local_aggregate_field(
    term: &Bitvector32Term,
    state: &CState,
) -> Option<ContractExpression> {
    state
        .locals()
        .aggregate_object_values()
        .find_map(|(name, layout, slot)| {
            layout.fields().iter().find_map(|field| {
                let (element_type, element_count) = match field.c_type() {
                    CType::Int32 => (CType::Int32, 1),
                    CType::UInt8 => (CType::UInt8, 1),
                    CType::Int32Array(length) => (CType::Int32, length),
                    CType::UInt8Array(length) => (CType::UInt8, length),
                    _ => return None,
                };
                (0..element_count).find_map(|index| {
                    let element_offset = field
                        .offset_bytes()
                        .checked_add(index.checked_mul(element_type.byte_width())?)?;
                    let pointer = if element_offset == 0 {
                        slot.clone()
                    } else {
                        Pointer {
                            block: slot.block.clone(),
                            offset: crate::kernel::PointerOffsetTerm::add(
                                slot.offset.clone(),
                                crate::kernel::PointerOffsetTerm::constant(i64::from(
                                    element_offset,
                                )),
                            ),
                        }
                    };
                    let CExpressionOutcome::Value(value) = state.memory().load(&pointer) else {
                        return None;
                    };
                    let value_term = match value {
                        CValue::Bool(value)
                        | CValue::Int16(value)
                        | CValue::Int32(value)
                        | CValue::UInt8(value)
                        | CValue::UInt16(value)
                        | CValue::UInt32(value)
                        | CValue::Int64(value)
                        | CValue::UInt64(value) => value,
                        CValue::Pointer(_)
                        | CValue::Void
                        | CValue::Float32(_)
                        | CValue::Float64(_) => return None,
                    };
                    if value_term != *term {
                        return None;
                    }
                    let base = CExpression::Variable(name.to_string());
                    let lowered_pointer = if field.offset_bytes() == 0 {
                        base.clone()
                    } else {
                        CExpression::PointerOffsetBytes {
                            pointer: Box::new(base.clone()),
                            bytes: field.offset_bytes(),
                        }
                    };
                    let field_expression = ContractExpression::Field {
                        base: Box::new(ContractExpression::CFragment(base)),
                        field: field.name().to_string(),
                        lowered: CExpression::TypedLoad {
                            pointer: Box::new(lowered_pointer),
                            value_type: field.c_type(),
                            volatile: false,
                        },
                    };
                    if element_count == 1 {
                        Some(field_expression)
                    } else {
                        Some(ContractExpression::Index(
                            Box::new(field_expression),
                            Box::new(ContractExpression::CFragment(CExpression::Value(int32(
                                index,
                            )))),
                        ))
                    }
                })
            })
        })
}

pub(super) fn bitvector_term_is_load_free(term: &Bitvector32Term) -> bool {
    let mut pending = vec![term];
    while let Some(term) = pending.pop() {
        if !consume_surface_synthesis_work("local-index") {
            return false;
        }
        match term {
            Bitvector32Term::MemoryLoad(_, _) => return false,
            Bitvector32Term::PointerAddress(pointer) => {
                pending.extend(pointer.offset.scaled_values());
            }
            Bitvector32Term::Constant(_)
            | Bitvector32Term::Int64Constant(_)
            | Bitvector32Term::UInt64Constant(_)
            | Bitvector32Term::Variable(_) => {}
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::UnsignedDivide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::UnsignedRemainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::LogicalShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Bitvector32Term::Int64Add(left, right)
            | Bitvector32Term::Int64Subtract(left, right)
            | Bitvector32Term::Int64Multiply(left, right)
            | Bitvector32Term::Int64Divide(left, right)
            | Bitvector32Term::Int64Remainder(left, right)
            | Bitvector32Term::Int64ShiftLeft(left, right)
            | Bitvector32Term::Int64ArithmeticShiftRight(left, right)
            | Bitvector32Term::Int64BitwiseAnd(left, right)
            | Bitvector32Term::Int64BitwiseOr(left, right)
            | Bitvector32Term::Int64BitwiseXor(left, right)
            | Bitvector32Term::UInt64Add(left, right)
            | Bitvector32Term::UInt64Subtract(left, right)
            | Bitvector32Term::UInt64Multiply(left, right)
            | Bitvector32Term::UInt64Divide(left, right)
            | Bitvector32Term::UInt64Remainder(left, right)
            | Bitvector32Term::UInt64ShiftLeft(left, right)
            | Bitvector32Term::UInt64LogicalShiftRight(left, right)
            | Bitvector32Term::UInt64BitwiseAnd(left, right)
            | Bitvector32Term::UInt64BitwiseOr(left, right)
            | Bitvector32Term::UInt64BitwiseXor(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Bitvector32Term::Float32Binary { left, right, .. }
            | Bitvector32Term::Float64Binary { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            Bitvector32Term::BitwiseNot(value)
            | Bitvector32Term::Int64BitwiseNot(value)
            | Bitvector32Term::UInt64BitwiseNot(value)
            | Bitvector32Term::Int64From32(value)
            | Bitvector32Term::UInt64From32(value)
            | Bitvector32Term::UInt32From64(value)
            | Bitvector32Term::Int64FromUInt32(value)
            | Bitvector32Term::UInt64FromInt32(value)
            | Bitvector32Term::UInt64FromInt64(value)
            | Bitvector32Term::Float32Negate(value)
            | Bitvector32Term::Float64Negate(value) => pending.push(value),
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => {
                pending.push(then_term);
                pending.push(else_term);
            }
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                pending.push(start);
                pending.push(end);
                pending.push(initial);
                pending.push(body);
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments);
            }
            Bitvector32Term::ClickFunctionApplication { .. }
            | Bitvector32Term::AlgebraicMatch { .. }
            | Bitvector32Term::IntegerToMachine { .. } => return false,
        }
    }
    true
}

fn synthesize_local_indexed_int32_load(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("local-index")?;
    state.locals().object_values().find_map(|(name, value)| {
        let CValue::Pointer(base) = value else {
            return None;
        };
        let element_width = base.c_type().pointee_type()?.byte_width();
        let index = pointer.element_index_from_base_with_width(base, element_width)?;
        if index == Bitvector32Term::Constant(0) {
            return None;
        }
        // This candidate is for ordinary `local[index]` forms. If the
        // derived index itself reads memory, trying to synthesize that load
        // can rediscover another local-relative form with a still larger
        // index indefinitely. More specific field and pointer forms are
        // tried by the surrounding reconstruction logic.
        if !bitvector_term_is_load_free(&index) {
            return None;
        }
        Some(ContractExpression::Index(
            Box::new(ContractExpression::CFragment(CExpression::Variable(
                name.to_string(),
            ))),
            Box::new(synthesize_surface_bitvector(
                &index,
                parameters,
                arguments,
                state,
                bound_variables,
            )?),
        ))
    })
}

fn synthesize_parameter_field_load(
    pointer: &Pointer,
    value_type: CType,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Option<ContractExpression> {
    for (parameter, argument) in parameters.iter().zip(arguments) {
        let (Some(layout), CExpression::Value(CValue::Pointer(base))) =
            (parameter.struct_layout(), argument)
        else {
            continue;
        };
        let Some(element_offset) = pointer
            .element_index_from_base(base)
            .and_then(|offset| offset.as_const())
        else {
            continue;
        };
        let offset_bytes = element_offset.checked_mul(4)?;
        let Some((field_name, field)) = layout
            .fields()
            .iter()
            .find(|(_, field)| field.offset_bytes() == offset_bytes)
        else {
            continue;
        };
        if field.c_type().to_kernel_type() != value_type {
            continue;
        }
        let base = CExpression::Variable(parameter.name().to_string());
        let field_pointer = if offset_bytes == 0 {
            base.clone()
        } else {
            CExpression::PointerOffsetBytes {
                pointer: Box::new(base.clone()),
                bytes: offset_bytes,
            }
        };
        return Some(ContractExpression::Field {
            base: Box::new(ContractExpression::CFragment(base)),
            field: field_name.clone(),
            lowered: CExpression::TypedLoad {
                pointer: Box::new(field_pointer),
                value_type,
                volatile: false,
            },
        });
    }
    None
}

fn synthesize_surface_pointer(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<CExpression> {
    let _frame = SurfaceSynthesisFrame::enter("pointer")?;
    if pointer == &Pointer::null() {
        return Some(CExpression::Value(int32(0)));
    }
    if let Some(expression) = parameters
        .iter()
        .zip(arguments)
        .find_map(|(parameter, argument)| {
            let CExpression::Value(CValue::Pointer(base)) = argument else {
                return None;
            };
            let element_width = parameter
                .c_type()
                .pointee_type()?
                .to_kernel_type()
                .byte_width();
            let index = pointer.element_index_from_base_with_width(base, element_width)?;
            let base = CExpression::Variable(parameter.name().to_string());
            if index == Bitvector32Term::Constant(0) {
                return Some(base);
            }
            let index = synthesize_surface_bitvector(
                &index,
                parameters,
                arguments,
                state,
                bound_variables,
            )?;
            let ContractExpression::CFragment(index) = index else {
                return None;
            };
            Some(CExpression::Add(Box::new(base), Box::new(index)))
        })
    {
        return Some(expression);
    }
    if let Some(expression) = state.locals().object_values().find_map(|(name, value)| {
        let CValue::Pointer(base) = value else {
            return None;
        };
        let element_width = base.c_type().pointee_type()?.byte_width();
        let index = pointer.element_index_from_base_with_width(base, element_width)?;
        let base = CExpression::Variable(name.to_string());
        if index == Bitvector32Term::Constant(0) {
            return Some(base);
        }
        let index =
            synthesize_surface_bitvector(&index, parameters, arguments, state, bound_variables)?;
        let ContractExpression::CFragment(index) = index else {
            return None;
        };
        Some(CExpression::Add(Box::new(base), Box::new(index)))
    }) {
        return Some(expression);
    }
    if !arguments.iter().any(|argument| {
        matches!(
            argument,
            CExpression::Value(CValue::Pointer(base)) if base.block == pointer.block
        )
    }) {
        return None;
    }
    let ContractExpression::CFragment(expression) = synthesize_surface_pointer_offset(
        &pointer.offset,
        parameters,
        arguments,
        state,
        bound_variables,
    )?
    else {
        return None;
    };
    Some(expression)
}

fn synthesize_surface_pointer_expression(
    pointer: &Pointer,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    bound_variables: &BTreeMap<Variable, String>,
) -> Option<ContractExpression> {
    let _frame = SurfaceSynthesisFrame::enter("pointer-expression")?;
    if let Some(pointer) =
        synthesize_surface_pointer(pointer, parameters, arguments, state, bound_variables)
    {
        return Some(ContractExpression::CFragment(pointer));
    }
    if !arguments.iter().any(|argument| {
        matches!(
            argument,
            CExpression::Value(CValue::Pointer(base)) if base.block == pointer.block
        )
    }) {
        return None;
    }
    synthesize_surface_pointer_offset(
        &pointer.offset,
        parameters,
        arguments,
        state,
        bound_variables,
    )
}
