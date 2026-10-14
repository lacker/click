//! Private ordinary resource carriers for conditional loop guard clauses.
//! Metadata locates an owned carrier; only checked unfolding transfers its guard.
use super::*;
use crate::kernel::*;

pub(super) struct DirectLoopGuard {
    source: CResourceSpec,
    definition: CCompositeResourceDefinition,
    head: ResourceInstance,
}

fn scalar_expression(expression: &SpecExpression) -> bool {
    use SpecExpression::*;
    match expression {
        Value(_) => true,
        CExpression(expression) => scalar_c_expression(expression),
        Add(a, b)
        | Subtract(a, b)
        | Multiply(a, b)
        | Divide(a, b)
        | Remainder(a, b)
        | ShiftLeft(a, b)
        | ShiftRight(a, b)
        | BitwiseAnd(a, b)
        | BitwiseOr(a, b)
        | BitwiseXor(a, b) => scalar_expression(a) && scalar_expression(b),
        BitwiseNot(value) | Cast(value, _) => scalar_expression(value),
        _ => false,
    }
}
fn scalar_c_expression(expression: &CExpression) -> bool {
    use CExpression::*;
    match expression {
        Value(_) | Variable(_) => true,
        Cast { expression, .. } | Not(expression) | BitwiseNot(expression) => {
            scalar_c_expression(expression)
        }
        Add(a, b)
        | Subtract(a, b)
        | Multiply(a, b)
        | Divide(a, b)
        | Remainder(a, b)
        | ShiftLeft(a, b)
        | ShiftRight(a, b)
        | BitwiseAnd(a, b)
        | BitwiseOr(a, b)
        | BitwiseXor(a, b)
        | Equal(a, b)
        | NotEqual(a, b)
        | LessThan(a, b)
        | LessEqual(a, b)
        | GreaterThan(a, b)
        | GreaterEqual(a, b) => scalar_c_expression(a) && scalar_c_expression(b),
        _ => false,
    }
}
fn scalar_condition(condition: &SpecProposition) -> bool {
    match condition {
        SpecProposition::Comparison { left, right, .. } => {
            scalar_expression(left) && scalar_expression(right)
        }
        SpecProposition::Not(inner) => scalar_condition(inner),
        _ => false,
    }
}

fn source_condition(
    state: &CState,
    spec: &CResourceSpec,
    assumptions: &PureFactContext,
) -> Result<(ConditionTerm, CValue), String> {
    let guard = spec
        .guard()
        .ok_or("conditional loop resource has no condition")?;
    if !scalar_condition(guard) {
        return Err("conditional mutex guard ownership currently requires a scalar comparison over C values".into());
    }
    let paths = crate::kernel::spec::lower_spec_proposition_at_state_with_loop_entry(
        state,
        guard,
        None,
        assumptions,
        &mut ExecutionBudget::beside_live_state(),
    )
    .map_err(|limit| {
        format!(
            "evaluating the conditional loop resource stopped at {}",
            limit.describe()
        )
    })?;
    let [path] = paths.as_slice() else {
        return Err("conditional loop resources require one scalar condition".into());
    };
    if !path
        .obligations
        .iter()
        .all(|o| crate::kernel::PureFactContext::settles_exactly(assumptions, o.proposition()))
    {
        return Err("Requires the conditional loop resource expression to be defined".into());
    }
    let value = crate::kernel::spec::conditional_spec_value(&path.proposition, int32(1), int32(0))
        .ok_or("conditional loop resources require one scalar condition")?;
    let (condition, expected) =
        crate::kernel::spec::proposition_as_single_condition(&path.proposition)
            .ok_or("conditional loop resources require one scalar condition")?;
    let held = if expected {
        condition
    } else {
        ConditionTerm::Bitvector32Equal(
            Box::new(match &value {
                CValue::Int32(term) => term.clone(),
                _ => unreachable!(),
            }),
            Box::new(1u32.into()),
        )
    };
    Ok((held, value))
}

fn source_mutex(
    state: &CState,
    spec: &CResourceSpec,
    assumptions: &PureFactContext,
) -> Result<Pointer, String> {
    let CResourceTerm::MutexGuard {
        mutex,
        snapshot: CResourceSnapshot::Current,
    } = spec.term()
    else {
        return Err("conditional loop guard requires current mutex_guard ownership".into());
    };
    if spec.access() != CResourceAccessMode::Own
        || spec.quantity() != &CResourceQuantity::One
        || spec.snapshot() == CResourceSnapshot::Post
        || spec.role() != CResourceTransferRole::Borrow
        || spec.binding_identity().is_some()
    {
        return Err(
            "conditional loop guard requires unnamed unit ownership at the current state".into(),
        );
    }
    let result = crate::kernel::loops::evaluate_loop_effect_segment_value(
        state,
        mutex,
        assumptions,
        "conditional loop mutex",
        &mut ExecutionBudget::beside_live_state(),
    )
    .map_err(|limit| {
        format!(
            "evaluating the conditional loop mutex stopped at {}",
            limit.describe()
        )
    })?;
    let pointer = match result {
        Ok(CValue::Pointer(pointer)) => pointer,
        Ok(_) => return Err("conditional loop guard requires a mutex pointer".into()),
        Err(message) => return Err(message),
    };
    Ok(pointer.pointer().clone())
}

fn missing_guard(spec: &CResourceSpec) -> String {
    let argument = spec
        .source_arguments()
        .and_then(|arguments| arguments.first());
    format!(
        "Requires owns mutex_guard({})",
        argument.map_or("...", String::as_str)
    )
}

fn instance_with_value(carrier: &DirectLoopGuard, value: CValue) -> ResourceInstance {
    ResourceInstance::new(
        carrier.head.identity(),
        carrier.head.name().into(),
        vec![].into(),
        carrier.head.schema().clone(),
        vec![value.into()].into(),
    )
    .expect("private carrier schema")
}

pub(in crate::kernel) fn prepare_direct_loop_guard(
    entry: &CState,
    head: &CState,
    spec: &CResourceSpec,
    identity: Variable,
    assumptions: &PureFactContext,
) -> Result<(CState, Pointer), String> {
    let mutex = source_mutex(entry, spec, assumptions)?;
    // A previous loop may have left an empty or held carrier at its exit.
    // Retire it only by the same checked ownership exchange as a runtime use.
    if entry
        .mutex_ledger
        .as_ref()
        .and_then(|ledger| ledger.storage.direct_loop_carriers.get(&mutex))
        .is_some_and(|carrier| {
            entry
                .resources
                .owned_instance(carrier.head.identity())
                .is_some()
        })
    {
        let open = |state: &CState| -> Result<CState, String> {
            let context = MutexContext::new(state.clone());
            let opened = context
                .open_direct_loop_guard(&mutex, assumptions)
                .map_err(|_| missing_guard(spec))?
                .ok_or_else(|| missing_guard(spec))?;
            Ok(opened
                .materialize_loop_mutex(&mutex, assumptions)
                .map_err(|_| "Requires the previous conditional loop guard condition")?
                .unwrap_or(opened)
                .state)
        };
        return prepare_direct_loop_guard(&open(entry)?, &open(head)?, spec, identity, assumptions);
    }
    if source_mutex(head, spec, assumptions)? != mutex {
        return Err("conditional loop mutex must not change at the loop head".into());
    }
    let (entry_condition, _) = source_condition(entry, spec, assumptions)?;
    let active = crate::kernel::loops::condition_is_decided(assumptions, &entry_condition)
        .ok_or("Requires the conditional loop resource condition at entry")?;
    let ledger = entry
        .mutex_ledger
        .as_ref()
        .ok_or("Requires an initialized loop mutex")?;
    if crate::kernel::loops::condition_is_decided(assumptions, &ledger.held_condition(&mutex))
        != Some(active)
    {
        return Err(missing_guard(spec));
    }
    let old_guard = active.then(|| ledger.guard_resource(&mutex)).flatten();
    if active
        && old_guard.as_ref().is_none_or(|fact| {
            entry
                .resources
                .unique_owned_occurrence_for_fact(fact)
                .is_none()
        })
    {
        return Err(missing_guard(spec));
    }
    let (condition, value) = source_condition(head, spec, assumptions)?;
    let schema =
        ResourceFieldSchema::new(vec![("active".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let name = format!("$conditional-loop-guard:{}", identity.0);
    let body = CResourceSpec::new(
        CResourceTerm::MutexGuard {
            mutex: Box::new(CExpression::Value(CValue::pointer(mutex.clone()))),
            snapshot: CResourceSnapshot::Current,
        },
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    let mut definition = CCompositeResourceDefinition::new(
        name.clone(),
        vec![],
        Some(SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("active")),
            operator: CComparisonOperator::NotEqual,
            right: SpecExpression::Value(int32(0)),
        }),
        false,
        vec![body],
        vec![],
    )
    .with_instance_schema(Some(schema.clone()));
    definition.contains_mutex_authority = true;
    let instance = ResourceInstance::new(
        identity,
        name,
        vec![].into(),
        schema,
        vec![value.into()].into(),
    )
    .unwrap();
    let carrier = Arc::new(DirectLoopGuard {
        source: spec.clone(),
        definition,
        head: instance.clone(),
    });
    let mut state = abstract_loop_mutex(head, &mutex, condition)?;
    if let Some(guard) = old_guard {
        state.resources = state
            .resources
            .without_fact_incrementally(&guard, assumptions)
            .ok_or_else(|| missing_guard(spec))?;
    }
    state.resources = state
        .resources
        .try_compose_into_valid_context_delaying_normalization(
            [CResourceFact::own(CResource::Instance(instance))],
            assumptions,
        )
        .map_err(|_| "conditional loop resource ownership overlaps")?;
    let ledger = state.mutex_ledger.as_ref().unwrap();
    let mut ledger = ledger.with_inserted(mutex.clone(), ledger.get(&mutex).unwrap().clone());
    Arc::get_mut(&mut ledger.storage)
        .unwrap()
        .direct_loop_carriers = ledger
        .storage
        .direct_loop_carriers
        .with_inserted(mutex.clone(), carrier);
    state.mutex_ledger = Some(ledger);
    Ok((state, mutex))
}

pub(in crate::kernel) fn select_direct_loop_guards(
    state: &CState,
    pointers: Vec<Pointer>,
) -> CState {
    let Some(ledger) = &state.mutex_ledger else {
        return state.clone();
    };
    let Some((mutex, entry)) = ledger.storage.entries.iter().next() else {
        return state.clone();
    };
    let mut next = ledger.with_inserted(mutex.clone(), entry.clone());
    Arc::get_mut(&mut next.storage)
        .unwrap()
        .direct_loop_selection = Arc::new(pointers);
    let mut state = state.clone();
    state.mutex_ledger = Some(next);
    state
}

impl MutexContext {
    pub(super) fn open_direct_loop_guard(
        &self,
        mutex: &Pointer,
        assumptions: &PureFactContext,
    ) -> Result<Option<Self>, MutexTransitionError> {
        let Some(carrier) = self
            .state
            .mutex_ledger
            .as_ref()
            .and_then(|ledger| ledger.storage.direct_loop_carriers.get(mutex))
        else {
            return Ok(None);
        };
        let Some(instance) = self.state.resources.owned_instance(carrier.head.identity()) else {
            return Ok(None);
        };
        let result = crate::kernel::functions::rewrite_resource_instance_selecting_children(
            &self.state,
            instance,
            &carrier.definition,
            std::slice::from_ref(&carrier.definition),
            assumptions,
            true,
            None,
        )
        .map_err(|_| MutexTransitionError::MissingGuard(mutex.clone()))?;
        let mut state = result.state;
        let ledger = state.mutex_ledger.as_ref().unwrap();
        let mut next = ledger.with_inserted(mutex.clone(), ledger.get(mutex).unwrap().clone());
        Arc::get_mut(&mut next.storage)
            .unwrap()
            .direct_loop_carriers = ledger.storage.direct_loop_carriers.without_key(mutex);
        state.mutex_ledger = Some(next);
        Ok(Some(Self {
            state,
            runtime_loan_transition: None,
        }))
    }
}

/// Close this head's conditional ownership before comparing ordinary resources.
pub(in crate::kernel) fn normalize_direct_loop_guards(
    top: &CState,
    next: &CState,
    assumptions: &PureFactContext,
) -> Result<(CState, Vec<Pointer>), String> {
    let mut state = next.clone();
    let mut checked = Vec::new();
    let Some(ledger) = &top.mutex_ledger else {
        return Ok((state, checked));
    };
    for mutex in ledger.storage.direct_loop_selection.iter() {
        crate::instrumentation::record_deterministic_work(1);
        let Some(carrier) = ledger.storage.direct_loop_carriers.get(mutex) else {
            continue;
        };
        let Some(head_instance) = top.resources.owned_instance(carrier.head.identity()) else {
            continue;
        };
        let (held, value) = source_condition(&state, &carrier.source, assumptions)?;
        if source_mutex(&state, &carrier.source, assumptions)? != *mutex {
            return Err("conditional loop guard changed its mutex".into());
        }
        if head_instance.fields().first() == Some(&AlgebraicValue::C(value.clone()))
            && state.resources.owned_instance(carrier.head.identity()) == Some(head_instance)
            && state.mutex_ledger.as_ref().is_some_and(|next| {
                matches!(
                    (ledger.get(mutex), next.get(mutex)),
                    (Some(MutexEntry::ConditionalLoop { initialization:a, epoch:b, held:c }),
                     Some(MutexEntry::ConditionalLoop { initialization:x, epoch:y, held:z }))
                    if a==x && b==y && c==z
                )
            })
        {
            continue;
        }
        let active = crate::kernel::loops::condition_is_decided(assumptions, &held)
            .ok_or("Requires the conditional loop resource condition at the backedge")?;
        let next_ledger = state
            .mutex_ledger
            .as_ref()
            .ok_or("Requires an initialized loop mutex")?;
        if crate::kernel::loops::condition_is_decided(
            assumptions,
            &next_ledger.held_condition(mutex),
        ) != Some(active)
        {
            return Err(missing_guard(&carrier.source));
        }
        if let Some(opened) = MutexContext::new(state.clone())
            .open_direct_loop_guard(mutex, assumptions)
            .map_err(|_| missing_guard(&carrier.source))?
        {
            state = opened.state;
        }
        let instance = instance_with_value(carrier, value);
        state = crate::kernel::functions::rewrite_resource_instance_selecting_children(
            &state,
            &instance,
            &carrier.definition,
            std::slice::from_ref(&carrier.definition),
            assumptions,
            false,
            None,
        )
        .map_err(|_| missing_guard(&carrier.source))?
        .state;
        state.resources = state
            .resources
            .without_fact_incrementally(
                &CResourceFact::own(CResource::Instance(instance)),
                assumptions,
            )
            .expect("just folded carrier")
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(
                head_instance.clone(),
            )));
        checked.push(mutex.clone());
    }
    Ok((state, checked))
}
