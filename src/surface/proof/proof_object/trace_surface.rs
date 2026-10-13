//! Source names for the individual values in a rejected child argument.
//! This is presentation, never proof authority.

use super::*;

const MAX_TRACE_FACT_DEPTH: usize = 24;
const MAX_TRACE_SNAPSHOTS: usize = 32;

impl Proof<'_> {
    pub(super) fn trace_pointer_pair(
        &self,
        left: &Pointer,
        right: &Pointer,
    ) -> Option<[crate::surface::proof_trace::PointerTraceView; 2]> {
        let view = self.execution_fixed_state_view()?;
        let locals = self.proof_local_values();
        let fact = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(left.clone(), right.clone()),
            true,
        );
        let surface = self
            .available_surface_fact(view.surface_propositions, None, &fact)
            .or_else(|| {
                let reversed = Proposition::ConditionIs(
                    ConditionTerm::pointer_equal(right.clone(), left.clone()),
                    true,
                );
                self.available_surface_fact(view.surface_propositions, None, &reversed)
            });
        let surface = surface.or_else(|| {
            let execution = self.branch_execution()?;
            let anchor = ProgramPointRef {
                region: CodeRegionRef::Statement(execution.core.frontier.next_statement_index),
                kind: ProgramPointKind::Entry,
            };
            self.available_surface_fact(view.surface_propositions, Some(&anchor), &fact)
        });
        let hints = match &surface {
            Some(ClickProposition::Comparison { left, right, .. }) => vec![left, right],
            _ => vec![],
        };
        let recent = view
            .fixed_state
            .recorded_snapshots
            .recent(MAX_TRACE_SNAPSHOTS);
        let function = match self.context.as_ref() {
            ProofContext::Execution(context) => Some(context.parsed_function),
            _ => None,
        };
        let name = |pointer: &Pointer| {
            use crate::surface::proof_trace::{PointerTraceView, pointer_definition};
            if pointer == &Pointer::null() {
                return Some(PointerTraceView {
                    text: "0".into(),
                    snapshot: None,
                });
            }
            // Proof-local values are immutable, unlike C locals. A direct
            // name for a value does not move a memory read to the current state.
            let immutable_name =
                locals
                    .iter()
                    .find_map(|(name, expression)| match expression {
                        ContractExpression::CFragment(CExpression::Value(CValue::Pointer(
                            value,
                        ))) if value.pointer() == pointer => Some(name.clone()),
                        _ => None,
                    });
            if let Some(text) = immutable_name {
                return Some(PointerTraceView {
                    text,
                    snapshot: None,
                });
            }
            let Some(Bitvector32Term::MemoryLoad(memory, address, _)) = pointer_definition(pointer)
            else {
                return None;
            };
            let states = recent
                .iter()
                .filter(|(selector, _)| matches!(selector, SnapshotSelector::Mark(_)))
                .chain(
                    recent
                        .iter()
                        .filter(|(selector, _)| !matches!(selector, SnapshotSelector::Mark(_))),
                )
                .filter(|(_, state)| state.memory().same_storage_roots(memory.memory()));
            let matching: Vec<_> = states.collect();
            let point = matching.first().map(|(selector, _)| {
                crate::surface::diagnostics::describe_snapshot_selector(selector)
            });
            // A checked field spelling through an immutable proof local is
            // usable even when the defining state has no retained C locals.
            // Check the field's address and pointer type, not merely its text.
            for hint in &hints {
                if let Some(text) = immutable_field_hint(hint, &address, &locals) {
                    return Some(PointerTraceView {
                        text,
                        snapshot: Some((memory, point)),
                    });
                }
            }
            for (selector, state) in matching {
                let (parameters, arguments) =
                    crate::surface::diagnostics::local_naming_tables_with_source(state, function);
                if let Some(text) = crate::surface::diagnostics::diagnostic_source_pointer_cell(
                    &address,
                    ParameterBinding::new(&parameters, &arguments),
                    None,
                ) {
                    return Some(PointerTraceView {
                        text,
                        snapshot: Some((
                            memory,
                            Some(crate::surface::diagnostics::describe_snapshot_selector(
                                selector,
                            )),
                        )),
                    });
                }
            }
            // A local can still name this address in another recorded state.
            // Qualify that base separately; do not pretend that the local's
            // state is the state from which the field value was read.
            for (selector, state) in recent
                .iter()
                .filter(|(selector, _)| matches!(selector, SnapshotSelector::Mark(_)))
                .chain(
                    recent
                        .iter()
                        .filter(|(selector, _)| !matches!(selector, SnapshotSelector::Mark(_))),
                )
            {
                let (parameters, arguments) =
                    crate::surface::diagnostics::local_naming_tables_with_source(state, function);
                let base_point = crate::surface::diagnostics::describe_snapshot_selector(selector);
                if let Some(text) = crate::surface::diagnostics::diagnostic_source_pointer_cell(
                    &address,
                    ParameterBinding::new(&parameters, &arguments),
                    Some(&base_point),
                ) {
                    return Some(PointerTraceView {
                        text,
                        snapshot: Some((memory, point)),
                    });
                }
            }
            None
        };
        Some([name(left)?, name(right)?])
    }
}

fn immutable_field_hint(
    expression: &ContractExpression,
    address: &Pointer,
    locals: &BTreeMap<String, ContractExpression>,
) -> Option<String> {
    let mut expression = expression;
    for _ in 0..MAX_TRACE_FACT_DEPTH {
        match expression {
            ContractExpression::At {
                expression: inner, ..
            }
            | ContractExpression::Old(inner) => expression = inner,
            _ => break,
        }
    }
    let ContractExpression::Field {
        base,
        field,
        offset_bytes,
        lowered,
    } = expression
    else {
        return None;
    };
    let CExpression::TypedLoad { value_type, .. } = lowered else {
        return None;
    };
    if !value_type.is_pointer() {
        return None;
    }
    let (name, base) = match base.as_ref() {
        ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) => {
            let ContractExpression::CFragment(CExpression::Value(CValue::Pointer(base))) =
                locals.get(name)?
            else {
                return None;
            };
            (name, base)
        }
        // Checked surface forms substitute model binders with their exact
        // values. Recover the immutable binder before spelling the field.
        ContractExpression::CFragment(CExpression::Value(CValue::Pointer(base))) => {
            let (name, _) = locals.iter().find(|(_, value)| matches!(value, ContractExpression::CFragment(CExpression::Value(CValue::Pointer(candidate))) if candidate == base))?;
            (name, base)
        }
        _ => return None,
    };
    let expected = base.pointer().offset_by_bytes(*offset_bytes);
    (expected.block == address.block
        && crate::kernel::offsets_have_same_canonical_form(&expected.offset, &address.offset))
    .then(|| crate::surface::diagnostics::describe_field_place(name, field))
}

#[cfg(test)]
mod pointer_trace_tests {
    use super::*;

    #[test]
    fn field_hint_recovers_substituted_immutable_binders_only_at_their_exact_address() {
        let base = Pointer::symbolic(Variable(990001));
        let value = CValue::typed_pointer(base.clone(), CType::Int32Pointer);
        let local = ContractExpression::CFragment(CExpression::Value(value.clone()));
        let locals = BTreeMap::from([("zid".to_string(), local.clone())]);
        let hint = |base_expression, value_type| ContractExpression::Field {
            base: Box::new(base_expression),
            field: "left".into(),
            offset_bytes: 8,
            lowered: CExpression::TypedLoad {
                pointer: Box::new(CExpression::Value(value.clone())),
                value_type,
                volatile: false,
                pointee_constant: false,
                source: Default::default(),
            },
        };
        let address = base.offset_by_bytes(8);
        let substituted = hint(local.clone(), CType::Int32Pointer);
        assert_eq!(
            immutable_field_hint(&substituted, &address, &locals),
            Some("zid->left".into())
        );
        assert_eq!(
            immutable_field_hint(&substituted, &base.offset_by_bytes(16), &locals),
            None
        );
        assert_eq!(
            immutable_field_hint(&hint(local, CType::UInt64), &address, &locals),
            None
        );
        assert_eq!(
            immutable_field_hint(&substituted, &address, &BTreeMap::new()),
            None
        );
        let reassigned = BTreeMap::from([(
            "zid".to_string(),
            ContractExpression::CFragment(CExpression::Value(CValue::typed_pointer(
                Pointer::symbolic(Variable(990002)),
                CType::Int32Pointer,
            ))),
        )]);
        assert_eq!(
            immutable_field_hint(&substituted, &address, &reassigned),
            None
        );
        // A C-local spelling is not enough to make it an immutable binder.
        assert_eq!(
            immutable_field_hint(
                &hint(
                    ContractExpression::CBinding("zid".into()),
                    CType::Int32Pointer
                ),
                &address,
                &locals
            ),
            None
        );
    }
}
