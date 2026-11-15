//! Shared pointer-class lookup for predicates, callback witnesses and checked object types.
//! Exact source handles are payloads, never class keys or inferred premises.
use super::*;

impl EqualityGraph {
    #[cfg(test)]
    pub(in crate::kernel) fn take_pointer_fact_merge_visits() -> usize {
        terms::take_pointer_fact_merge_visits()
    }

    pub(in crate::kernel) fn clear_proposition_pointer_facts(&self) {
        self.clear_pointer_fact_sources(false);
    }

    pub(in crate::kernel) fn clear_condition_pointer_facts(&self) {
        self.clear_pointer_fact_sources(true);
    }

    fn clear_pointer_fact_sources(&self, conditions: bool) {
        let sources = {
            let state = self.state.lock().expect("equality graph");
            if conditions {
                state.condition_pointer_fact_inputs.clone()
            } else {
                state.pointer_fact_inputs.clone()
            }
        };
        for (_, source) in sources.iter() {
            crate::instrumentation::record_deterministic_work(1);
            self.adjust_pointer_fact_source(source, false);
        }
    }

    /// Checked values retained directly by an admitted, unconditional atom.
    /// Opaque call arguments may carry annotations from another interning
    /// context; they are not evidence here. Binders and states stay opaque.
    fn object_type_keys(proposition: &Proposition) -> BTreeSet<(Pointer, terms::PointerFactKey)> {
        enum Work<'a> {
            Term(&'a Term),
            Model(&'a AlgebraicTerm),
            Value(&'a ProgramValue),
            Pointer(&'a PointerValue),
        }
        let mut pending = match proposition {
            Proposition::Equal(a, b) => vec![Work::Term(a), Work::Term(b)],
            Proposition::Predicate { arguments, .. } => arguments.iter().map(Work::Term).collect(),
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(a, b), true) => {
                vec![Work::Pointer(a), Work::Pointer(b)]
            }
            Proposition::ConditionIs(ConditionTerm::AlgebraicEqual(a, b), true) => {
                vec![Work::Model(a), Work::Model(b)]
            }
            _ => return BTreeSet::new(),
        };
        let mut keys = BTreeSet::new();
        while let Some(work) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            match work {
                Work::Term(Term::ProgramValue(value)) => pending.push(Work::Value(value)),
                Work::Term(Term::Algebraic(model)) => pending.push(Work::Model(model)),
                Work::Model(AlgebraicTerm {
                    node: AlgebraicTermNode::Constructor { fields, .. },
                    ..
                }) => {
                    for field in fields {
                        match field {
                            AlgebraicValue::Program(value) => pending.push(Work::Value(value)),
                            AlgebraicValue::Algebraic(model) => pending.push(Work::Model(model)),
                            AlgebraicValue::Integer(_) => {}
                        }
                    }
                }
                Work::Value(ProgramValue::Pointer(pointer)) => pending.push(Work::Pointer(pointer)),
                Work::Pointer(pointer) => {
                    if let Some(evidence) = pointer.object_type_evidence() {
                        keys.insert((
                            pointer.pointer().clone(),
                            terms::PointerFactKey::ObjectType(evidence.class.clone()),
                        ));
                    }
                }
                _ => {}
            }
        }
        keys
    }

    pub(in crate::kernel) fn has_object_type(
        &self,
        pointer: &Pointer,
        class: &crate::kernel::effective_type::CAccessClass,
    ) -> bool {
        self.pointer_fact_candidates(pointer, &terms::PointerFactKey::ObjectType(class.clone()))
            .get(&String::new())
            .is_some_and(|sources| !sources.is_empty())
    }

    fn pointer_predicate_key(
        proposition: &crate::kernel::Proposition,
    ) -> Option<(Pointer, terms::PointerFactKey)> {
        use crate::kernel::{ProgramValue, Proposition, Term};
        let Proposition::Predicate { name, arguments } = proposition else {
            return None;
        };
        let (position, pointer) =
            arguments
                .iter()
                .enumerate()
                .find_map(|(position, argument)| {
                    if let Term::ProgramValue(ProgramValue::Pointer(pointer)) = argument {
                        Some((position, pointer))
                    } else {
                        None
                    }
                })?;
        // Every coverage fact of one opaque extent shares a bucket, whatever
        // its element width, so a lookup by extent finds them all.
        if name.starts_with(crate::kernel::SUBOBJECT_COVERS_PREDICATE_PREFIX) {
            return Some((
                pointer.pointer().clone(),
                terms::PointerFactKey::PredicateShape(
                    crate::kernel::SUBOBJECT_COVERS_PREDICATE_PREFIX.to_string(),
                    arguments.len(),
                    position,
                    pointer.program_type(),
                ),
            ));
        }
        let key = crate::kernel::proof::fact_keys::pointer_predicate_selector(proposition)
            .map(terms::PointerFactKey::Predicate)
            .unwrap_or_else(|| {
                terms::PointerFactKey::PredicateShape(
                    name.clone(),
                    arguments.len(),
                    position,
                    pointer.program_type(),
                )
            });
        Some((pointer.pointer().clone(), key))
    }

    /// Retain an exact source proposition in the selected pointer's checked
    /// class. This adds no equality, read permission, or state transport.
    pub(in crate::kernel) fn adjust_pointer_fact(
        &self,
        source: &std::sync::Arc<crate::kernel::ExecutionPureFact>,
        insert: bool,
    ) {
        let source = source.clone() as std::sync::Arc<dyn terms::PointerFactSource>;
        self.adjust_pointer_fact_source(&source, insert);
    }

    pub(super) fn adjust_pointer_fact_source(
        &self,
        source: &std::sync::Arc<dyn terms::PointerFactSource>,
        insert: bool,
    ) {
        use crate::kernel::{FunctionContract, ProgramValue, Proposition, Term};
        let proposition = source.proposition();
        if self.adjust_address_separation_source(source, insert) {
            return;
        }
        let mut keys = Self::object_type_keys(proposition);
        let predicate = Self::pointer_predicate_key(proposition);
        keys.extend(predicate.iter().cloned());
        if keys.is_empty() {
            return;
        }
        for (pointer, _) in &keys {
            self.address_class(pointer);
        }
        let mut state = self.state.lock().expect("equality graph");
        let identity = std::sync::Arc::as_ptr(source) as *const () as usize;
        let condition = matches!(proposition, Proposition::ConditionIs(..));
        let inputs = if condition {
            &mut state.condition_pointer_fact_inputs
        } else {
            &mut state.pointer_fact_inputs
        };
        let order = if insert {
            inputs.insert(identity, source.clone())
        } else {
            let Some(order) = inputs.remove(&identity) else {
                return;
            };
            order
        };
        let order = (condition, order);
        for (pointer, key) in keys {
            let address = state.register_pointer_address(&pointer);
            state
                .terms
                .adjust_pointer_fact(address, key, order, source, insert);
        }
        // A contract fact names its function value first; the values after
        // it fix the contract's value parameters.
        if let Proposition::Predicate { name, arguments } = proposition
            && FunctionContract::surface_name_from_predicate(name).is_some()
            && matches!(
                arguments.as_slice(),
                [Term::ExecutionState(_), Term::ProgramValue(ProgramValue::Pointer(_)), values @ ..]
                    if values.iter().all(|value| matches!(value, Term::ProgramValue(_)))
            )
        {
            let address = state.register_pointer_address(&predicate.expect("contract pointer").0);
            state.terms.adjust_pointer_fact(
                address,
                terms::PointerFactKey::FunctionContracts,
                order,
                source,
                insert,
            );
        }
    }

    fn pointer_fact_candidates(
        &self,
        pointer: &Pointer,
        key: &terms::PointerFactKey,
    ) -> terms::PointerFactBucket {
        let address = self
            .address_class(pointer)
            .expect("registered pointer address");
        self.state
            .lock()
            .expect("equality graph")
            .terms
            .pointer_facts(address, key)
    }

    pub(in crate::kernel) fn knows_pointer_predicate(
        &self,
        proposition: &crate::kernel::Proposition,
    ) -> bool {
        use crate::kernel::{ProgramValue, Proposition, Term};
        let Some((pointer, key)) = Self::pointer_predicate_key(proposition) else {
            return false;
        };
        let Proposition::Predicate { name, arguments } = proposition else {
            return false;
        };
        self.pointer_fact_candidates(&pointer, &key)
            .get(&String::new())
            .cloned()
            .unwrap_or_default()
            .iter()
            .any(|(_, source)| {
                crate::instrumentation::record_deterministic_work(1);
                let Proposition::Predicate {
                    name: source_name,
                    arguments: source_arguments,
                } = source.proposition()
                else {
                    return false;
                };
                name == source_name
                    && arguments.len() == source_arguments.len()
                    && arguments.iter().zip(source_arguments).all(|(left, right)| {
                        crate::instrumentation::record_deterministic_work(1);
                        match (left, right) {
                            (
                                Term::ProgramValue(ProgramValue::Pointer(left)),
                                Term::ProgramValue(ProgramValue::Pointer(right)),
                            ) => {
                                left.program_type() == right.program_type()
                                    && left.pointee_volatile() == right.pointee_volatile()
                                    && self.knows_condition(
                                        &crate::kernel::ConditionTerm::PointerValueEqual(
                                            Box::new(left.clone()),
                                            Box::new(right.clone()),
                                        ),
                                        true,
                                    )
                            }
                            _ => left == right,
                        }
                    })
            })
    }

    /// The coverage facts of the opaque extent whose start is `start`, and of
    /// every extent a pointer equality has identified with it.
    pub(in crate::kernel) fn subobject_coverage_facts(
        &self,
        start: &Pointer,
    ) -> Vec<crate::kernel::Proposition> {
        use crate::kernel::{PointerValue, ProgramType, SUBOBJECT_COVERS_PREDICATE_PREFIX};
        [3, 4]
            .into_iter()
            .flat_map(|arity| {
                let key = terms::PointerFactKey::PredicateShape(
                    SUBOBJECT_COVERS_PREDICATE_PREFIX.to_string(),
                    arity,
                    0,
                    PointerValue::new(start.clone(), ProgramType::VoidPointer).program_type(),
                );
                self.pointer_fact_candidates(start, &key)
                    .iter()
                    .flat_map(|(_, sources)| sources.iter())
                    .map(|(_, source)| {
                        crate::instrumentation::record_deterministic_work(1);
                        source.proposition().clone()
                    })
                    .collect::<Vec<_>>()
            })
            .collect()
    }

    /// Call consumers use the same class-bucket mechanism as predicates.
    /// The caller still checks the declared contract's exact call signature.
    /// A contract appears once for each distinct list of values its facts
    /// fix for its value parameters: once for a contract with none.
    pub(in crate::kernel) fn pointer_function_contracts(
        &self,
        pointer: &Pointer,
    ) -> impl Iterator<Item = (String, crate::kernel::Proposition)> {
        self.pointer_fact_candidates(pointer, &terms::PointerFactKey::FunctionContracts)
            .iter()
            .map(|(group, sources)| {
                crate::instrumentation::record_deterministic_work(1);
                let name = group
                    .split_once(terms::CONTRACT_VALUES_SEPARATOR)
                    .map_or(group.as_str(), |(name, _)| name);
                (
                    name.to_string(),
                    sources
                        .iter()
                        .next()
                        .expect("nonempty contract sources")
                        .1
                        .proposition()
                        .clone(),
                )
            })
            .collect::<Vec<_>>()
            .into_iter()
    }
}
