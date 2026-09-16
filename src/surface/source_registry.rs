use super::*;

/// Proof-local identity of the ordinary C function whose written entry
/// requirements are being used.  `source_unit` is the canonical key from the
/// verified-source map, not a display path recovered later.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::surface) struct CallerSourceOwnerId {
    pub(in crate::surface) source_unit: String,
    pub(in crate::surface) declaration_name: String,
}

impl CallerSourceOwnerId {
    pub(in crate::surface) fn ordinary(
        source_unit: impl Into<String>,
        declaration_name: impl Into<String>,
    ) -> Self {
        Self {
            source_unit: source_unit.into(),
            declaration_name: declaration_name.into(),
        }
    }
}

/// Stable identity of one outer requirement declaration in an ordinary
/// caller.  This ordinal is never interchangeable with a lowered fact index.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::surface) struct RequirementSourceId {
    pub(in crate::surface) owner: CallerSourceOwnerId,
    pub(in crate::surface) outer_ordinal: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) enum RequirementFactRole {
    Principal { unfolding_path: Vec<usize> },
    LoweringGuard { ordinal: usize },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) enum EntryFactOrigin {
    Requirement {
        source_id: RequirementSourceId,
        role: RequirementFactRole,
    },
    Derived,
}

/// Bounded source leaf retained after a checked `choose` projection.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub(in crate::surface) struct ProjectionSourceToken {
    pub(in crate::surface) source_id: RequirementSourceId,
    pub(in crate::surface) connective_path: Vec<usize>,
}

/// Shallow lookup key for a direct caller predicate argument.  Exact
/// propositions and expressions remain validation payloads, never map keys.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[allow(dead_code)]
pub(in crate::surface) struct CallerRequirementKey {
    pub(in crate::surface) predicate_name: String,
    pub(in crate::surface) predicate_argument_slot: usize,
    pub(in crate::surface) caller_parameter_slot: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub(in crate::surface) struct CallerRequirementRecord {
    pub(in crate::surface) source_id: RequirementSourceId,
    pub(in crate::surface) source_proposition: ClickProposition,
    pub(in crate::surface) key: CallerRequirementKey,
    pub(in crate::surface) principal_fact_index: usize,
    pub(in crate::surface) principal_fact: Proposition,
    pub(in crate::surface) source_arguments: Vec<ContractExpression>,
    pub(in crate::surface) entry_snapshot: crate::kernel::CMemorySnapshotIdentity,
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub(in crate::surface) struct CallerRequirementSelection {
    pub(in crate::surface) source_id: RequirementSourceId,
    pub(in crate::surface) principal_fact_index: usize,
    pub(in crate::surface) principal_fact: Proposition,
    pub(in crate::surface) source_proposition: ClickProposition,
    pub(in crate::surface) source_arguments: Vec<ContractExpression>,
    pub(in crate::surface) entry_snapshot: crate::kernel::CMemorySnapshotIdentity,
}

/// The proof-local lookup table for direct caller predicate requirements.
///
/// The table is deliberately separate from [`FunctionSourceRegistry`]: the
/// latter owns file-scoped callee declarations, while this index owns the
/// entry facts and snapshot of one proof.  Keys contain only the shallow
/// shape needed to route a query.  The exact source arguments, fact, and
/// snapshot stay in the bounded candidate records and are revalidated by the
/// lookup.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub(in crate::surface) struct CallerRequirementIndex {
    buckets: PersistentMap<CallerRequirementKey, CallerRequirementBucket>,
    /// Exact source-ID view used by checked `Choose`.  The key is never an
    /// array offset; an `None` value is a permanent ambiguity tombstone.
    by_source: PersistentMap<RequirementSourceId, Option<CallerRequirementSelection>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CallerRequirementBucket {
    /// At most eight candidates are retained.  `overfull` is a permanent
    /// fail-closed marker: no query may select an arbitrary ninth candidate.
    candidates: Vec<CallerRequirementRecord>,
    overfull: bool,
}

const MAX_CALLER_REQUIREMENT_CANDIDATES: usize = 8;

impl CallerRequirementIndex {
    /// Constructs the direct caller index from the entry-origin stream.  The
    /// stream is already aligned with `entry_facts`; this routine never scans
    /// propositions looking for a plausible match.  Requirements that are
    /// not top-level predicate calls, or whose selected argument is not a
    /// direct caller parameter, are intentionally omitted.
    pub(in crate::surface) fn from_entry_facts(
        owner: CallerSourceOwnerId,
        function_block: &FunctionBlock,
        parameters: &[syntax::C0Parameter],
        entry_facts: &[Proposition],
        entry_fact_origins: &[EntryFactOrigin],
        entry_snapshot: crate::kernel::CMemorySnapshotIdentity,
    ) -> Self {
        if entry_facts.len() != entry_fact_origins.len() {
            return Self::default();
        }

        // A source declaration can have several derived facts, but exactly
        // one principal fact is the source selection authority.  Populate
        // the source-ID view directly from the aligned stream; a duplicate
        // becomes an ambiguity tombstone rather than a first-match choice.
        let mut principals =
            PersistentMap::<RequirementSourceId, Option<(usize, Proposition)>>::default();
        for (fact_index, (fact, origin)) in entry_facts.iter().zip(entry_fact_origins).enumerate() {
            let EntryFactOrigin::Requirement { source_id, role } = origin else {
                continue;
            };
            if source_id.owner != owner || !matches!(role, RequirementFactRole::Principal { .. }) {
                continue;
            }
            if principals.get(source_id).is_some() {
                principals.insert(source_id.clone(), None);
            } else {
                principals.insert(source_id.clone(), Some((fact_index, fact.clone())));
            }
        }

        let parameter_slots = parameters
            .iter()
            .enumerate()
            .map(|(slot, parameter)| (parameter.name(), slot))
            .collect::<BTreeMap<_, _>>();
        let mut index = Self::default();
        for (outer_ordinal, requirement) in function_block.requires().iter().enumerate() {
            let source_id = RequirementSourceId {
                owner: owner.clone(),
                outer_ordinal,
            };
            let Some(principal_resolution) = principals.get(&source_id) else {
                continue;
            };
            let Some((principal_fact_index, principal_fact)) = principal_resolution else {
                // Preserve the fail-closed result explicitly for checked
                // source-ID resolution, even when duplicate principal facts
                // cannot produce a by-key candidate.
                index.by_source.insert(source_id, None);
                continue;
            };
            let Requirement::Proposition(source_proposition) = requirement.inner() else {
                continue;
            };
            let source_arguments = match source_proposition {
                ClickProposition::PredicateCall { arguments, .. } => arguments.clone(),
                _ => Vec::new(),
            };
            let source_selection = CallerRequirementSelection {
                source_id: source_id.clone(),
                principal_fact_index: *principal_fact_index,
                principal_fact: principal_fact.clone(),
                source_proposition: source_proposition.clone(),
                source_arguments: source_arguments.clone(),
                entry_snapshot,
            };
            index
                .by_source
                .insert(source_id.clone(), Some(source_selection.clone()));

            let ClickProposition::PredicateCall { name, arguments } = source_proposition else {
                continue;
            };

            // There is one record for each direct parameter argument.  The
            // query's argument slot disambiguates which one the callee clause
            // selected; all other argument expressions remain exact payload.
            for (predicate_argument_slot, argument) in arguments.iter().enumerate() {
                let Some(parameter_name) = direct_parameter_name(argument) else {
                    continue;
                };
                let Some(&caller_parameter_slot) = parameter_slots.get(parameter_name) else {
                    continue;
                };
                let record = CallerRequirementRecord {
                    source_id: source_id.clone(),
                    source_proposition: ClickProposition::PredicateCall {
                        name: name.clone(),
                        arguments: arguments.clone(),
                    },
                    key: CallerRequirementKey {
                        predicate_name: name.clone(),
                        predicate_argument_slot,
                        caller_parameter_slot,
                    },
                    principal_fact_index: *principal_fact_index,
                    principal_fact: principal_fact.clone(),
                    source_arguments: source_arguments.clone(),
                    entry_snapshot,
                };
                index.insert(record);
            }
        }
        index
    }

    fn insert(&mut self, record: CallerRequirementRecord) {
        let key = record.key.clone();
        let mut bucket = self
            .buckets
            .get(&key)
            .cloned()
            .unwrap_or(CallerRequirementBucket {
                candidates: Vec::new(),
                overfull: false,
            });
        if bucket.candidates.len() < MAX_CALLER_REQUIREMENT_CANDIDATES {
            bucket.candidates.push(record);
        } else {
            bucket.overfull = true;
        }
        self.buckets.insert(key, bucket);
    }

    /// Performs the bounded exact selection.  A missing, stale, conflicting,
    /// or overfull bucket returns `None`; the caller must preserve the
    /// original structured unmet requirement in that case.
    pub(in crate::surface) fn lookup_unique_caller_requirement(
        &self,
        owner: &CallerSourceOwnerId,
        predicate_name: &str,
        predicate_argument_slot: usize,
        caller_parameter_slot: usize,
        source_arguments: &[ContractExpression],
        expected_entry_snapshot: crate::kernel::CMemorySnapshotIdentity,
    ) -> Option<CallerRequirementSelection> {
        let key = CallerRequirementKey {
            predicate_name: predicate_name.to_string(),
            predicate_argument_slot,
            caller_parameter_slot,
        };
        let bucket = self.buckets.get(&key)?;
        if bucket.overfull {
            return None;
        }
        let mut matches = bucket.candidates.iter().filter(|candidate| {
            candidate.source_id.owner == *owner
                && candidate.source_arguments == source_arguments
                && candidate.entry_snapshot == expected_entry_snapshot
        });
        let candidate = matches.next()?;
        // Two exact records are still ambiguous without an explicit source
        // ID, even if their declarations happen to look identical.
        if matches.next().is_some() {
            return None;
        }
        Some(CallerRequirementSelection {
            source_id: candidate.source_id.clone(),
            principal_fact_index: candidate.principal_fact_index,
            principal_fact: candidate.principal_fact.clone(),
            source_proposition: candidate.source_proposition.clone(),
            source_arguments: candidate.source_arguments.clone(),
            entry_snapshot: candidate.entry_snapshot,
        })
    }

    /// Resolves an outer source declaration for checked projection.  The
    /// final fact index is returned as payload and is checked independently
    /// by the caller against its active fixed-state view.
    pub(in crate::surface) fn lookup_source_requirement(
        &self,
        source_id: &RequirementSourceId,
    ) -> Option<CallerRequirementSelection> {
        self.by_source.get(source_id)?.clone()
    }

    #[cfg(test)]
    fn bucket_count(&self) -> usize {
        self.buckets.len()
    }

    #[cfg(test)]
    fn source_count(&self) -> usize {
        self.by_source.len()
    }

    #[cfg(test)]
    fn source_candidate(
        &self,
        source_id: &RequirementSourceId,
    ) -> Option<CallerRequirementSelection> {
        self.lookup_source_requirement(source_id)
    }

    #[cfg(test)]
    fn candidate_count(&self, key: &CallerRequirementKey) -> usize {
        self.buckets
            .get(key)
            .map_or(0, |bucket| bucket.candidates.len())
    }

    #[cfg(test)]
    fn key_lookup_comparisons(&self, key: &CallerRequirementKey) -> usize {
        self.buckets.lookup_comparisons(key)
    }
}

fn direct_parameter_name(expression: &ContractExpression) -> Option<&str> {
    match expression {
        ContractExpression::CFragment(CExpression::Variable(name)) => Some(name),
        _ => None,
    }
}

/// The source-side forms that can be re-lowered for an ordinary function
/// requirement.  The source ordinal is kept separately so an outer label is
/// preserved without copying label syntax into the retry carrier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) enum FunctionRequirementSource {
    Proposition(ClickProposition),
    LoadableSegment(ContractSegment),
}

/// The source requirements for one function, indexed by the outer
/// `FunctionBlock::requires()` ordinal.  `None` is deliberate for resource
/// clauses and forms that cannot be safely re-lowered as a proposition.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub(in crate::surface) struct FunctionSourceRequirements {
    requirements: Vec<Option<FunctionRequirementSource>>,
}

impl FunctionSourceRequirements {
    fn from_function_block(function: &FunctionBlock) -> Self {
        let requirements = function
            .requires()
            .iter()
            .map(|requirement| match requirement.inner() {
                Requirement::Proposition(proposition) => {
                    Some(FunctionRequirementSource::Proposition(proposition.clone()))
                }
                Requirement::LoadableSegment { segment } => {
                    Some(FunctionRequirementSource::LoadableSegment(segment.clone()))
                }
                Requirement::Resource(_) | Requirement::Labeled { .. } => None,
            })
            .collect();
        Self { requirements }
    }

    /// Returns the source form at the exact outer requirement ordinal.  A
    /// missing ordinal and an intentionally unresolvable source both fail
    /// closed as `None`.
    #[allow(dead_code)]
    pub(in crate::surface) fn get(&self, ordinal: usize) -> Option<&FunctionRequirementSource> {
        self.requirements.get(ordinal).and_then(Option::as_ref)
    }

    #[cfg(test)]
    fn entries(&self) -> &[Option<FunctionRequirementSource>] {
        &self.requirements
    }
}

/// Immutable file-scoped source lookup for ordinary function requirements.
/// The persistent AVL map provides logarithmic function-name lookup; each source ordinal
/// is then a direct vector access.  It is intentionally built before proof
/// contexts are created and shared by `Arc` through their constants. Named
/// callback and explicit `StepContract` interfaces are deliberately absent:
/// those source definitions are selected by their interface name through
/// `PredicateEnvironment::contract_definition`.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub(in crate::surface) struct FunctionSourceRegistry {
    functions: PersistentMap<String, FunctionSourceRequirements>,
}

impl FunctionSourceRegistry {
    pub(in crate::surface) fn from_function_blocks(
        function_blocks: &[FunctionBlock],
    ) -> Result<Self, ClickError> {
        let mut functions = PersistentMap::default();
        for function in function_blocks {
            let name = function.signature().name().to_string();
            if functions.get(&name).is_some() {
                return Err(ClickError::new(format!(
                    "ambiguous ordinary function source requirements for `{name}`"
                )));
            }
            functions.insert(
                name,
                FunctionSourceRequirements::from_function_block(function),
            );
        }
        Ok(Self { functions })
    }

    /// Finds one ordinary function's source requirements by stable function
    /// name.  No project-wide scan occurs at retry time.
    #[allow(dead_code)]
    pub(in crate::surface) fn ordinary_function(
        &self,
        name: &str,
    ) -> Option<&FunctionSourceRequirements> {
        self.functions.get(name)
    }

    #[cfg(test)]
    fn len(&self) -> usize {
        self.functions.len()
    }

    #[cfg(test)]
    fn lookup_comparisons(&self, name: &str) -> usize {
        self.functions.lookup_comparisons(&name.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn function(name: &str, requires: Vec<Requirement>) -> FunctionBlock {
        function_with_parameters(name, requires, &[])
    }

    fn function_with_parameters(
        name: &str,
        requires: Vec<Requirement>,
        parameter_names: &[&str],
    ) -> FunctionBlock {
        FunctionBlock {
            signature: FunctionSignature {
                return_type: C0Type::Int32,
                return_pointee_constant: false,
                name: name.to_string(),
                parameters: parameter_names
                    .iter()
                    .map(|name| FunctionParameter {
                        click_type: ClickType::C(C0Type::Int32),
                        name: (*name).to_string(),
                        struct_name: None,
                        function_pointer_signature: None,
                        constant: false,
                        pointee_constant: false,
                    })
                    .collect(),
                exceptional_type: None,
                declared_loadable_bytes: Vec::new(),
            },
            external: true,
            one_call_proof: false,
            requirement_label_indices: requires
                .iter()
                .enumerate()
                .filter_map(|(index, requirement)| {
                    requirement.label().map(|label| (label.to_string(), index))
                })
                .collect(),
            requires,
            decreases: None,
            structural_clauses: Vec::new(),
            constructs: Vec::new(),
            ensures: Vec::new(),
            exceptional_ensures: Vec::new(),
            requirement_source_clauses: Vec::new(),
            ensure_source_clauses: Vec::new(),
            grouped_proof: None,
        }
    }

    fn owner() -> CallerSourceOwnerId {
        CallerSourceOwnerId::ordinary("test.c", "caller")
    }

    fn snapshot() -> crate::kernel::CMemorySnapshotIdentity {
        crate::kernel::CMemorySnapshotIdentity::of(&crate::kernel::CMemory::new())
    }

    fn direct_predicate(name: &str, parameter: &str) -> Requirement {
        Requirement::Proposition(ClickProposition::PredicateCall {
            name: name.to_string(),
            arguments: vec![ContractExpression::CFragment(CExpression::Variable(
                parameter.to_string(),
            ))],
        })
    }

    fn entry_origins(
        owner: &CallerSourceOwnerId,
        ordinals: impl IntoIterator<Item = usize>,
    ) -> Vec<EntryFactOrigin> {
        ordinals
            .into_iter()
            .map(|ordinal| EntryFactOrigin::Requirement {
                source_id: RequirementSourceId {
                    owner: owner.clone(),
                    outer_ordinal: ordinal,
                },
                role: RequirementFactRole::Principal {
                    unfolding_path: Vec::new(),
                },
            })
            .collect()
    }

    fn principal_facts(count: usize) -> Vec<Proposition> {
        (0..count)
            .map(|index| {
                Proposition::ConditionIs(ConditionTerm::Variable(Variable(index as u64)), true)
            })
            .collect()
    }

    fn proposition(name: &str) -> Requirement {
        Requirement::Proposition(ClickProposition::PredicateCall {
            name: name.to_string(),
            arguments: Vec::new(),
        })
    }

    #[test]
    fn preserves_outer_ordinals_and_fails_closed_for_resources() {
        let requirements = vec![
            Requirement::Labeled {
                label: "labelled".to_string(),
                requirement: Box::new(proposition("p")),
            },
            Requirement::Resource(ResourceClause::OwnMemory(ContractSegment {
                state: ContractSegmentState::Current,
                base: CExpression::Variable("p".to_string()),
                start: CExpression::Value(int32(0)),
                end: CExpression::Value(int32(1)),
                surface: ContractSegmentSurface::Object("p".to_string()),
            })),
            proposition("q"),
        ];
        let block = function("target", requirements);
        let registry = FunctionSourceRegistry::from_function_blocks(&[block]).unwrap();
        let source = registry.ordinary_function("target").unwrap();
        assert_eq!(source.entries().len(), 3);
        assert!(matches!(
            source.get(0),
            Some(FunctionRequirementSource::Proposition(ClickProposition::PredicateCall {
                name,
                ..
            })) if name == "p"
        ));
        assert!(source.entries()[1].is_none());
        assert!(source.get(3).is_none());
        assert!(matches!(
            source.get(2),
            Some(FunctionRequirementSource::Proposition(ClickProposition::PredicateCall {
                name,
                ..
            })) if name == "q"
        ));
    }

    #[test]
    fn duplicate_names_fail_closed() {
        let first = function("same", vec![proposition("first")]);
        let second = function("same", vec![proposition("second")]);
        let error = FunctionSourceRegistry::from_function_blocks(&[first, second])
            .expect_err("duplicate ordinary source names must be rejected");
        assert!(
            error
                .message()
                .contains("ambiguous ordinary function source")
        );
    }

    #[test]
    fn unrelated_function_count_does_not_change_one_entry_shape() {
        for count in [1, 8, 32, 128, 256] {
            let mut functions = vec![function("target", vec![proposition("target")])];
            for index in 0..count {
                functions.push(function(
                    &format!("unrelated_{index:03}"),
                    vec![proposition("u")],
                ));
            }
            let registry = FunctionSourceRegistry::from_function_blocks(&functions).unwrap();
            assert!(registry.ordinary_function("target").is_some());
            let comparisons = registry.lookup_comparisons("target");
            assert!(
                comparisons <= 2 * ((registry.len() + 1).ilog2() as usize + 1),
                "lookup comparisons {comparisons} exceeded logarithmic bound for {} entries",
                registry.len()
            );
        }
    }

    #[test]
    fn caller_index_keeps_source_ordinal_separate_from_fact_index() {
        let owner = owner();
        let block = function_with_parameters(
            "caller",
            vec![
                Requirement::Proposition(ClickProposition::Comparison {
                    left: ContractExpression::IntegerLiteral("0".to_string()),
                    operator: ComparisonOperator::Equal,
                    right: ContractExpression::IntegerLiteral("0".to_string()),
                }),
                Requirement::Resource(ResourceClause::OwnMemory(ContractSegment {
                    state: ContractSegmentState::Current,
                    base: CExpression::Variable("p".to_string()),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Value(int32(1)),
                    surface: ContractSegmentSurface::Object("p".to_string()),
                })),
                direct_predicate("readable", "p"),
            ],
            &["p"],
        );
        let facts = principal_facts(5);
        let snapshot_value = snapshot();
        let origins = vec![
            EntryFactOrigin::Derived,
            EntryFactOrigin::Derived,
            EntryFactOrigin::Derived,
            EntryFactOrigin::Derived,
            EntryFactOrigin::Requirement {
                source_id: RequirementSourceId {
                    owner: owner.clone(),
                    outer_ordinal: 2,
                },
                role: RequirementFactRole::Principal {
                    unfolding_path: Vec::new(),
                },
            },
        ];
        let index = CallerRequirementIndex::from_entry_facts(
            owner.clone(),
            &block,
            &[syntax::C0Parameter::new(
                C0Type::Int32,
                "p".to_string(),
                None,
            )],
            &facts,
            &origins,
            snapshot_value,
        );
        let source_arguments = vec![ContractExpression::CFragment(CExpression::Variable(
            "p".to_string(),
        ))];
        let selected = index
            .lookup_unique_caller_requirement(
                &owner,
                "readable",
                0,
                0,
                &source_arguments,
                snapshot_value,
            )
            .expect("the nonzero source ordinal must be indexed");
        assert_eq!(selected.source_id.outer_ordinal, 2);
        assert_eq!(selected.principal_fact_index, 4);
        assert_eq!(selected.principal_fact, facts[4]);
        let source_id = RequirementSourceId {
            owner,
            outer_ordinal: 2,
        };
        let source = index
            .source_candidate(&source_id)
            .expect("source-ID view must retain the principal fact");
        assert_eq!(source.principal_fact_index, 4);
        assert_eq!(source.principal_fact, facts[4]);
        assert_ne!(
            selected.source_id.outer_ordinal,
            selected.principal_fact_index
        );
        assert_eq!(index.source_count(), 1);
    }

    #[test]
    fn caller_index_scales_and_caps_candidate_validation() {
        let owner = owner();
        for count in [1, 8, 64, 512] {
            let snapshot_value = snapshot();
            let requires = (0..count)
                .map(|index| direct_predicate(&format!("predicate_{index}"), "p"))
                .collect::<Vec<_>>();
            let block = function_with_parameters("caller", requires, &["p"]);
            let facts = principal_facts(count);
            let origins = entry_origins(&owner, 0..count);
            let index = CallerRequirementIndex::from_entry_facts(
                owner.clone(),
                &block,
                &[syntax::C0Parameter::new(
                    C0Type::Int32,
                    "p".to_string(),
                    None,
                )],
                &facts,
                &origins,
                snapshot_value,
            );
            assert_eq!(index.bucket_count(), count);
            let source_arguments = vec![ContractExpression::CFragment(CExpression::Variable(
                "p".to_string(),
            ))];
            let selected = index
                .lookup_unique_caller_requirement(
                    &owner,
                    &format!("predicate_{}", count - 1),
                    0,
                    0,
                    &source_arguments,
                    snapshot_value,
                )
                .expect("unique direct requirement should be selectable");
            assert_eq!(selected.source_id.outer_ordinal, count - 1);
            let key = CallerRequirementKey {
                predicate_name: format!("predicate_{}", count - 1),
                predicate_argument_slot: 0,
                caller_parameter_slot: 0,
            };
            let comparisons = index.key_lookup_comparisons(&key);
            assert!(
                comparisons <= 2 * ((index.bucket_count() + 1).ilog2() as usize + 1),
                "shallow index lookup used {comparisons} comparisons for {} buckets",
                index.bucket_count()
            );
            assert!(index.candidate_count(&key) <= 8);
        }
    }

    #[test]
    fn caller_index_rejects_duplicates_and_overfull_buckets() {
        let owner = owner();
        let snapshot_value = snapshot();
        let source_arguments = vec![ContractExpression::CFragment(CExpression::Variable(
            "p".to_string(),
        ))];
        let duplicate_requires = vec![direct_predicate("readable", "p"); 2];
        let duplicate_block = function_with_parameters("caller", duplicate_requires, &["p"]);
        let duplicate_index = CallerRequirementIndex::from_entry_facts(
            owner.clone(),
            &duplicate_block,
            &[syntax::C0Parameter::new(
                C0Type::Int32,
                "p".to_string(),
                None,
            )],
            &principal_facts(2),
            &entry_origins(&owner, 0..2),
            snapshot_value,
        );
        assert!(
            duplicate_index
                .lookup_unique_caller_requirement(
                    &owner,
                    "readable",
                    0,
                    0,
                    &source_arguments,
                    snapshot_value,
                )
                .is_none()
        );

        let duplicate_source_index = CallerRequirementIndex::from_entry_facts(
            owner.clone(),
            &function_with_parameters("caller", vec![direct_predicate("readable", "p")], &["p"]),
            &[syntax::C0Parameter::new(
                C0Type::Int32,
                "p".to_string(),
                None,
            )],
            &principal_facts(2),
            &[
                EntryFactOrigin::Requirement {
                    source_id: RequirementSourceId {
                        owner: owner.clone(),
                        outer_ordinal: 0,
                    },
                    role: RequirementFactRole::Principal {
                        unfolding_path: Vec::new(),
                    },
                },
                EntryFactOrigin::Requirement {
                    source_id: RequirementSourceId {
                        owner: owner.clone(),
                        outer_ordinal: 0,
                    },
                    role: RequirementFactRole::Principal {
                        unfolding_path: Vec::new(),
                    },
                },
            ],
            snapshot_value,
        );
        assert!(
            duplicate_source_index
                .lookup_source_requirement(&RequirementSourceId {
                    owner: owner.clone(),
                    outer_ordinal: 0,
                })
                .is_none()
        );

        let overfull_requires = (0..9)
            .map(|_| direct_predicate("readable", "p"))
            .collect::<Vec<_>>();
        let overfull_block = function_with_parameters("caller", overfull_requires, &["p"]);
        let overfull_index = CallerRequirementIndex::from_entry_facts(
            owner.clone(),
            &overfull_block,
            &[syntax::C0Parameter::new(
                C0Type::Int32,
                "p".to_string(),
                None,
            )],
            &principal_facts(9),
            &entry_origins(&owner, 0..9),
            snapshot_value,
        );
        let key = CallerRequirementKey {
            predicate_name: "readable".to_string(),
            predicate_argument_slot: 0,
            caller_parameter_slot: 0,
        };
        assert_eq!(overfull_index.candidate_count(&key), 8);
        assert!(
            overfull_index
                .lookup_unique_caller_requirement(
                    &owner,
                    "readable",
                    0,
                    0,
                    &source_arguments,
                    snapshot_value,
                )
                .is_none()
        );
    }

    #[test]
    fn caller_index_fails_closed_for_unsupported_or_stale_candidates() {
        let owner = owner();
        let snapshot_value = snapshot();
        let block = function_with_parameters(
            "caller",
            vec![
                Requirement::Proposition(ClickProposition::And(
                    Box::new(ClickProposition::PredicateCall {
                        name: "nested".to_string(),
                        arguments: vec![ContractExpression::CFragment(CExpression::Variable(
                            "p".to_string(),
                        ))],
                    }),
                    Box::new(ClickProposition::PredicateCall {
                        name: "other".to_string(),
                        arguments: vec![],
                    }),
                )),
                Requirement::Resource(ResourceClause::OwnMemory(ContractSegment {
                    state: ContractSegmentState::Current,
                    base: CExpression::Variable("p".to_string()),
                    start: CExpression::Value(int32(0)),
                    end: CExpression::Value(int32(1)),
                    surface: ContractSegmentSurface::Object("p".to_string()),
                })),
            ],
            &["p"],
        );
        let index = CallerRequirementIndex::from_entry_facts(
            owner.clone(),
            &block,
            &[syntax::C0Parameter::new(
                C0Type::Int32,
                "p".to_string(),
                None,
            )],
            &principal_facts(2),
            &entry_origins(&owner, 0..2),
            snapshot_value,
        );
        let source_arguments = vec![ContractExpression::CFragment(CExpression::Variable(
            "p".to_string(),
        ))];
        assert!(
            index
                .lookup_unique_caller_requirement(
                    &owner,
                    "nested",
                    0,
                    0,
                    &source_arguments,
                    snapshot(),
                )
                .is_none()
        );

        let valid_block =
            function_with_parameters("caller", vec![direct_predicate("readable", "p")], &["p"]);
        let valid_index = CallerRequirementIndex::from_entry_facts(
            owner.clone(),
            &valid_block,
            &[syntax::C0Parameter::new(
                C0Type::Int32,
                "p".to_string(),
                None,
            )],
            &principal_facts(1),
            &entry_origins(&owner, [0]),
            snapshot_value,
        );
        assert!(
            valid_index
                .lookup_unique_caller_requirement(
                    &owner,
                    "readable",
                    0,
                    0,
                    &source_arguments,
                    crate::kernel::CMemorySnapshotIdentity::of(
                        &crate::kernel::CMemory::new().with_block("stale", 1),
                    ),
                )
                .is_none()
        );
    }
}
