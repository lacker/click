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
pub(in crate::surface) struct ProjectionSourceToken {
    pub(in crate::surface) source_id: RequirementSourceId,
    pub(in crate::surface) connective_path: Vec<usize>,
}

/// Shallow lookup key for a direct caller predicate argument.  Exact
/// propositions and expressions remain validation payloads, never map keys.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub(in crate::surface) struct CallerRequirementKey {
    pub(in crate::surface) predicate_name: String,
    pub(in crate::surface) predicate_argument_slot: usize,
    pub(in crate::surface) caller_parameter_slot: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
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
pub(in crate::surface) struct CallerRequirementSelection {
    pub(in crate::surface) source_id: RequirementSourceId,
    pub(in crate::surface) principal_fact_index: usize,
    pub(in crate::surface) principal_fact: Proposition,
    pub(in crate::surface) source_proposition: ClickProposition,
    pub(in crate::surface) source_arguments: Vec<ContractExpression>,
    pub(in crate::surface) entry_snapshot: crate::kernel::CMemorySnapshotIdentity,
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
        FunctionBlock {
            signature: FunctionSignature {
                return_type: C0Type::Int32,
                return_pointee_constant: false,
                name: name.to_string(),
                parameters: Vec::new(),
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
            grouped_proof: None,
        }
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
}
