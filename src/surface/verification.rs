use super::*;

fn collect_applied_theorems(tactics: &[ProofTactic], names: &mut BTreeSet<String>) {
    for tactic in tactics {
        match tactic {
            ProofTactic::ApplyTheorem(application)
            | ProofTactic::ApplyTheoremUsing { application, .. } => {
                names.insert(application.name.clone());
            }
            ProofTactic::Have(proof_have) => {
                if let SourceProof::Script(tactics) = &proof_have.proof {
                    collect_applied_theorems(tactics, names);
                }
            }
            ProofTactic::Open(proof_open) => {
                collect_applied_theorems(&proof_open.tactics, names);
            }
            ProofTactic::If(proof_if) => {
                collect_applied_theorems(&proof_if.then_tactics, names);
                collect_applied_theorems(&proof_if.else_tactics, names);
            }
            ProofTactic::Cases(proof_cases) => {
                collect_applied_theorems(&proof_cases.left_tactics, names);
                collect_applied_theorems(&proof_cases.right_tactics, names);
            }
            ProofTactic::Branch(proof_branch) => {
                collect_applied_theorems(&proof_branch.then_tactics, names);
                collect_applied_theorems(&proof_branch.else_tactics, names);
            }
            ProofTactic::Loop(clause) => {
                for item in &clause.items {
                    if let SourceProof::Script(tactics) = &item.proof {
                        collect_applied_theorems(tactics, names);
                    }
                }
                for proof in [
                    clause.initialize_proof.as_ref(),
                    clause.preserve_proof.as_ref(),
                ]
                .into_iter()
                .flatten()
                {
                    if let SourceProof::Script(tactics) = proof {
                        collect_applied_theorems(tactics, names);
                    }
                }
            }
            _ => {}
        }
    }
}

fn collect_applied_theorems_from_proof(proof: &SourceProof, names: &mut BTreeSet<String>) {
    if let SourceProof::Script(tactics) = proof {
        collect_applied_theorems(tactics, names);
    }
}

fn collect_function_theorem_dependencies(function: &FunctionBlock, names: &mut BTreeSet<String>) {
    if let Some(proof) = function.grouped_proof() {
        collect_applied_theorems_from_proof(proof, names);
    }
    for clause in function.ensures() {
        collect_applied_theorems_from_proof(&clause.proof, names);
    }
    for clause in function.effects() {
        collect_applied_theorems_from_proof(&clause.proof, names);
    }
    for clause in function.structural_clauses() {
        for item in &clause.items {
            collect_applied_theorems_from_proof(&item.proof, names);
        }
        for proof in [
            clause.initialize_proof.as_ref(),
            clause.preserve_proof.as_ref(),
        ]
        .into_iter()
        .flatten()
        {
            collect_applied_theorems_from_proof(proof, names);
        }
    }
}

fn selected_theorem_definitions(
    file: &ClickFile,
    definitions: &[TheoremDefinition],
    standard_library_count: usize,
    selected_functions: Option<&BTreeSet<String>>,
    verification_target: Option<&VerificationTarget>,
) -> Vec<TheoremDefinition> {
    let Some(selected_functions) = selected_functions else {
        return definitions.to_vec();
    };
    let mut required = BTreeSet::new();
    for function in file.function_blocks() {
        if selected_functions.contains(function.signature().name()) {
            collect_function_theorem_dependencies(function, &mut required);
        }
    }
    if let Some(VerificationTarget::Theorem(name)) = verification_target {
        required.insert(name.clone());
    }

    let definitions_by_name = definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    let mut frontier = required.iter().cloned().collect::<Vec<_>>();
    while let Some(name) = frontier.pop() {
        let Some(definition) = definitions_by_name.get(name.as_str()) else {
            continue;
        };
        let mut dependencies = BTreeSet::new();
        for ensure in definition.ensures() {
            collect_applied_theorems_from_proof(&ensure.proof, &mut dependencies);
        }
        for dependency in dependencies {
            if required.insert(dependency.clone()) {
                frontier.push(dependency);
            }
        }
    }
    definitions
        .iter()
        .enumerate()
        .filter(|(index, definition)| {
            *index < standard_library_count || required.contains(definition.name())
        })
        .map(|(_, definition)| definition)
        .cloned()
        .collect()
}

pub fn parse(source: &str) -> Result<ClickFile, ClickError> {
    parser::parse(source)
}

pub fn verify_click_theorems(click_source: &str) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let file = parse(click_source)?;
    verify_click_file_theorems(&file)
}

pub(in crate::surface) fn verify_click_file_theorems(
    file: &ClickFile,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let predicate_definitions = combined_predicate_definitions(file)?;
    let click_function_definitions = combined_click_function_definitions(file)?;
    let (theorem_definitions, stdlib_theorem_ensure_count) =
        combined_theorem_definitions_with_stdlib_ensure_count(file)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
    let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
        &click_function_definitions,
        file.algebraic_type_definitions(),
    );
    let verified = verify_theorem_definitions(
        &theorem_definitions,
        &predicate_environment,
        &click_function_environment,
    )?;
    Ok(verified
        .into_iter()
        .skip(stdlib_theorem_ensure_count)
        .collect())
}

pub(in crate::surface) fn verify_click_theorems_with_c_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let sources = c_sources.iter().copied().collect::<BTreeMap<_, _>>();
    let (struct_layouts, union_layouts, aggregate_objects, aggregate_array_objects) =
        parse_c_layouts(click_source, &sources)?;
    let file = parser::parse_with_layouts_and_aggregate_objects(
        click_source,
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
    )?;
    verify_click_file_theorems(&file)
}

pub(in crate::surface) fn parse_c0_click_file(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<ClickFile, ClickError> {
    let sources = c_sources.iter().copied().collect::<BTreeMap<_, _>>();
    let (struct_layouts, union_layouts, aggregate_objects, aggregate_array_objects) =
        parse_c_layouts(click_source, &sources)?;
    parser::parse_with_layouts_and_aggregate_objects(
        click_source,
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
    )
}

pub(in crate::surface) fn proof_unit_erased_click_file(
    mut file: ClickFile,
    target: &VerificationTarget,
) -> ClickFile {
    if let VerificationTarget::Theorem(target_name) = target {
        for theorem in &mut file.theorem_definitions {
            if theorem.name == *target_name {
                for ensure in &mut theorem.ensures {
                    ensure.proof = SourceProof::Default;
                }
            }
        }
    }
    let VerificationTarget::Function(target_name) = target else {
        return file;
    };
    for function in &mut file.function_blocks {
        if function.signature.name != *target_name {
            continue;
        }
        if function.grouped_proof.is_some() {
            function.grouped_proof = Some(SourceProof::Default);
        }
        for ensure in &mut function.ensures {
            ensure.proof = SourceProof::Default;
        }
        for effect in &mut function.effects {
            effect.proof = SourceProof::Default;
        }
        for clause in &mut function.structural_clauses {
            // Omitted loop-phase proofs and explicit default/expanded proofs
            // are all syntax for the selected function's proof unit.  Erase
            // presence as well as contents so inserting an expansion for an
            // omitted phase does not look like an interface change.
            clause.initialize_proof = None;
            clause.preserve_proof = None;
            for item in &mut clause.items {
                item.proof = SourceProof::Default;
            }
        }
    }
    file
}

pub fn verify_c0_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        verify_c0_sources_with_limits(click_source, c_sources)
    })
}

/// Runs one ordinary verification while filling in the given expansion
/// capture. Verification behaves identically with or without the capture;
/// only the capture's `result` differs.
pub(in crate::surface) fn verify_c0_sources_with_expansion_capture(
    click_source: &str,
    c_sources: &[(&str, &str)],
    expansion_capture: &mut ExpansionCapture,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        verify_c0_sources_with_environment(
            click_source,
            c_sources,
            None,
            None,
            Some(expansion_capture),
        )
        .map(|(verified, _)| verified)
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct C0IncrementalSelection {
    pub selected_functions: Vec<String>,
    pub reused_functions: Vec<String>,
    pub reasons: Vec<String>,
    pub full_rebuild: bool,
}

pub fn c0_function_names(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<String>, ClickError> {
    Ok(parse_c0_click_file(click_source, c_sources)?
        .function_blocks()
        .iter()
        .map(|function| function.signature().name().to_string())
        .collect())
}

/// Compares two parsed versions of one sidecar and returns the current
/// functions whose proofs may be affected. Comments and formatting disappear
/// during parsing; changes to shared logical definitions conservatively select
/// every current function. Function-local C or Click changes select that
/// function and its transitive callers in the union of the old and new call
/// graphs.
pub fn c0_incremental_selection(
    current_click_source: &str,
    current_c_sources: &[(&str, &str)],
    baseline_click_source: &str,
    baseline_c_sources: &[(&str, &str)],
) -> Result<C0IncrementalSelection, ClickError> {
    let current_file = parse_c0_click_file(current_click_source, current_c_sources)?;
    let baseline_file = parse_c0_click_file(baseline_click_source, baseline_c_sources)?;
    let current_source_map = current_c_sources
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    let baseline_source_map = baseline_c_sources
        .iter()
        .copied()
        .collect::<BTreeMap<_, _>>();
    let current_parsed = parse_verified_sources(&current_file, &current_source_map)?;
    let baseline_parsed = parse_verified_sources(&baseline_file, &baseline_source_map)?;
    let current_blocks = current_file
        .function_blocks()
        .iter()
        .map(|function| (function.signature().name().to_string(), function))
        .collect::<BTreeMap<_, _>>();
    let baseline_blocks = baseline_file
        .function_blocks()
        .iter()
        .map(|function| (function.signature().name().to_string(), function))
        .collect::<BTreeMap<_, _>>();
    let current_names = current_blocks.keys().cloned().collect::<BTreeSet<_>>();

    let shared_environment_changed = current_file.predicate_definitions()
        != baseline_file.predicate_definitions()
        || current_file.click_function_definitions() != baseline_file.click_function_definitions()
        || current_file.resource_definitions() != baseline_file.resource_definitions()
        || current_file.theorem_definitions() != baseline_file.theorem_definitions();
    if shared_environment_changed {
        return Ok(C0IncrementalSelection {
            selected_functions: current_names.iter().cloned().collect(),
            reused_functions: Vec::new(),
            reasons: vec![
                "shared predicate, pure function, resource, or theorem definitions changed"
                    .to_string(),
            ],
            full_rebuild: true,
        });
    }

    let all_names = current_blocks
        .keys()
        .chain(baseline_blocks.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    let mut changed = BTreeSet::new();
    let mut reasons = Vec::new();
    for name in all_names {
        let click_changed = current_blocks.get(&name) != baseline_blocks.get(&name);
        let c_changed = current_parsed.get(&name) != baseline_parsed.get(&name);
        if click_changed || c_changed {
            changed.insert(name.clone());
            reasons.push(format!(
                "`{name}` {} changed",
                match (click_changed, c_changed) {
                    (true, true) => "C body/signature and Click contract/proof",
                    (true, false) => "Click contract/proof",
                    (false, true) => "C body/signature or imported layout",
                    (false, false) => unreachable!(),
                }
            ));
        }
    }

    let mut reverse = BTreeMap::<String, BTreeSet<String>>::new();
    for parsed in [&current_parsed, &baseline_parsed] {
        for (caller, (_, function)) in parsed {
            for dependency in c0_statement_calls(function).into_iter().flatten() {
                reverse
                    .entry(dependency)
                    .or_default()
                    .insert(caller.clone());
            }
        }
    }
    let mut affected = changed.clone();
    let mut pending = changed.into_iter().collect::<Vec<_>>();
    while let Some(name) = pending.pop() {
        for caller in reverse.get(&name).into_iter().flatten() {
            if affected.insert(caller.clone()) {
                reasons.push(format!("`{caller}` calls affected function `{name}`"));
                pending.push(caller.clone());
            }
        }
    }
    affected.retain(|name| current_names.contains(name));
    let reused = current_names
        .difference(&affected)
        .cloned()
        .collect::<Vec<_>>();
    Ok(C0IncrementalSelection {
        selected_functions: affected.into_iter().collect(),
        reused_functions: reused,
        reasons,
        full_rebuild: false,
    })
}

/// Verifies a selected function set and its transitive callees in one native
/// verifier transaction.
pub fn verify_c0_sources_functions(
    click_source: &str,
    c_sources: &[(&str, &str)],
    functions: impl IntoIterator<Item = String>,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let functions = functions.into_iter().collect::<BTreeSet<_>>();
    instrumentation::with_default_tactic_limits(|| {
        verify_c0_sources_targeted(
            click_source,
            c_sources,
            Some(VerificationTarget::Functions(functions)),
        )
    })
}

pub(in crate::surface) fn verify_c0_sources_with_limits(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let result = verify_c0_sources_targeted(click_source, c_sources, None);
    if let Err(error) = &result {
        error.emit_timing_failure();
    }
    result
}

impl C0VerificationSession {
    pub fn new(
        click_source: &str,
        c_sources: &[(&str, &str)],
    ) -> Result<(Self, Vec<VerifiedCTheorem>), ClickError> {
        instrumentation::with_default_tactic_limits(|| {
            Self::new_with_limits(click_source, c_sources)
        })
    }

    fn new_with_limits(
        click_source: &str,
        c_sources: &[(&str, &str)],
    ) -> Result<(Self, Vec<VerifiedCTheorem>), ClickError> {
        let (verified, verified_function_environment) =
            verify_c0_sources_with_environment(click_source, c_sources, None, None, None)?;
        let baseline_file = parse_c0_click_file(click_source, c_sources)?;
        Ok((
            Self {
                c_sources: c_sources
                    .iter()
                    .map(|(name, source)| ((*name).to_string(), (*source).to_string()))
                    .collect(),
                baseline_file,
                verified_function_environment,
            },
            verified,
        ))
    }

    /// Reports whether the kernel produced separate termination evidence for
    /// this function. Ordinary partial-contract verification does not consult
    /// this stronger result.
    pub fn function_termination_is_verified(&self, name: &str) -> bool {
        self.verified_function_environment
            .has_verified_function_termination(name)
    }

    pub fn verify_at(
        &self,
        click_source: &str,
        line: usize,
        column: usize,
    ) -> Result<Vec<VerifiedCTheorem>, ClickError> {
        instrumentation::with_default_tactic_limits(|| {
            self.verify_at_with_limits(click_source, line, column)
        })
    }

    fn verify_at_with_limits(
        &self,
        click_source: &str,
        line: usize,
        column: usize,
    ) -> Result<Vec<VerifiedCTheorem>, ClickError> {
        let c_sources = self
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let target = verification_target_at(click_source, &c_sources, line, column)?;
        let target_exists_in_baseline = match &target {
            VerificationTarget::Function(name) => self
                .baseline_file
                .function_blocks()
                .iter()
                .any(|function| function.signature().name() == name),
            VerificationTarget::Theorem(name) => self
                .baseline_file
                .theorem_definitions()
                .iter()
                .any(|theorem| theorem.name() == name),
            VerificationTarget::Functions(_) => false,
        };
        if !target_exists_in_baseline {
            return Err(ClickError::new(
                "rewritten source location resolves to a proof unit absent from the baseline",
            ));
        }
        let rewritten_file = parse_c0_click_file(click_source, &c_sources)?;
        let baseline_interface = proof_unit_erased_click_file(self.baseline_file.clone(), &target);
        let rewritten_interface = proof_unit_erased_click_file(rewritten_file, &target);
        if rewritten_interface != baseline_interface {
            return Err(ClickError::new(
                "rewritten sidecar changed source outside the selected proof unit",
            ));
        }
        let initial_environment = match &target {
            VerificationTarget::Function(function_name) => Some(
                self.verified_function_environment
                    .clone()
                    .without_verified_function_rule(function_name),
            ),
            VerificationTarget::Theorem(_) => None,
            VerificationTarget::Functions(_) => None,
        };
        verify_c0_sources_with_environment(
            click_source,
            &c_sources,
            Some(target),
            initial_environment,
            None,
        )
        .map(|(verified, _)| verified)
    }
}

/// Parses and validates the complete sidecar, then verifies only the proof
/// unit containing the one-based source location and the C functions it calls.
pub fn verify_c0_sources_at(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let target = verification_target_at(click_source, c_sources, line, column)?;
        verify_c0_sources_targeted(click_source, c_sources, Some(target))
    })
}

pub(in crate::surface) fn verify_c0_sources_targeted(
    click_source: &str,
    c_sources: &[(&str, &str)],
    verification_target: Option<VerificationTarget>,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    verify_c0_sources_with_environment(click_source, c_sources, verification_target, None, None)
        .map(|(verified, _)| verified)
}

pub(in crate::surface) fn verify_c0_sources_with_environment(
    click_source: &str,
    c_sources: &[(&str, &str)],
    verification_target: Option<VerificationTarget>,
    initial_function_environment: Option<CExecutionEnvironment>,
    mut expansion_capture: Option<&mut ExpansionCapture>,
) -> Result<(Vec<VerifiedCTheorem>, CExecutionEnvironment), ClickError> {
    check_verification_deadline()?;
    // A verification that continues from an earlier one's environment shares
    // that environment's snapshots and keeps its kernel session; every other
    // verification starts its own, so thread-local kernel state cannot carry
    // over from whatever verified before it on this thread.
    // The guard scopes the kernel's thread-local state to this verification
    // and is held until it finishes.
    let _session = initial_function_environment
        .is_none()
        .then(crate::kernel::VerificationSession::enter);
    let (file, parsed_sources, selected_functions) = {
        let _timing = VerificationTimingPhase::new("frontend");
        let c_sources: BTreeMap<&str, &str> = c_sources.iter().copied().collect();
        let (struct_layouts, union_layouts, aggregate_objects, aggregate_array_objects) =
            parse_c_layouts(click_source, &c_sources)?;
        let file = parser::parse_with_layouts_and_aggregate_objects(
            click_source,
            struct_layouts,
            union_layouts,
            aggregate_objects,
            aggregate_array_objects,
        )?;
        let parsed_sources = parse_verified_sources(&file, &c_sources)?;
        let expansion_functions = expansion_capture
            .as_deref()
            .map(|capture| {
                tactic_expansion_required_functions(
                    &file,
                    &parsed_sources,
                    (capture.site.clone(), capture.source_index),
                )
            })
            .transpose()?;
        let selected_functions = if expansion_functions.is_some() {
            expansion_functions
        } else {
            match verification_target.as_ref() {
                Some(VerificationTarget::Function(function_name)) => {
                    if initial_function_environment.is_some() {
                        Some(BTreeSet::from([function_name.clone()]))
                    } else {
                        Some(verification_required_functions(
                            &file,
                            &parsed_sources,
                            function_name,
                        )?)
                    }
                }
                Some(VerificationTarget::Functions(function_names)) => {
                    let mut required = BTreeSet::new();
                    for function_name in function_names {
                        required.extend(verification_required_functions(
                            &file,
                            &parsed_sources,
                            function_name,
                        )?);
                    }
                    Some(required)
                }
                Some(VerificationTarget::Theorem(_)) => Some(BTreeSet::new()),
                None => None,
            }
        };
        check_verification_deadline()?;
        (file, parsed_sources, selected_functions)
    };
    check_verification_deadline()?;
    let (mut termination_plans, mut requested_termination) =
        c_function_termination_plans(&file, selected_functions.as_ref())?;
    let (
        predicate_environment,
        click_function_environment,
        resource_environment,
        mut function_environment,
        theorem_certification_facts,
        theorem_certification_authorities,
        theorem_environment,
    ) = {
        let _timing = VerificationTimingPhase::new("environment");
        let predicate_definitions = combined_predicate_definitions(&file)?;
        let click_function_definitions = combined_click_function_definitions(&file)?;
        let resource_definitions = combined_resource_definitions(&file)?;
        let theorem_definitions = combined_theorem_definitions(&file)?;
        let standard_library_theorem_count = theorem_definitions
            .len()
            .saturating_sub(file.theorem_definitions().len());
        let theorem_definitions = selected_theorem_definitions(
            &file,
            &theorem_definitions,
            standard_library_theorem_count,
            selected_functions.as_ref(),
            verification_target.as_ref(),
        );
        let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
        let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
            &click_function_definitions,
            file.algebraic_type_definitions(),
        );
        let resource_environment = ResourceEnvironment::new(&resource_definitions);
        // Frame evidence may look through composite definitions to decide
        // that a call's mutable ranges or a store's written cell cannot
        // touch a loaded pointer inside a composite's footprint. Definitions
        // are file-global, so one guard covers this verification; nothing is
        // published, so nested composites still require `observe(...)` before
        // a user's `separate(...)` goal can cite them.
        let external_and_user_function_blocks = combined_external_function_blocks(&file)?;
        let built_function_environment = build_function_environment(
            &parsed_sources,
            &external_and_user_function_blocks,
            &predicate_environment,
            &click_function_environment,
            &resource_environment,
        )?;
        let mut function_environment =
            initial_function_environment.unwrap_or(built_function_environment);
        // Verify the selected call-graph closure as one transaction. These
        // crate-private rules are partial-contract hypotheses, not published
        // results: every selected function below must still pass exact kernel
        // certification before this function can return an environment.
        for function_block in file.function_blocks() {
            if selected_functions
                .as_ref()
                .is_some_and(|selected| !selected.contains(function_block.signature().name()))
            {
                continue;
            }
            let Some(function) = function_environment
                .get_function(function_block.signature().name())
                .cloned()
            else {
                continue;
            };
            if let Some(hypothesis) =
                crate::kernel::c_recursive_function_contract_hypothesis(function)
            {
                function_environment = function_environment.with_verified_function_rule(hypothesis);
            }
        }
        let verified_theorems = verify_theorem_definitions(
            &theorem_definitions,
            &predicate_environment,
            &click_function_environment,
        )?;
        // Verified pure theorems over scalar parameters become closed
        // universally-quantified facts, so kernel contract certification can
        // discharge obligations the surface proof established by `apply`.
        let mut theorem_certification_facts = BTreeMap::<String, Vec<Proposition>>::new();
        let mut theorem_certification_authorities =
            BTreeMap::<String, Vec<CVerifiedPureTheorem>>::new();
        for theorem in verified_theorems.iter().filter(|theorem| {
            theorem.kernel_authority.is_some()
                && theorem
                    .theorem_definition
                    .parameters()
                    .iter()
                    .all(|parameter| parameter.click_type() == &ClickType::C(C0Type::Int32))
        }) {
            let implication = theorem.requires.iter().rev().fold(
                theorem.conclusion.clone(),
                |body, requirement| {
                    Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
                },
            );
            let fact = theorem
                .theorem_definition
                .parameters()
                .iter()
                .enumerate()
                .rev()
                .fold(implication, |body, (index, _)| Proposition::ForAll {
                    var: crate::kernel::Variable(index as u64),
                    sort: crate::kernel::Sort::CInt32,
                    body: Box::new(body),
                });
            theorem_certification_facts
                .entry(theorem.theorem_definition.name().to_string())
                .or_default()
                .push(fact);
            let authority = theorem
                .kernel_authority
                .as_ref()
                .expect("theorem certification facts require kernel authority");
            theorem_certification_authorities
                .entry(theorem.theorem_definition.name().to_string())
                .or_default()
                .push(authority.clone());
        }
        let theorem_environment = TheoremEnvironment::new(&theorem_definitions);
        check_verification_deadline()?;
        (
            predicate_environment,
            click_function_environment,
            resource_environment,
            function_environment,
            theorem_certification_facts,
            theorem_certification_authorities,
            theorem_environment,
        )
    };

    // Frame evidence may look through composite definitions to decide that a
    // call's mutable ranges or a store's written cell cannot touch a loaded
    // pointer inside a composite's footprint. Definitions are file-global, so
    // one guard covers this verification; nothing is published, so a nested
    // composite still needs its `observe(...)` chain before a user's
    // `separate(...)` goal can cite it.
    let _frame_composite_definitions = crate::kernel::arm_frame_composite_definitions(
        composite_resource_definitions(
            &resource_environment,
            &predicate_environment,
            &click_function_environment,
        )
        .unwrap_or_default(),
    );
    check_verification_deadline()?;
    let mut verified = Vec::new();
    let mut termination_loop_rules = BTreeMap::<String, Vec<CVerifiedLoopRule>>::new();

    for function_block in file.function_blocks {
        check_verification_deadline()?;
        if function_block.is_external() {
            continue;
        }
        if selected_functions
            .as_ref()
            .is_some_and(|functions| !functions.contains(function_block.signature.name()))
        {
            continue;
        }
        // This outer span makes otherwise-unclassified proof orchestration
        // visible at an interrupted project deadline. Nested tactic and
        // certification spans take precedence in the active-work snapshot.
        let _verifier_core_timing = VerificationTimingPhase::new("verifier-core");
        let function_timing_start = std::time::Instant::now();
        let (source_path, parsed_function) = parsed_sources
            .get(function_block.signature.name())
            .ok_or_else(|| {
                ClickError::new(format!(
                    "`{}` is not defined by any `verifying` source",
                    function_block.signature.name()
                ))
            })?;
        check_signature(&function_block.signature, parsed_function, source_path)?;
        validate_region_proof_clauses(&function_block, parsed_function)?;
        let verified_loop_rules = verify_loop_execution_proofs(
            expansion_capture.as_deref_mut(),
            &function_block,
            parsed_function,
            &function_environment,
            &predicate_environment,
            &click_function_environment,
            &resource_environment,
            &theorem_environment,
        )?;
        let verification_function_environment = function_environment
            .clone()
            .with_verified_loop_rules(verified_loop_rules);
        let implicit_safety_clause = EnsureClause {
            name: None,
            ensure: Ensure::Proposition(ClickProposition::Comparison {
                left: ContractExpression::CFragment(CExpression::Value(int32(0))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(CExpression::Value(int32(0))),
            }),
            proof: SourceProof::Tactic(SmartTactic::Auto),
        };
        let mut claims = function_claims(&function_block);
        let has_explicit_claims = !claims.is_empty();
        if !has_explicit_claims {
            claims.push(FunctionClaimRef::Ensure(0, &implicit_safety_clause));
        }
        let mut function_verified = Vec::new();
        if let Some(grouped_proof) = function_block.grouped_proof() {
            let theorems = match grouped_proof {
                SourceProof::Tactic(SmartTactic::Auto) => prove_claims_by_grouped_auto(
                    expansion_capture.as_deref_mut(),
                    source_path,
                    &function_block,
                    parsed_function,
                    &claims,
                    &verification_function_environment,
                    &predicate_environment,
                    &click_function_environment,
                    &resource_environment,
                    &theorem_environment,
                )?,
                SourceProof::Script(tactics) => prove_claims_by_grouped_script(
                    expansion_capture.as_deref_mut(),
                    source_path,
                    &function_block,
                    parsed_function,
                    &claims,
                    &verification_function_environment,
                    &predicate_environment,
                    &click_function_environment,
                    &resource_environment,
                    &theorem_environment,
                    tactics,
                )?,
                SourceProof::Default
                | SourceProof::Tactic(SmartTactic::Simp | SmartTactic::Frame) => {
                    return Err(ClickError::new(format!(
                        "grouped proof for `{}` must use `by auto;` or an explicit `by {{ ... }}` proof script",
                        function_block.signature().name()
                    )));
                }
            };
            function_verified.extend(theorems.iter().cloned());
            verified.extend(theorems);
        } else {
            for claim in claims {
                let claim_label = if has_explicit_claims {
                    function_claim_label(function_block.signature.name(), &claim)
                } else {
                    format!("{}.body_safety", function_block.signature.name())
                };
                let theorems = match claim.proof() {
                    SourceProof::Default | SourceProof::Tactic(SmartTactic::Auto) => {
                        prove_claim_by_auto(
                            expansion_capture.as_deref_mut(),
                            source_path,
                            &function_block,
                            parsed_function,
                            &claim,
                            &claim_label,
                            &verification_function_environment,
                            &predicate_environment,
                            &click_function_environment,
                            &resource_environment,
                            &theorem_environment,
                        )?
                    }
                    SourceProof::Tactic(SmartTactic::Frame) => prove_claim_by_frame(
                        expansion_capture.as_deref_mut(),
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &verification_function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                    )?,
                    SourceProof::Tactic(SmartTactic::Simp) => prove_claim_by_simp(
                        expansion_capture.as_deref_mut(),
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &verification_function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                    )?,
                    SourceProof::Script(tactics) => prove_claim_by_script(
                        expansion_capture.as_deref_mut(),
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &verification_function_environment,
                        &predicate_environment,
                        &click_function_environment,
                        &resource_environment,
                        &theorem_environment,
                        tactics,
                    )?,
                };
                function_verified.extend(theorems.iter().cloned());
                if has_explicit_claims {
                    verified.extend(theorems);
                }
            }
        }
        let function_termination_loop_rules = termination_loop_rules
            .entry(function_block.signature().name().to_string())
            .or_default();
        for rule in function_verified
            .iter()
            .flat_map(|theorem| theorem.frontier_loop_rules.iter())
        {
            if !function_termination_loop_rules.contains(rule) {
                function_termination_loop_rules.push(rule.clone());
            }
        }
        // A frontier-local proof constructs loop annotations and checked
        // rules while checking the actual execution path. Final whole-contract
        // certification must use one coherent proof's artifacts; otherwise it
        // forgets the rule and starts concretely unrolling a symbolic loop.
        // Per-claim proofs may legitimately choose different invariants, so do
        // not merge their loop sets. Select that bound block before building
        // the entry context so predicate unfolds in its loop phases are
        // reflected in the exact certification facts as well.
        let frontier_loop_artifacts = function_verified
            .iter()
            .find(|verified| !verified.frontier_loop_rules.is_empty());
        let certification_function_block = frontier_loop_artifacts.map_or_else(
            || function_block.clone(),
            |verified| {
                function_block.with_bound_frontier_loop_clauses(&verified.frontier_loop_clauses)
            },
        );
        let (certification_state, certification_arguments, mut certification_facts, _) =
            initial_claim_context(
                &certification_function_block,
                parsed_function,
                &resource_environment,
                &predicate_environment,
                &click_function_environment,
                &format!("{}.contract certification", function_block.signature.name()),
            )?;
        let mut certification_theorems = BTreeSet::new();
        for verified in &function_verified {
            if let Some(tactics) = &verified.proof_tactics {
                collect_applied_theorems(tactics, &mut certification_theorems);
            }
        }
        let mut certification_pure_theorems = Vec::new();
        for theorem_name in certification_theorems {
            if let Some(facts) = theorem_certification_facts.get(&theorem_name) {
                certification_facts.extend(facts.iter().cloned());
            }
            if let Some(authorities) = theorem_certification_authorities.get(&theorem_name) {
                certification_pure_theorems.extend(authorities.iter().cloned());
            }
        }
        // A sized array parameter form (`int32 p[2]`) declares its span
        // loadable as part of the calling convention; certification may rely
        // on it to discharge requirement side-obligations.
        for (name, bytes) in function_block.signature.declared_loadable_bytes() {
            let position = parsed_function
                .parameters()
                .iter()
                .position(|parameter| parameter.name() == name);
            let Some(CExpression::Value(CValue::Pointer(base))) =
                position.and_then(|index| certification_arguments.get(index))
            else {
                continue;
            };
            certification_facts.push(Proposition::CMemoryLoadable {
                memory: certification_state.memory().clone(),
                base: base.pointer().clone(),
                bytes: Bitvector32Term::Constant(*bytes),
            });
        }
        let has_frontier_loop_rules = frontier_loop_artifacts.is_some();
        let contract_function = annotated_function(
            &certification_function_block,
            parsed_function,
            &certification_state,
            &certification_arguments,
            &predicate_environment,
            &click_function_environment,
            &resource_environment,
            !has_frontier_loop_rules,
        )?;
        if contract_function.opaque_contract_supported() {
            let contract_execution_mode = if function_verified
                .iter()
                .any(|verified| verified.concrete_loop_execution)
            {
                CFunctionContractExecutionMode::ExecuteLoops
            } else {
                CFunctionContractExecutionMode::VerifyLoops
            };
            let certification_started = std::time::Instant::now();
            let contract_execution = {
                let _certification_timing = VerificationTimingPhase::new("certification");
                let certification_function_environment = frontier_loop_artifacts.map_or_else(
                    || verification_function_environment.clone(),
                    |verified| {
                        verification_function_environment
                            .clone()
                            .with_verified_loop_rules(verified.frontier_loop_rules.clone())
                    },
                );
                instrumentation::measure_operation(
                    function_block.signature.name(),
                    "contract certification",
                    "contract symbolic execution",
                    || {
                        let checked_artifacts = function_verified
                            .iter()
                            .map(|verified| verified.checked_execution.clone())
                            .collect::<Vec<_>>();
                        prove_c_function_contract_execution_paths_with_checked_artifacts_and_pure_theorems(
                            certification_state,
                            contract_function.clone(),
                            certification_arguments,
                            certification_facts,
                            certification_function_environment,
                            if has_frontier_loop_rules {
                                CExecutionSemantics::APPLY_VERIFIED_RULES
                            } else {
                                match contract_execution_mode {
                                    CFunctionContractExecutionMode::VerifyLoops => {
                                        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS
                                    }
                                    CFunctionContractExecutionMode::ExecuteLoops => {
                                        CExecutionSemantics::APPLY_VERIFIED_RULES
                                    }
                                }
                            },
                            contract_execution_mode,
                            &checked_artifacts,
                            &certification_pure_theorems,
                        )
                    },
                )
            };
            if instrumentation::enabled() {
                instrumentation::emit(VerificationEvent::ContractExecutionFinished {
                    function: function_block.signature.name().to_string(),
                    elapsed: certification_started.elapsed(),
                });
            }
            let claims_started = std::time::Instant::now();
            if contract_execution.path_count() == 0 {
                return Err(ClickError::new(
                    match contract_execution.reuse_diagnostic() {
                        Some(detail) => format!(
                            "could not certify contract for `{}`: {detail}",
                            function_block.signature.name(),
                        ),
                        None => format!(
                            "could not certify contract for `{}`: certification produced no paths",
                            function_block.signature.name(),
                        ),
                    },
                ));
            }
            if let Some(verified) = frontier_loop_artifacts {
                let mut loop_measures = BTreeMap::new();
                for clause in &verified.frontier_loop_clauses {
                    let Some(measure) = clause.decreases() else {
                        continue;
                    };
                    let CodeRegion::Loop(loop_index) = clause.region() else {
                        continue;
                    };
                    let expressions = termination_measure_expressions(
                        measure,
                        &format!(
                            "frontier-local loop {loop_index} `decreases` in `{}`",
                            function_block.signature.name()
                        ),
                    )?;
                    if let Some(previous) = loop_measures.insert(*loop_index, expressions.clone())
                        && previous != expressions
                    {
                        return Err(ClickError::new(format!(
                            "frontier-local proofs for `{}` disagree on loop {loop_index} `decreases`",
                            function_block.signature.name()
                        )));
                    }
                }
                if !loop_measures.is_empty() {
                    if let Some(plan) = termination_plans
                        .iter_mut()
                        .find(|plan| plan.function_name() == function_block.signature.name())
                    {
                        plan.extend_loop_measures(loop_measures);
                    } else {
                        termination_plans.push(c_function_termination_plan(
                            function_block.signature.name(),
                            None,
                            loop_measures,
                        ));
                    }
                    requested_termination.insert(function_block.signature.name().to_string());
                }
            }
            let checked_propositions = function_verified
                .iter()
                .filter_map(|verified| verified.checked_proposition.clone())
                .collect::<Vec<_>>();
            let certified_claims = {
                let _certification_timing = VerificationTimingPhase::new("certification");
                c_verified_function_contract_claims_with_checked_propositions(
                    &contract_function,
                    &contract_execution,
                    &checked_propositions,
                )
            };
            if instrumentation::enabled() {
                instrumentation::emit(VerificationEvent::ContractClaimsFinished {
                    function: function_block.signature.name().to_string(),
                    elapsed: claims_started.elapsed(),
                });
            }
            let Some(certified_claims) = certified_claims else {
                let detail = match c_unverified_function_contract_claims_with_checked_propositions(
                    &contract_function,
                    &contract_execution,
                    &checked_propositions,
                ) {
                    Ok(keys) if !keys.is_empty() => {
                        let described = keys
                            .iter()
                            .map(|key| {
                                let target = contract_function
                                    .contract_claims()
                                    .iter()
                                    .find(|claim| claim.key() == key)
                                    .map(CFunctionContractClaim::target);
                                match target {
                                    Some(CFunctionContractClaimTarget::EnsureProposition(
                                        index,
                                    )) => contract_function
                                        .contract_ensures()
                                        .get(*index)
                                        .map_or_else(
                                            || format!("{key:?}"),
                                            |ensure| format!("{key:?} = {ensure:?}"),
                                        ),
                                    Some(CFunctionContractClaimTarget::EnsureResource(index)) => {
                                        contract_function
                                            .resource_ensures()
                                            .get(*index)
                                            .map_or_else(
                                                || format!("{key:?}"),
                                                |resource| {
                                                    format!("{key:?} = produces {resource:?}")
                                                },
                                            )
                                    }
                                    _ => format!("{key:?}"),
                                }
                            })
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("; unverified claims: {described}")
                    }
                    Ok(_) => String::new(),
                    Err(reason) => format!("; {reason}"),
                };
                return Err(ClickError::new(format!(
                    "could not certify contract for `{}`: exact symbolic execution did not establish every contract claim{}",
                    function_block.signature.name(),
                    detail,
                )));
            };
            let _ordered_claim_proofs = function_verified
                .iter()
                .map(|verified| {
                    let key = if has_explicit_claims {
                        match &verified.claim {
                            VerifiedClaim::Ensure { index, .. } => {
                                CFunctionContractClaimKey::Ensure(*index)
                            }
                            VerifiedClaim::Effect { index, .. } => {
                                CFunctionContractClaimKey::Effect(*index)
                            }
                        }
                    } else {
                        CFunctionContractClaimKey::BodySafety
                    };
                    certified_claims
                        .iter()
                        .find(|proof| proof.key() == &key)
                        .cloned()
                        .ok_or_else(|| {
                            ClickError::new(format!(
                                "could not certify contract claim {key:?} for `{}`",
                                function_block.signature.name(),
                            ))
                        })
                })
                .collect::<Result<Vec<_>, _>>()?;
            // Package every kernel-certified structural claim. Surface proof
            // scripts mention ensures and explicit effects; a resource-backed
            // mutable frame (for example `consumes p[1..2]`) is covered by
            // the resource transition, while explicit mutable frames require
            // an Effect claim.
            let rule = c_verified_function_rule(contract_function, &certified_claims).ok_or_else(
                || {
                    ClickError::new(format!(
                        "could not package verified contract for `{}`",
                        function_block.signature.name()
                    ))
                },
            )?;
            function_environment = function_environment.with_verified_function_rule(rule);
        }
        if instrumentation::enabled() {
            instrumentation::emit(VerificationEvent::FunctionFinished {
                name: function_block.signature.name().to_string(),
                elapsed: function_timing_start.elapsed(),
            });
        }
        check_verification_deadline()?;
    }

    let partial_rules = function_environment.verified_function_rules();
    let termination_rules = c_verified_function_termination_rules(
        &partial_rules,
        &termination_plans,
        &termination_loop_rules,
    )
    .map_err(|error| ClickError::new(format!("could not certify C termination: {error}")))?;
    for name in &requested_termination {
        if !termination_rules
            .iter()
            .any(|rule| rule.function_name() == name)
        {
            return Err(ClickError::new(format!(
                "could not certify termination for `{name}`: every reachable loop, recursive cycle, and callee must have a checked ranking proof"
            )));
        }
    }
    function_environment =
        function_environment.with_verified_function_termination_rules(termination_rules);

    Ok((verified, function_environment))
}

pub(in crate::surface) fn tactic_expansion_required_functions(
    file: &ClickFile,
    parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>,
    (site, tactic_index): (ProofSite, Option<usize>),
) -> Result<BTreeSet<String>, ClickError> {
    let ProofSite::FunctionClaim {
        function_name,
        claim,
    } = site
    else {
        return Ok(file
            .function_blocks()
            .iter()
            .map(|function| function.signature().name().to_string())
            .collect());
    };
    let _tactic_index = tactic_index.ok_or_else(|| {
        ClickError::new(format!(
            "whole-proof capture is not supported for function claim {claim:?}"
        ))
    })?;
    let function_block = file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let _tactics = match claim {
        CProofClaim::Grouped => function_block
            .grouped_proof()
            .and_then(SourceProof::tactics),
        CProofClaim::Ensure(index) => function_block
            .ensures()
            .get(index)
            .and_then(|clause| clause.proof().tactics()),
        CProofClaim::Effect(index) => function_block
            .effects()
            .get(index)
            .and_then(|clause| clause.proof().tactics()),
    }
    .ok_or_else(|| {
        ClickError::new(format!(
            "selected {claim:?} proof for `{function_name}` is not an explicit tactic script"
        ))
    })?;
    let parsed_function = &parsed_sources
        .get(&function_name)
        .ok_or_else(|| ClickError::new(format!("no C source defines `{function_name}`")))?
        .1;
    let statement_calls = c0_statement_calls(parsed_function);
    let mut required = BTreeSet::from([function_name]);
    // Expansion is defined only for an already-correct complete proof unit.
    // Capturing some post-execution tactics also legitimately continues past
    // their source location before the surface certificate is complete. Load
    // every callee of the selected function so capture and final rewritten
    // verification use the same dependency closure. Unrelated functions are
    // still excluded by this targeted traversal.
    let mut pending = statement_calls
        .iter()
        .flatten()
        .cloned()
        .collect::<Vec<_>>();
    while let Some(dependency) = pending.pop() {
        if !required.insert(dependency.clone()) {
            continue;
        }
        if let Some((_, parsed)) = parsed_sources.get(&dependency) {
            pending.extend(c0_statement_calls(parsed).into_iter().flatten());
        }
    }
    Ok(required)
}

pub(in crate::surface) fn tactic_expansion_dependency_context(
    click_source: &str,
    c_sources: &[(&str, &str)],
    site: &ProofSite,
    tactic_index: usize,
) -> Result<Option<String>, ClickError> {
    let ProofSite::FunctionClaim { function_name, .. } = site else {
        return Ok(None);
    };
    let source_map = c_sources.iter().copied().collect::<BTreeMap<_, _>>();
    let file = parse_c0_click_file(click_source, c_sources)?;
    let parsed_sources = parse_verified_sources(&file, &source_map)?;
    let required = tactic_expansion_required_functions(
        &file,
        &parsed_sources,
        (site.clone(), Some(tactic_index)),
    )?;
    if required.len() <= 1 {
        return Ok(None);
    }

    let mut paths = BTreeMap::from([(function_name.clone(), vec![function_name.clone()])]);
    let mut pending = vec![function_name.clone()];
    let mut cursor = 0;
    while let Some(name) = pending.get(cursor).cloned() {
        cursor += 1;
        let Some((_, function)) = parsed_sources.get(&name) else {
            continue;
        };
        let parent_path = paths
            .get(&name)
            .cloned()
            .expect("queued dependency has a recorded path");
        for dependency in c0_statement_calls(function)
            .into_iter()
            .flatten()
            .filter(|dependency| required.contains(dependency))
        {
            if paths.contains_key(&dependency) {
                continue;
            }
            let mut path = parent_path.clone();
            path.push(dependency.clone());
            paths.insert(dependency.clone(), path);
            pending.push(dependency);
        }
    }
    let rendered = paths
        .into_values()
        .filter(|path| path.len() > 1)
        .map(|path| path.join(" -> "))
        .collect::<Vec<_>>();
    Ok((!rendered.is_empty())
        .then(|| format!("required dependency paths: {}", rendered.join(", "))))
}

pub(in crate::surface) fn verification_required_functions(
    file: &ClickFile,
    parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>,
    function_name: &str,
) -> Result<BTreeSet<String>, ClickError> {
    let function_blocks = combined_external_function_blocks(file)?;
    verification_required_functions_with_blocks(parsed_sources, function_name, &function_blocks)
}

fn verification_required_functions_with_blocks(
    parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>,
    function_name: &str,
    function_blocks: &[FunctionBlock],
) -> Result<BTreeSet<String>, ClickError> {
    if !function_blocks
        .iter()
        .any(|function| function.signature().name() == function_name)
    {
        return Err(ClickError::new(format!(
            "source location selected unknown function `{function_name}`"
        )));
    }
    let mut required = BTreeSet::new();
    let mut pending = vec![function_name.to_string()];
    while let Some(name) = pending.pop() {
        if !required.insert(name.clone()) {
            continue;
        }
        let Some(parsed) = parsed_sources.get(&name).map(|entry| &entry.1) else {
            if function_blocks
                .iter()
                .any(|function| function.is_external() && function.signature().name() == name)
            {
                continue;
            }
            return Err(ClickError::new(format!("no C source defines `{name}`")));
        };
        pending.extend(c0_statement_calls(parsed).into_iter().flatten());
    }
    Ok(required)
}

/// Returns the external C assumptions in each user function's transitive C
/// call closure. This is intentionally derived from the same call graph used
/// by targeted verification, so reporting cannot silently omit a transitive
/// external callee.
pub fn c0_external_dependencies(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<BTreeMap<String, Vec<String>>, ClickError> {
    let sources = c_sources.iter().copied().collect::<BTreeMap<_, _>>();
    let (struct_layouts, union_layouts, aggregate_objects, aggregate_array_objects) =
        parse_c_layouts(click_source, &sources)?;
    let file = parser::parse_with_layouts_and_aggregate_objects(
        click_source,
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
    )?;
    let parsed_sources = parse_verified_sources(&file, &sources)?;
    let function_blocks = combined_external_function_blocks(&file)?;
    let external_names = function_blocks
        .iter()
        .filter(|function| function.is_external())
        .map(|function| function.signature().name().to_string())
        .collect::<BTreeSet<_>>();
    let mut dependencies = BTreeMap::new();
    for function in file
        .function_blocks()
        .iter()
        .filter(|function| !function.is_external())
    {
        let required = verification_required_functions_with_blocks(
            &parsed_sources,
            function.signature().name(),
            &function_blocks,
        )?;
        let external = required
            .intersection(&external_names)
            .cloned()
            .collect::<Vec<_>>();
        if !external.is_empty() {
            dependencies.insert(function.signature().name().to_string(), external);
        }
    }
    Ok(dependencies)
}

pub(in crate::surface) fn c0_statement_calls(
    function: &syntax::C0Function,
) -> Vec<BTreeSet<String>> {
    fn collect_function_pointer_names(
        statement: &syntax::C0Statement,
        names: &mut BTreeSet<String>,
    ) {
        match statement {
            syntax::C0Statement::Declare { c_type, name, .. }
                if matches!(c_type, syntax::C0Type::FunctionPointer(_)) =>
            {
                names.insert(name.clone());
            }
            syntax::C0Statement::Seq(first, second) => {
                collect_function_pointer_names(first, names);
                collect_function_pointer_names(second, names);
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_function_pointer_names(then_branch, names);
                collect_function_pointer_names(else_branch, names);
            }
            syntax::C0Statement::While { body, .. } | syntax::C0Statement::DoWhile { body, .. } => {
                collect_function_pointer_names(body, names);
            }
            syntax::C0Statement::For {
                initializer,
                step,
                body,
                ..
            } => {
                collect_function_pointer_names(initializer, names);
                collect_function_pointer_names(body, names);
                collect_function_pointer_names(step, names);
            }
            syntax::C0Statement::Switch { cases, .. } => {
                for case in cases {
                    collect_function_pointer_names(case.body(), names);
                }
            }
            syntax::C0Statement::Skip
            | syntax::C0Statement::Break
            | syntax::C0Statement::Continue
            | syntax::C0Statement::Declare { .. }
            | syntax::C0Statement::DeclareStructValue { .. }
            | syntax::C0Statement::Assign { .. }
            | syntax::C0Statement::CallAssign { .. }
            | syntax::C0Statement::Call { .. }
            | syntax::C0Statement::IndirectCall { .. }
            | syntax::C0Statement::HeapAllocate { .. }
            | syntax::C0Statement::HeapFree { .. }
            | syntax::C0Statement::Return(_)
            | syntax::C0Statement::Store { .. }
            | syntax::C0Statement::AggregateCopy { .. }
            | syntax::C0Statement::Update { .. } => {}
        }
    }

    fn collect_function_addresses(expression: &syntax::C0Expression, names: &mut BTreeSet<String>) {
        match expression {
            syntax::C0Expression::Call { arguments, .. } => {
                for argument in arguments {
                    collect_function_addresses(argument, names);
                }
            }
            syntax::C0Expression::IndirectCall {
                function,
                arguments,
                ..
            } => {
                collect_function_addresses(function, names);
                for argument in arguments {
                    collect_function_addresses(argument, names);
                }
            }
            syntax::C0Expression::FunctionAddress(name) => {
                names.insert(name.clone());
            }
            syntax::C0Expression::Cast { expression, .. }
            | syntax::C0Expression::FloatNegate(expression)
            | syntax::C0Expression::FloatClassification { expression, .. }
            | syntax::C0Expression::AddressOf(expression)
            | syntax::C0Expression::AggregateAddress {
                pointer: expression,
                ..
            }
            | syntax::C0Expression::UnionAddress {
                pointer: expression,
                ..
            }
            | syntax::C0Expression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | syntax::C0Expression::Not(expression)
            | syntax::C0Expression::BitwiseNot(expression)
            | syntax::C0Expression::Load(expression) => {
                collect_function_addresses(expression, names);
            }
            syntax::C0Expression::Conditional {
                condition,
                then_branch,
                else_branch,
            } => {
                collect_function_addresses(condition, names);
                collect_function_addresses(then_branch, names);
                collect_function_addresses(else_branch, names);
            }
            syntax::C0Expression::LessThan(left, right)
            | syntax::C0Expression::LessEqual(left, right)
            | syntax::C0Expression::GreaterThan(left, right)
            | syntax::C0Expression::GreaterEqual(left, right)
            | syntax::C0Expression::Equal(left, right)
            | syntax::C0Expression::NotEqual(left, right)
            | syntax::C0Expression::And(left, right)
            | syntax::C0Expression::Or(left, right)
            | syntax::C0Expression::Add(left, right)
            | syntax::C0Expression::Subtract(left, right)
            | syntax::C0Expression::Multiply(left, right)
            | syntax::C0Expression::Divide(left, right)
            | syntax::C0Expression::Remainder(left, right)
            | syntax::C0Expression::ShiftLeft(left, right)
            | syntax::C0Expression::ShiftRight(left, right)
            | syntax::C0Expression::BitwiseAnd(left, right)
            | syntax::C0Expression::BitwiseOr(left, right)
            | syntax::C0Expression::BitwiseXor(left, right)
            | syntax::C0Expression::Index(left, right) => {
                collect_function_addresses(left, names);
                collect_function_addresses(right, names);
            }
            syntax::C0Expression::Field { pointer, .. } => {
                collect_function_addresses(pointer, names);
            }
            syntax::C0Expression::UnionField { pointer, .. } => {
                collect_function_addresses(pointer, names);
            }
            syntax::C0Expression::Void
            | syntax::C0Expression::Variable(_)
            | syntax::C0Expression::Int32Literal(_)
            | syntax::C0Expression::UInt8Literal(_)
            | syntax::C0Expression::UInt32Literal(_)
            | syntax::C0Expression::Int64Literal(_)
            | syntax::C0Expression::UInt64Literal(_)
            | syntax::C0Expression::Float32Literal(_)
            | syntax::C0Expression::Float64Literal(_)
            | syntax::C0Expression::SizeOfStruct { .. }
            | syntax::C0Expression::SizeOfUnion { .. }
            | syntax::C0Expression::SizeOfType { .. } => {}
        }
    }

    let mut function_pointer_names = function
        .parameters()
        .iter()
        .filter(|parameter| matches!(parameter.c_type(), syntax::C0Type::FunctionPointer(_)))
        .map(|parameter| parameter.name().to_string())
        .collect::<BTreeSet<_>>();
    collect_function_pointer_names(function.body(), &mut function_pointer_names);

    fn visit(
        statement: &syntax::C0Statement,
        calls: &mut Vec<BTreeSet<String>>,
        function_pointer_names: &BTreeSet<String>,
    ) {
        match statement {
            syntax::C0Statement::Skip
            | syntax::C0Statement::Break
            | syntax::C0Statement::Continue => {}
            syntax::C0Statement::Seq(first, second) => {
                visit(first, calls, function_pointer_names);
                visit(second, calls, function_pointer_names);
            }
            syntax::C0Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(condition, &mut dependencies);
                calls.push(dependencies);
                visit(then_branch, calls, function_pointer_names);
                visit(else_branch, calls, function_pointer_names);
            }
            syntax::C0Statement::While { condition, body }
            | syntax::C0Statement::DoWhile { condition, body } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(condition, &mut dependencies);
                calls.push(dependencies);
                visit(body, calls, function_pointer_names);
            }
            syntax::C0Statement::For {
                initializer,
                condition,
                step,
                body,
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(condition, &mut dependencies);
                calls.push(dependencies);
                visit(initializer, calls, function_pointer_names);
                visit(body, calls, function_pointer_names);
                visit(step, calls, function_pointer_names);
            }
            syntax::C0Statement::Switch { expression, cases } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(expression, &mut dependencies);
                calls.push(dependencies);
                for case in cases {
                    visit(case.body(), calls, function_pointer_names);
                }
            }
            syntax::C0Statement::CallAssign {
                function_name,
                arguments,
                ..
            } => {
                let mut dependencies = BTreeSet::new();
                if !function_pointer_names.contains(function_name) {
                    dependencies.insert(function_name.clone());
                }
                for argument in arguments {
                    collect_function_addresses(argument, &mut dependencies);
                }
                calls.push(dependencies);
            }
            syntax::C0Statement::Call {
                function_name,
                arguments,
            } => {
                let mut dependencies = BTreeSet::new();
                if !function_pointer_names.contains(function_name) {
                    dependencies.insert(function_name.clone());
                }
                for argument in arguments {
                    collect_function_addresses(argument, &mut dependencies);
                }
                calls.push(dependencies);
            }
            syntax::C0Statement::IndirectCall {
                function,
                arguments,
                ..
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(function, &mut dependencies);
                for argument in arguments {
                    collect_function_addresses(argument, &mut dependencies);
                }
                calls.push(dependencies);
            }
            syntax::C0Statement::Declare { .. }
            | syntax::C0Statement::DeclareStructValue { .. } => calls.push(BTreeSet::new()),
            syntax::C0Statement::Assign { expression, .. }
            | syntax::C0Statement::HeapAllocate {
                bytes: expression, ..
            }
            | syntax::C0Statement::HeapFree {
                pointer: expression,
            }
            | syntax::C0Statement::Return(expression) => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(expression, &mut dependencies);
                calls.push(dependencies);
            }
            syntax::C0Statement::Store { pointer, value, .. } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(pointer, &mut dependencies);
                collect_function_addresses(value, &mut dependencies);
                calls.push(dependencies);
            }
            syntax::C0Statement::AggregateCopy { target, source, .. } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(target, &mut dependencies);
                collect_function_addresses(source, &mut dependencies);
                calls.push(dependencies);
            }
            syntax::C0Statement::Update {
                target, operand, ..
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(target, &mut dependencies);
                collect_function_addresses(operand, &mut dependencies);
                calls.push(dependencies);
            }
        }
    }

    let mut calls = Vec::new();
    visit(function.body(), &mut calls, &function_pointer_names);
    calls
}

pub(in crate::surface) fn termination_measure_name(
    expression: &ContractExpression,
    context: &str,
) -> Result<String, ClickError> {
    match expression {
        ContractExpression::CFragment(CExpression::Variable(name))
        | ContractExpression::CBinding(name) => Ok(name.clone()),
        _ => Err(ClickError::new(format!(
            "{context} must name one int32 C variable; compound ranking expressions are not yet supported"
        ))),
    }
}

pub(in crate::surface) fn termination_measure_expression(
    expression: &ContractExpression,
    context: &str,
) -> Result<CExpression, ClickError> {
    resource_argument_to_c_expression(expression).map_err(|error| {
        ClickError::new(format!(
            "{context} must be a current int32 C expression: {}",
            error.message()
        ))
    })
}

pub(in crate::surface) fn termination_measure_expressions(
    measure: &TerminationMeasure,
    context: &str,
) -> Result<Vec<CExpression>, ClickError> {
    measure
        .components()
        .iter()
        .map(|expression| termination_measure_expression(expression, context))
        .collect()
}

pub(in crate::surface) fn c_function_termination_plans(
    file: &ClickFile,
    selected_functions: Option<&BTreeSet<String>>,
) -> Result<
    (
        Vec<crate::kernel::CFunctionTerminationPlan>,
        BTreeSet<String>,
    ),
    ClickError,
> {
    let mut plans = Vec::new();
    let mut requested = BTreeSet::new();
    for function in file.function_blocks() {
        if function.is_external() {
            continue;
        }
        let selected = selected_functions
            .is_none_or(|selected| selected.contains(function.signature().name()));
        let recursive_measure = function
            .decreases()
            .map(|measure| match measure {
                CFunctionDecrease::Numeric(measure) => {
                    let name = termination_measure_name(
                        measure,
                        &format!(
                            "function-level `decreases` in `{}`",
                            function.signature().name()
                        ),
                    )?;
                    let index = function
                        .signature()
                        .parameters()
                        .iter()
                        .position(|parameter| parameter.name() == name)
                        .ok_or_else(|| {
                            ClickError::new(format!(
                                "function-level `decreases` in `{}` must name an int32 parameter, not `{name}`",
                                function.signature().name()
                            ))
                        })?;
                    if function.signature().parameters()[index].c_type() != C0Type::Int32 {
                        return Err(ClickError::new(format!(
                            "function-level `decreases` parameter `{name}` in `{}` must have type int32",
                            function.signature().name()
                        )));
                    }
                    Ok(crate::kernel::CFunctionTerminationMeasure::NumericParameter(index))
                }
                CFunctionDecrease::Resource(measure) => {
                    let ResourceClause::Declared {
                        kind: ResourceKind::Composite,
                        name: measure_name,
                        arguments: measure_arguments,
                        ..
                    } = measure
                    else {
                        return Err(ClickError::new(format!(
                            "function-level `decreases resource` in `{}` must name one composite resource",
                            function.signature().name()
                        )));
                    };
                    let mut resource_index = 0;
                    let mut matched = None;
                    for requirement in function.requires() {
                        let Requirement::Resource(required) = requirement.inner() else {
                            continue;
                        };
                        if matches!(
                            required,
                            ResourceClause::Declared {
                                kind: ResourceKind::Composite,
                                name,
                                arguments,
                                ..
                            } if name == measure_name && arguments == measure_arguments
                        ) {
                            matched = Some(resource_index);
                            break;
                        }
                        resource_index += 1;
                    }
                    let index = matched.ok_or_else(|| {
                        ClickError::new(format!(
                            "function-level `decreases resource {measure_name}(...)` in `{}` must exactly match an owned or viewed entry resource",
                            function.signature().name()
                        ))
                    })?;
                    Ok(crate::kernel::CFunctionTerminationMeasure::ResourceRequirement(index))
                }
            })
            .transpose()?;
        let mut loop_measures = BTreeMap::new();
        for clause in function.structural_clauses() {
            let Some(measure) = clause.decreases() else {
                continue;
            };
            let CodeRegion::Loop(index) = clause.region() else {
                return Err(ClickError::new(format!(
                    "`decreases` is supported only for loop regions, not {:?} in `{}`",
                    clause.region(),
                    function.signature().name()
                )));
            };
            let expressions = termination_measure_expressions(
                measure,
                &format!(
                    "loop {index} `decreases` in `{}`",
                    function.signature().name()
                ),
            )?;
            if loop_measures.insert(*index, expressions).is_some() {
                return Err(ClickError::new(format!(
                    "duplicate `decreases` measure for loop {index} in `{}`",
                    function.signature().name()
                )));
            }
        }
        // Grouped proofs are the source of frontier-local loop clauses. A
        // nested `loop` tactic lives inside its enclosing loop's preservation
        // proof, so it is not present in `structural_clauses()`; collect those
        // clauses in source/proof order and let the kernel bind that order to
        // the exact C loop indices it re-traverses.
        if function.structural_clauses().is_empty()
            && let Some(proof) = function.grouped_proof()
        {
            let mut grouped_clauses = Vec::new();
            proof.collect_termination_loop_clauses(&mut grouped_clauses);
            for (index, clause) in grouped_clauses.into_iter().enumerate() {
                if let Some(measure) = clause.decreases() {
                    let expressions = termination_measure_expressions(
                        measure,
                        &format!(
                            "loop {index} `decreases` in `{}`",
                            function.signature().name()
                        ),
                    )?;
                    if loop_measures.insert(index, expressions).is_some() {
                        return Err(ClickError::new(format!(
                            "duplicate `decreases` measure for loop {index} in `{}`",
                            function.signature().name()
                        )));
                    }
                }
            }
        }
        if recursive_measure.is_some() || !loop_measures.is_empty() {
            if selected {
                requested.insert(function.signature().name().to_string());
            }
            plans.push(c_function_termination_plan(
                function.signature().name(),
                recursive_measure,
                loop_measures,
            ));
        }
    }
    Ok((plans, requested))
}

fn parse_c_source_functions(
    source_path: &str,
    c_sources: &BTreeMap<&str, &str>,
) -> Result<Vec<syntax::C0Function>, ClickError> {
    let expanded =
        crate::languages::c::source::expand_includes(source_path, c_sources).map_err(|error| {
            ClickError::new(format!(
                "failed to resolve includes for C source `{source_path}`: {error}"
            ))
        })?;
    for header_path in expanded.dependencies() {
        let header = crate::languages::c::source::expand_includes(header_path, c_sources).map_err(
            |error| {
                ClickError::new(format!(
                    "failed to resolve includes for C header `{header_path}`: {error}"
                ))
            },
        )?;
        syntax::validate_header(header.source()).map_err(|error| {
            ClickError::new(format!("failed to parse C header `{header_path}`: {error}"))
        })?;
    }
    syntax::parse_functions_for_source(expanded.source(), source_path).map_err(|error| {
        ClickError::new(format!("failed to parse C source `{source_path}`: {error}"))
    })
}

pub(in crate::surface) fn parse_c_layouts(
    click_source: &str,
    c_sources: &BTreeMap<&str, &str>,
) -> Result<
    (
        BTreeMap<String, syntax::C0StructLayout>,
        BTreeMap<String, syntax::C0UnionLayout>,
        BTreeMap<String, BTreeMap<String, String>>,
        BTreeMap<String, BTreeSet<String>>,
    ),
    ClickError,
> {
    let mut layouts = BTreeMap::new();
    let mut union_layouts = BTreeMap::new();
    let mut aggregate_objects = BTreeMap::new();
    let mut aggregate_array_objects = BTreeMap::new();
    for source_path in super::verifying_source_paths(click_source)? {
        let functions = parse_c_source_functions(&source_path, c_sources)?;
        for function in functions {
            for (name, layout) in function.structs() {
                if let Some(previous) = layouts.insert(name.clone(), layout.clone())
                    && previous != *layout
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for struct `{name}`"
                    )));
                }
            }
            for (name, layout) in function.unions() {
                if let Some(previous) = union_layouts.insert(name.clone(), layout.clone())
                    && previous != *layout
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for union `{name}`"
                    )));
                }
            }
            let mut function_aggregate_objects = BTreeMap::new();
            for aggregate in function.global_aggregates().values() {
                function_aggregate_objects.insert(
                    aggregate.name().to_string(),
                    aggregate.struct_name().to_string(),
                );
            }
            for aggregate in function.static_aggregates().values() {
                function_aggregate_objects.insert(
                    aggregate.name().to_string(),
                    aggregate.struct_name().to_string(),
                );
            }
            let mut function_aggregate_array_objects = BTreeSet::new();
            for aggregate in function.global_aggregate_arrays().values() {
                function_aggregate_objects.insert(
                    aggregate.name().to_string(),
                    aggregate.struct_name().to_string(),
                );
                function_aggregate_array_objects.insert(aggregate.name().to_string());
            }
            for aggregate in function.static_aggregate_arrays().values() {
                function_aggregate_objects.insert(
                    aggregate.name().to_string(),
                    aggregate.struct_name().to_string(),
                );
                function_aggregate_array_objects.insert(aggregate.name().to_string());
            }
            aggregate_objects.insert(function.name().to_string(), function_aggregate_objects);
            aggregate_array_objects.insert(
                function.name().to_string(),
                function_aggregate_array_objects,
            );
        }
    }
    Ok((
        layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
    ))
}

pub(in crate::surface) fn parse_verified_sources(
    file: &ClickFile,
    c_sources: &BTreeMap<&str, &str>,
) -> Result<BTreeMap<String, (String, syntax::C0Function)>, ClickError> {
    if file.verifying_sources.is_empty() {
        if file
            .function_blocks()
            .iter()
            .all(FunctionBlock::is_external)
        {
            return Ok(BTreeMap::new());
        }
        return Err(ClickError::new(
            "`.click` file must declare at least one `verifying \"source.c\";`",
        ));
    }

    let mut parsed = BTreeMap::new();
    for source_path in &file.verifying_sources {
        let functions = parse_c_source_functions(source_path, c_sources)?;
        for function in functions {
            let function_name = function.name().to_string();
            let previous = parsed.insert(function_name.clone(), (source_path.clone(), function));
            if previous.is_some() {
                return Err(ClickError::new(format!(
                    "more than one `verifying` source defines function `{function_name}`"
                )));
            }
        }
    }

    // Each translation unit sees only the declarations available through its
    // own includes. Link the collected declarations here so every kernel
    // function receives the same externally linked global layout, while
    // counting a definition once per source file rather than once per
    // function. File-scope `static` declarations stay in their own
    // translation unit and are linked below only into that unit's functions.
    let mut globals_by_source = BTreeMap::<String, BTreeMap<String, syntax::C0Global>>::new();
    for (source_path, function) in parsed.values() {
        let source_globals = globals_by_source.entry(source_path.clone()).or_default();
        for (name, global) in function.globals() {
            match source_globals.get(name) {
                Some(previous) if previous.c_type() != global.c_type() => {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for global `{name}`"
                    )));
                }
                Some(previous)
                    if previous.pointee_is_constant() != global.pointee_is_constant() =>
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for global `{name}`"
                    )));
                }
                Some(previous) if previous.is_defined() && global.is_defined() => {
                    if previous != global {
                        return Err(ClickError::new(format!(
                            "conflicting definitions for global `{name}` in `{source_path}`"
                        )));
                    }
                }
                _ => {
                    let merged = match source_globals.get(name) {
                        Some(previous) if previous.is_defined() => previous.clone(),
                        Some(_) if global.is_defined() => global.clone(),
                        Some(previous) => previous.clone(),
                        None => global.clone(),
                    };
                    source_globals.insert(name.clone(), merged);
                }
            }
        }
    }
    let mut globals = BTreeMap::<String, syntax::C0Global>::new();
    for source_globals in globals_by_source.values() {
        for (name, global) in source_globals {
            if global.is_file_static() {
                continue;
            }
            match globals.get(name) {
                Some(previous) if previous.c_type() != global.c_type() => {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for global `{name}`"
                    )));
                }
                Some(previous)
                    if previous.pointee_is_constant() != global.pointee_is_constant() =>
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for global `{name}`"
                    )));
                }
                Some(previous) if previous.is_defined() && global.is_defined() => {
                    return Err(ClickError::new(format!(
                        "multiple definitions of global `{name}`"
                    )));
                }
                _ => {
                    let merged = match globals.get(name) {
                        Some(previous) if previous.is_defined() => previous.clone(),
                        Some(_) if global.is_defined() => global.clone(),
                        Some(previous) => previous.clone(),
                        None => global.clone(),
                    };
                    globals.insert(name.clone(), merged);
                }
            }
        }
    }
    if let Some((name, _)) = globals.iter().find(|(_, global)| !global.is_defined()) {
        return Err(ClickError::new(format!(
            "global `{name}` is declared `extern` but has no definition"
        )));
    }
    let mut global_arrays_by_source =
        BTreeMap::<String, BTreeMap<String, syntax::C0GlobalArray>>::new();
    for (source_path, function) in parsed.values() {
        let source_arrays = global_arrays_by_source
            .entry(source_path.clone())
            .or_default();
        for (name, array) in function.global_arrays() {
            if globals_by_source
                .get(source_path)
                .is_some_and(|source_globals| source_globals.contains_key(name))
            {
                return Err(ClickError::new(format!(
                    "global `{name}` conflicts with a scalar global declaration"
                )));
            }
            match source_arrays.get(name) {
                Some(previous) if previous.c_type() != array.c_type() => {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for global array `{name}`"
                    )));
                }
                Some(previous) if previous.is_defined() && array.is_defined() => {
                    if previous != array {
                        return Err(ClickError::new(format!(
                            "conflicting definitions for global array `{name}` in `{source_path}`"
                        )));
                    }
                }
                _ => {
                    let merged = match source_arrays.get(name) {
                        Some(previous) if previous.is_defined() => previous.clone(),
                        Some(_) if array.is_defined() => array.clone(),
                        Some(previous) => previous.clone(),
                        None => array.clone(),
                    };
                    source_arrays.insert(name.clone(), merged);
                }
            }
        }
    }
    let mut global_arrays = BTreeMap::<String, syntax::C0GlobalArray>::new();
    for source_arrays in global_arrays_by_source.values() {
        for (name, array) in source_arrays {
            if array.is_file_static() {
                continue;
            }
            if globals.contains_key(name) {
                return Err(ClickError::new(format!(
                    "global `{name}` conflicts with a scalar global declaration"
                )));
            }
            match global_arrays.get(name) {
                Some(previous) if previous.c_type() != array.c_type() => {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for global array `{name}`"
                    )));
                }
                Some(previous) if previous.is_defined() && array.is_defined() => {
                    return Err(ClickError::new(format!(
                        "multiple definitions of global array `{name}`"
                    )));
                }
                _ => {
                    let merged = match global_arrays.get(name) {
                        Some(previous) if previous.is_defined() => previous.clone(),
                        Some(_) if array.is_defined() => array.clone(),
                        Some(previous) => previous.clone(),
                        None => array.clone(),
                    };
                    global_arrays.insert(name.clone(), merged);
                }
            }
        }
    }
    if let Some((name, _)) = global_arrays.iter().find(|(_, array)| !array.is_defined()) {
        return Err(ClickError::new(format!(
            "global array `{name}` is declared `extern` but has no definition"
        )));
    }
    let mut global_aggregates_by_source =
        BTreeMap::<String, BTreeMap<String, syntax::C0GlobalAggregate>>::new();
    for (source_path, function) in parsed.values() {
        let source_aggregates = global_aggregates_by_source
            .entry(source_path.clone())
            .or_default();
        for (name, aggregate) in function.global_aggregates() {
            if globals_by_source
                .get(source_path)
                .is_some_and(|source_globals| source_globals.contains_key(name))
                || global_arrays_by_source
                    .get(source_path)
                    .is_some_and(|source_arrays| source_arrays.contains_key(name))
            {
                return Err(ClickError::new(format!(
                    "global `{name}` conflicts with a scalar or array declaration"
                )));
            }
            match source_aggregates.get(name) {
                Some(previous)
                    if previous.struct_name() != aggregate.struct_name()
                        || previous.layout() != aggregate.layout() =>
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for aggregate global `{name}`"
                    )));
                }
                Some(previous) if previous.is_constant() != aggregate.is_constant() => {
                    return Err(ClickError::new(format!(
                        "conflicting const qualifiers for aggregate global `{name}`"
                    )));
                }
                Some(previous) if previous.is_file_static() != aggregate.is_file_static() => {
                    return Err(ClickError::new(format!(
                        "conflicting linkage declarations for aggregate global `{name}`"
                    )));
                }
                Some(previous) if previous.is_defined() && aggregate.is_defined() => {
                    if previous != aggregate {
                        return Err(ClickError::new(format!(
                            "conflicting definitions for aggregate global `{name}` in `{source_path}`"
                        )));
                    }
                }
                _ => {
                    let merged = match source_aggregates.get(name) {
                        Some(previous) if previous.is_defined() => previous.clone(),
                        Some(_) if aggregate.is_defined() => aggregate.clone(),
                        Some(previous) => previous.clone(),
                        None => aggregate.clone(),
                    };
                    source_aggregates.insert(name.clone(), merged);
                }
            }
        }
    }
    let mut global_aggregates = BTreeMap::<String, syntax::C0GlobalAggregate>::new();
    for source_aggregates in global_aggregates_by_source.values() {
        for (name, aggregate) in source_aggregates {
            if aggregate.is_file_static() {
                continue;
            }
            if globals.contains_key(name) || global_arrays.contains_key(name) {
                return Err(ClickError::new(format!(
                    "global `{name}` conflicts with a scalar or array declaration"
                )));
            }
            match global_aggregates.get(name) {
                Some(previous)
                    if previous.struct_name() != aggregate.struct_name()
                        || previous.layout() != aggregate.layout() =>
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for aggregate global `{name}`"
                    )));
                }
                Some(previous) if previous.is_constant() != aggregate.is_constant() => {
                    return Err(ClickError::new(format!(
                        "conflicting const qualifiers for aggregate global `{name}`"
                    )));
                }
                Some(previous) if previous.is_defined() && aggregate.is_defined() => {
                    return Err(ClickError::new(format!(
                        "multiple definitions of aggregate global `{name}`"
                    )));
                }
                _ => {
                    let merged = match global_aggregates.get(name) {
                        Some(previous) if previous.is_defined() => previous.clone(),
                        Some(_) if aggregate.is_defined() => aggregate.clone(),
                        Some(previous) => previous.clone(),
                        None => aggregate.clone(),
                    };
                    global_aggregates.insert(name.clone(), merged);
                }
            }
        }
    }
    if let Some((name, _)) = global_aggregates
        .iter()
        .find(|(_, aggregate)| !aggregate.is_defined())
    {
        return Err(ClickError::new(format!(
            "aggregate global `{name}` is declared `extern` but has no definition"
        )));
    }
    let mut global_aggregate_arrays_by_source =
        BTreeMap::<String, BTreeMap<String, syntax::C0GlobalAggregateArray>>::new();
    for (source_path, function) in parsed.values() {
        let source_aggregate_arrays = global_aggregate_arrays_by_source
            .entry(source_path.clone())
            .or_default();
        for (name, aggregate) in function.global_aggregate_arrays() {
            if globals_by_source
                .get(source_path)
                .is_some_and(|source_globals| source_globals.contains_key(name))
                || global_arrays_by_source
                    .get(source_path)
                    .is_some_and(|source_arrays| source_arrays.contains_key(name))
                || global_aggregates_by_source
                    .get(source_path)
                    .is_some_and(|source_aggregates| source_aggregates.contains_key(name))
            {
                return Err(ClickError::new(format!(
                    "global `{name}` conflicts with a scalar, array, or aggregate declaration"
                )));
            }
            match source_aggregate_arrays.get(name) {
                Some(previous)
                    if previous.struct_name() != aggregate.struct_name()
                        || previous.layout() != aggregate.layout()
                        || previous.length() != aggregate.length() =>
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for aggregate global array `{name}`"
                    )));
                }
                Some(previous) if previous.is_constant() != aggregate.is_constant() => {
                    return Err(ClickError::new(format!(
                        "conflicting const qualifiers for aggregate global array `{name}`"
                    )));
                }
                Some(previous) if previous.is_file_static() != aggregate.is_file_static() => {
                    return Err(ClickError::new(format!(
                        "conflicting linkage declarations for aggregate global array `{name}`"
                    )));
                }
                Some(previous) if previous.is_defined() && aggregate.is_defined() => {
                    if previous != aggregate {
                        return Err(ClickError::new(format!(
                            "conflicting definitions for aggregate global array `{name}` in `{source_path}`"
                        )));
                    }
                }
                _ => {
                    let merged = match source_aggregate_arrays.get(name) {
                        Some(previous) if previous.is_defined() => previous.clone(),
                        Some(_) if aggregate.is_defined() => aggregate.clone(),
                        Some(previous) => previous.clone(),
                        None => aggregate.clone(),
                    };
                    source_aggregate_arrays.insert(name.clone(), merged);
                }
            }
        }
    }
    let mut global_aggregate_arrays = BTreeMap::<String, syntax::C0GlobalAggregateArray>::new();
    for source_aggregate_arrays in global_aggregate_arrays_by_source.values() {
        for (name, aggregate) in source_aggregate_arrays {
            if aggregate.is_file_static() {
                continue;
            }
            if globals.contains_key(name)
                || global_arrays.contains_key(name)
                || global_aggregates.contains_key(name)
            {
                return Err(ClickError::new(format!(
                    "global `{name}` conflicts with a scalar, array, or aggregate declaration"
                )));
            }
            match global_aggregate_arrays.get(name) {
                Some(previous)
                    if previous.struct_name() != aggregate.struct_name()
                        || previous.layout() != aggregate.layout()
                        || previous.length() != aggregate.length() =>
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for aggregate global array `{name}`"
                    )));
                }
                Some(previous) if previous.is_constant() != aggregate.is_constant() => {
                    return Err(ClickError::new(format!(
                        "conflicting const qualifiers for aggregate global array `{name}`"
                    )));
                }
                Some(previous) if previous.is_defined() && aggregate.is_defined() => {
                    return Err(ClickError::new(format!(
                        "multiple definitions of aggregate global array `{name}`"
                    )));
                }
                _ => {
                    let merged = match global_aggregate_arrays.get(name) {
                        Some(previous) if previous.is_defined() => previous.clone(),
                        Some(_) if aggregate.is_defined() => aggregate.clone(),
                        Some(previous) => previous.clone(),
                        None => aggregate.clone(),
                    };
                    global_aggregate_arrays.insert(name.clone(), merged);
                }
            }
        }
    }
    if let Some((name, _)) = global_aggregate_arrays
        .iter()
        .find(|(_, aggregate)| !aggregate.is_defined())
    {
        return Err(ClickError::new(format!(
            "aggregate global array `{name}` is declared `extern` but has no definition"
        )));
    }
    parsed = parsed
        .into_iter()
        .map(|(name, (source_path, function))| {
            let mut visible_globals = globals.clone();
            let mut visible_global_arrays = global_arrays.clone();
            let mut visible_global_aggregates = global_aggregates.clone();
            let mut visible_global_aggregate_arrays = global_aggregate_arrays.clone();
            if let Some(source_globals) = globals_by_source.get(&source_path) {
                for (global_name, global) in source_globals {
                    if global.is_file_static() {
                        visible_globals.insert(global_name.clone(), global.clone());
                    }
                }
            }
            if let Some(source_arrays) = global_arrays_by_source.get(&source_path) {
                for (array_name, array) in source_arrays {
                    if array.is_file_static() {
                        visible_global_arrays.insert(array_name.clone(), array.clone());
                    }
                }
            }
            if let Some(source_aggregates) = global_aggregates_by_source.get(&source_path) {
                for (aggregate_name, aggregate) in source_aggregates {
                    if aggregate.is_file_static() {
                        visible_global_aggregates.insert(aggregate_name.clone(), aggregate.clone());
                    }
                }
            }
            if let Some(source_aggregate_arrays) =
                global_aggregate_arrays_by_source.get(&source_path)
            {
                for (aggregate_name, aggregate) in source_aggregate_arrays {
                    if aggregate.is_file_static() {
                        visible_global_aggregate_arrays
                            .insert(aggregate_name.clone(), aggregate.clone());
                    }
                }
            }
            (
                name,
                (
                    source_path,
                    function
                        .with_globals(visible_globals)
                        .with_global_arrays(visible_global_arrays)
                        .with_global_aggregates(visible_global_aggregates)
                        .with_global_aggregate_arrays(visible_global_aggregate_arrays),
                ),
            )
        })
        .collect();

    for function in file
        .function_blocks()
        .iter()
        .filter(|function| function.is_external())
    {
        if parsed.contains_key(function.signature().name()) {
            return Err(ClickError::new(format!(
                "external function `{}` is also defined by a `verifying` source",
                function.signature().name()
            )));
        }
    }

    Ok(parsed)
}

fn external_c0_function(function_block: &FunctionBlock) -> syntax::C0Function {
    syntax::C0Function::external(
        function_block.signature().return_type(),
        function_block.signature().name().to_string(),
        function_block
            .signature()
            .parameters()
            .iter()
            .map(|parameter| {
                syntax::C0Parameter::new(
                    parameter.c_type(),
                    parameter.name().to_string(),
                    parameter.struct_name().map(str::to_string),
                )
                .with_constant(parameter.is_constant())
                .with_pointee_constant(parameter.pointee_is_constant())
            })
            .collect(),
    )
}

pub(in crate::surface) fn build_function_environment(
    parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>,
    function_blocks: &[FunctionBlock],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
) -> Result<CExecutionEnvironment, ClickError> {
    let mut environment = CExecutionEnvironment::new();
    for (_, function) in parsed_sources.values() {
        let function = match function_blocks
            .iter()
            .find(|block| block.signature().name() == function.name())
        {
            Some(function_block) => {
                let (resource_requires, resource_ensures) =
                    function_resource_summary(function_block, function, resource_environment)?;
                let resource_constructors = function_resource_constructors(function_block)?;
                let (
                    contract_requires,
                    contract_ensures,
                    contract_mutable,
                    contract_claims,
                    opaque_supported,
                    predicate_unfoldings,
                ) = function_contract_summary(
                    function_block,
                    function,
                    predicate_environment,
                    click_function_environment,
                    resource_environment,
                )?;
                let function = function
                    .to_kernel_function()
                    .with_resource_summary(resource_requires, resource_ensures)
                    .with_resource_constructors(resource_constructors)
                    .with_composite_resource_definitions(composite_resource_definitions(
                        resource_environment,
                        predicate_environment,
                        click_function_environment,
                    )?)
                    .with_predicate_unfoldings(predicate_unfoldings)
                    .with_contract(
                        contract_requires,
                        contract_ensures,
                        contract_mutable,
                        contract_claims,
                        opaque_supported,
                    );
                if function_block.effects().is_empty() {
                    function.with_resource_derived_mutable_frame()
                } else {
                    function
                }
            }
            None => function.to_kernel_function(),
        };
        environment = environment.with_function(function);
    }
    for function_block in function_blocks
        .iter()
        .filter(|function| function.is_external())
    {
        let parsed_function = external_c0_function(function_block);
        let (state, arguments, _, _) = initial_claim_context(
            function_block,
            &parsed_function,
            resource_environment,
            predicate_environment,
            click_function_environment,
            &format!("{}.external contract", function_block.signature().name()),
        )?;
        let function = annotated_function(
            function_block,
            &parsed_function,
            &state,
            &arguments,
            predicate_environment,
            click_function_environment,
            resource_environment,
            false,
        )?;
        let rule = crate::kernel::c_external_function_rule(function.clone()).ok_or_else(|| {
            ClickError::new(format!(
                "external function `{}` has a contract that cannot be applied opaquely",
                function_block.signature().name()
            ))
        })?;
        environment = environment
            .with_function(function)
            .with_external_function_rule(rule);
    }
    Ok(environment)
}

pub(in crate::surface) fn function_resource_summary(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
    resource_environment: &ResourceEnvironment,
) -> Result<(Vec<CResourceSpec>, Vec<CResourceSpec>), ClickError> {
    let mut requires = Vec::new();
    for requirement in function_block.requires() {
        let Requirement::Resource(resource) = requirement.inner() else {
            continue;
        };
        append_entry_resource_specs(
            resource,
            parsed_function.parameters(),
            resource_environment,
            &mut requires,
        )?;
    }
    let ensures = function_block
        .ensures()
        .iter()
        .filter_map(|ensure| match ensure.ensure() {
            Ensure::Resource(resource) => Some(resource_clause_to_resource_spec_with_parameters(
                resource,
                parsed_function.parameters(),
                Some(parsed_function.return_type().to_kernel_type()),
            )),
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((requires, ensures))
}

pub(in crate::surface) fn function_resource_constructors(
    function_block: &FunctionBlock,
) -> Result<Vec<CResourceSpec>, ClickError> {
    function_block
        .constructs()
        .iter()
        .map(resource_clause_to_resource_spec)
        .collect()
}

pub(in crate::surface) fn composite_resource_definitions(
    resource_environment: &ResourceEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<CCompositeResourceDefinition>, ClickError> {
    let mut definitions = Vec::new();
    for definition in resource_environment.definitions.values() {
        let Some(body) = definition.composite_body() else {
            continue;
        };
        let contains = body
            .contains()
            .iter()
            .map(resource_clause_to_resource_spec)
            .collect::<Result<Vec<_>, _>>()?;
        let recursive = body.contains().iter().any(|resource| {
            matches!(
                resource,
                ResourceClause::Declared {
                    kind: ResourceKind::Composite,
                    name,
                    ..
                } if name == definition.name()
            )
        });
        let parameters = definition
            .parameters()
            .iter()
            .map(|parameter| {
                crate::kernel::CParameter::new(
                    parameter.name(),
                    parameter.c_type().to_kernel_type(),
                )
            })
            .collect();
        let condition = lower_composite_resource_condition(
            definition,
            predicate_environment,
            click_function_environment,
        )?;
        let facts = lower_composite_resource_facts(
            definition,
            predicate_environment,
            click_function_environment,
        )?;
        let witnesses = body
            .witnesses()
            .iter()
            .map(|witness| {
                crate::kernel::CParameter::new(witness.name(), witness.c_type().to_kernel_type())
            })
            .collect();
        let observes_its_population = body.facts().iter().any(proposition_contains_resource_count);
        definitions.push(
            if observes_its_population {
                CCompositeResourceDefinition::counted_population(
                    definition.name(),
                    parameters,
                    condition,
                    contains,
                    facts,
                )
            } else {
                CCompositeResourceDefinition::new(
                    definition.name(),
                    parameters,
                    condition,
                    recursive,
                    contains,
                    facts,
                )
            }
            .with_witnesses(witnesses),
        );
    }
    Ok(definitions)
}

pub(in crate::surface) fn append_entry_resource_specs(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    _resource_environment: &ResourceEnvironment,
    specs: &mut Vec<CResourceSpec>,
) -> Result<(), ClickError> {
    specs.push(resource_clause_to_resource_spec_with_parameters(
        resource, parameters, None,
    )?);
    Ok(())
}

fn resource_clause_to_resource_spec_with_parameters(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    result_type: Option<crate::kernel::CType>,
) -> Result<CResourceSpec, ClickError> {
    match resource {
        ResourceClause::Quantified { quantity, resource } => Ok(CResourceSpec::Quantified {
            quantity: resource_argument_to_c_expression(quantity)?,
            resource: Box::new(resource_clause_to_resource_spec_with_parameters(
                resource,
                parameters,
                result_type,
            )?),
        }),
        ResourceClause::ViewMemory(segment) => Ok(CResourceSpec::ViewMemory(
            CMemorySegment::new(
                segment.base.clone(),
                segment.start.clone(),
                segment.end.clone(),
            )
            .with_element_width(
                crate::surface::lowering::contract_segment_element_width_for_result_type(
                    parameters,
                    segment,
                    result_type,
                ),
            ),
        )),
        ResourceClause::OwnMemory(segment) => Ok(CResourceSpec::OwnMemory(
            CMemorySegment::new(
                segment.base.clone(),
                segment.start.clone(),
                segment.end.clone(),
            )
            .with_element_width(
                crate::surface::lowering::contract_segment_element_width_for_result_type(
                    parameters,
                    segment,
                    result_type,
                ),
            ),
        )),
        ResourceClause::MemoryAggregate { .. } => Err(ClickError::new(
            "aggregate resource clauses must be expanded before one resource spec is required",
        )),
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => {
            let access = resource_access_to_kernel(*access);
            let arguments = arguments
                .iter()
                .map(resource_argument_to_c_expression)
                .collect::<Result<Vec<_>, _>>()?;
            let parameter_types = parameter_types
                .iter()
                .map(|c_type| c_type.to_kernel_type())
                .collect();
            Ok(match kind {
                ResourceKind::Composite => CResourceSpec::Composite {
                    access,
                    name: name.clone(),
                    arguments,
                    parameter_types,
                },
                ResourceKind::Token => CResourceSpec::Token {
                    access,
                    name: name.clone(),
                    arguments,
                    parameter_types,
                },
            })
        }
    }
}

pub(in crate::surface) fn resource_argument_contract_substitutions(
    definition: &ResourceDefinition,
    arguments: &[ContractExpression],
) -> Result<BTreeMap<String, ContractExpression>, ClickError> {
    if definition.parameters().len() != arguments.len() {
        return Err(ClickError::new(format!(
            "resource `{}` expects {} argument(s), got {}",
            definition.name(),
            definition.parameters().len(),
            arguments.len()
        )));
    }
    Ok(definition
        .parameters()
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
        .collect())
}

pub(in crate::surface) fn substitute_resource_clause_for_summary(
    resource: &ResourceClause,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Quantified { quantity, resource } => Ok(ResourceClause::Quantified {
            quantity: substitute_contract_expression(quantity, substitutions)?,
            resource: Box::new(substitute_resource_clause_for_summary(
                resource,
                substitutions,
            )?),
        }),
        ResourceClause::ViewMemory(segment) => Ok(ResourceClause::ViewMemory(
            substitute_contract_segment(segment, substitutions)?,
        )),
        ResourceClause::OwnMemory(segment) => Ok(ResourceClause::OwnMemory(
            substitute_contract_segment(segment, substitutions)?,
        )),
        ResourceClause::MemoryAggregate { access, segments } => {
            Ok(ResourceClause::MemoryAggregate {
                access: *access,
                segments: segments
                    .iter()
                    .map(|segment| substitute_contract_segment(segment, substitutions))
                    .collect::<Result<Vec<_>, _>>()?,
            })
        }
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            access: *access,
            kind: *kind,
            name: name.clone(),
            arguments: arguments
                .iter()
                .map(|argument| substitute_contract_expression(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

pub(in crate::surface) fn substitute_contract_segment(
    segment: &ContractSegment,
    substitutions: &BTreeMap<String, ContractExpression>,
) -> Result<ContractSegment, String> {
    let surface = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression(base, substitutions)?,
            start: substitute_contract_expression(start, substitutions)?,
            end: substitute_contract_expression(end, substitutions)?,
        },
        surface => surface.clone(),
    };
    Ok(ContractSegment {
        state: segment.state,
        base: substitute_c_fragment(&segment.base, substitutions)?,
        start: substitute_c_fragment(&segment.start, substitutions)?,
        end: substitute_c_fragment(&segment.end, substitutions)?,
        surface,
    })
}

pub(in crate::surface) fn resource_clause_to_resource_spec(
    resource: &ResourceClause,
) -> Result<CResourceSpec, ClickError> {
    match resource {
        ResourceClause::Quantified { quantity, resource } => Ok(CResourceSpec::Quantified {
            quantity: resource_argument_to_c_expression(quantity)?,
            resource: Box::new(resource_clause_to_resource_spec(resource)?),
        }),
        ResourceClause::ViewMemory(segment) => Ok(CResourceSpec::ViewMemory(CMemorySegment::new(
            segment.base.clone(),
            segment.start.clone(),
            segment.end.clone(),
        ))),
        ResourceClause::OwnMemory(segment) => Ok(CResourceSpec::OwnMemory(CMemorySegment::new(
            segment.base.clone(),
            segment.start.clone(),
            segment.end.clone(),
        ))),
        ResourceClause::MemoryAggregate { .. } => Err(ClickError::new(
            "aggregate resource clauses must be expanded before one resource spec is required",
        )),
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => {
            let access = resource_access_to_kernel(*access);
            let arguments = arguments
                .iter()
                .map(resource_argument_to_c_expression)
                .collect::<Result<Vec<_>, _>>()?;
            let parameter_types = parameter_types
                .iter()
                .map(|c_type| c_type.to_kernel_type())
                .collect();
            Ok(match kind {
                ResourceKind::Composite => CResourceSpec::Composite {
                    access,
                    name: name.clone(),
                    arguments,
                    parameter_types,
                },
                ResourceKind::Token => CResourceSpec::Token {
                    access,
                    name: name.clone(),
                    arguments,
                    parameter_types,
                },
            })
        }
    }
}

pub(in crate::surface) fn resource_access_to_kernel(
    access: ResourceAccessMode,
) -> CResourceAccessMode {
    match access {
        ResourceAccessMode::Own => CResourceAccessMode::Own,
        ResourceAccessMode::View => CResourceAccessMode::View,
    }
}

pub(in crate::surface) fn function_claim_label(
    function_name: &str,
    claim: &FunctionClaimRef<'_>,
) -> String {
    match claim {
        FunctionClaimRef::Ensure(index, ensure) => match ensure.name() {
            Some(name) => format!("{function_name}.{name}"),
            None => format!("{function_name}.ensures_{index}"),
        },
        FunctionClaimRef::Effect(index, effect) => match effect.effect() {
            Effect::Immutable => format!("{function_name}.immutable_{index}"),
            Effect::Mutable(_) => format!("{function_name}.mutable_{index}"),
        },
    }
}

pub(in crate::surface) fn implication_body(proposition: &Proposition) -> &Proposition {
    match proposition {
        Proposition::Implies(_, body) => implication_body(body),
        _ => proposition,
    }
}

pub(in crate::surface) fn assumptions_from_propositions(
    propositions: &[Proposition],
) -> PureFactContext {
    propositions
        .iter()
        .cloned()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition)
}

pub(in crate::surface) fn check_signature(
    signature: &FunctionSignature,
    parsed_function: &syntax::C0Function,
    source_path: &str,
) -> Result<(), ClickError> {
    if signature.return_type() != parsed_function.return_type() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click return type is {:?}, C return type is {:?}",
            signature.name(),
            signature.return_type(),
            parsed_function.return_type()
        )));
    }

    if signature.parameters().len() != parsed_function.parameters().len() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click has {} parameters, C has {}",
            signature.name(),
            signature.parameters().len(),
            parsed_function.parameters().len()
        )));
    }

    for (index, (expected, actual)) in signature
        .parameters()
        .iter()
        .zip(parsed_function.parameters())
        .enumerate()
    {
        if expected.c_type() != actual.c_type()
            || expected.name() != actual.name()
            || expected.struct_name() != actual.struct_name()
            || expected.function_pointer_signature() != actual.function_pointer_signature()
        {
            return Err(ClickError::new(format!(
                "signature mismatch for `{}` parameter {} in `{source_path}`: .click has {} {}, C has {} {}",
                signature.name(),
                index + 1,
                describe_parameter_type(expected.c_type(), expected.struct_name()),
                expected.name(),
                describe_parameter_type(actual.c_type(), actual.struct_name()),
                actual.name()
            )));
        }
    }

    Ok(())
}

pub(in crate::surface) fn describe_parameter_type(
    c_type: C0Type,
    struct_name: Option<&str>,
) -> String {
    match struct_name {
        Some(name) if matches!(c_type, C0Type::UInt8Array(_)) => format!("struct {name}"),
        Some(name) => format!("struct {name}*"),
        None => format!("{c_type:?}"),
    }
}

pub(in crate::surface) fn validate_region_proof_clauses(
    function_block: &FunctionBlock,
    parsed_function: &syntax::C0Function,
) -> Result<(), ClickError> {
    let loop_count = count_loops(parsed_function.body());
    for region_proof_clause in function_block.structural_clauses() {
        match region_proof_clause.region() {
            CodeRegion::Function => {
                return Err(ClickError::new(
                    "`for function` region proof blocks are not supported",
                ));
            }
            CodeRegion::Loop(index) if *index >= loop_count => {
                return Err(ClickError::new(format!(
                    "`{}` has no `loop({index})` code region; it contains {loop_count} loop(s)",
                    function_block.signature().name()
                )));
            }
            CodeRegion::Statement(_) => {
                return Err(ClickError::new(
                    "internal frontier-loop proof was bound to a statement region",
                ));
            }
            CodeRegion::Loop(_) => {}
        }

        for (phase, proof) in [
            ("initialize", region_proof_clause.initialize_proof()),
            ("preserve", region_proof_clause.preserve_proof()),
        ] {
            let Some(proof) = proof else {
                continue;
            };
            if proof.is_frame_tactic() {
                return Err(ClickError::new(format!(
                    "`{phase}` must use `auto`, `simp`, or an explicit proof script"
                )));
            }
        }

        validate_loop_phase_proof("initialize", region_proof_clause.initialize_proof())?;
        validate_loop_phase_proof("preserve", region_proof_clause.preserve_proof())?;

        for item in region_proof_clause.items() {
            if item.is_effect_kind() {
                if !item.proof().is_auto_or_frame_tactic()
                    && !matches!(
                        item.proof(),
                        SourceProof::Script(tactics)
                            if ProofCertificate::from_proof_tactics(tactics).is_ok()
                    )
                {
                    return Err(ClickError::new(
                        "`immutable` and `mutable` region proof clauses must use the default prover, `by auto;`, `by frame;`, or a surface certificate",
                    ));
                }
            } else {
                debug_assert!(item.proof().is_auto_tactic());
            }
        }
    }
    Ok(())
}

pub(in crate::surface) fn validate_loop_phase_proof(
    phase: &str,
    proof: Option<&SourceProof>,
) -> Result<(), ClickError> {
    let Some(SourceProof::Script(tactics)) = proof else {
        return Ok(());
    };
    if phase == "preserve" {
        return Ok(());
    }
    validate_loop_initialization_tactics(tactics)
}

pub(in crate::surface) fn validate_loop_initialization_tactics(
    tactics: &[ProofTactic],
) -> Result<(), ClickError> {
    for tactic in tactics {
        match tactic {
            ProofTactic::UnfoldPredicate(_)
            | ProofTactic::UnfoldFunction(_)
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::Have(_)
            | ProofTactic::Assumption
            | ProofTactic::Normalize
            | ProofTactic::Rewrite(_)
            | ProofTactic::Simp => {}
            ProofTactic::If(proof_if) => {
                validate_loop_initialization_tactics(&proof_if.then_tactics)?;
                validate_loop_initialization_tactics(&proof_if.else_tactics)?;
            }
            ProofTactic::Cases(proof_cases) => {
                validate_loop_initialization_tactics(&proof_cases.left_tactics)?;
                validate_loop_initialization_tactics(&proof_cases.right_tactics)?;
            }
            tactic => {
                return Err(ClickError::new(format!(
                    "`initialize` is a pure proof and cannot use `{}`",
                    validation::tactic_name(tactic)
                )));
            }
        }
    }
    Ok(())
}
