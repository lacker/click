use super::*;

fn collect_applied_theorems(tactics: &[ProofTactic], names: &mut BTreeSet<String>) {
    for tactic in tactics {
        match tactic {
            ProofTactic::ApplyTheorem(application)
            | ProofTactic::ApplyTheoremUsing { application, .. } => {
                names.insert(application.name.clone());
            }
            ProofTactic::Have(proof_have) => {
                if let Proof::Script(tactics) = &proof_have.proof {
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
                    if let Proof::Script(tactics) = &item.proof {
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
                    if let Proof::Script(tactics) = proof {
                        collect_applied_theorems(tactics, names);
                    }
                }
            }
            _ => {}
        }
    }
}

fn collect_applied_theorems_from_proof(proof: &Proof, names: &mut BTreeSet<String>) {
    if let Proof::Script(tactics) = proof {
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

pub(in crate::lang::click) fn verify_click_file_theorems(
    file: &ClickFile,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let predicate_definitions = combined_predicate_definitions(file)?;
    let click_function_definitions = combined_click_function_definitions(file)?;
    let (theorem_definitions, stdlib_theorem_ensure_count) =
        combined_theorem_definitions_with_stdlib_ensure_count(file)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
    let click_function_environment = ClickFunctionEnvironment::new(&click_function_definitions);
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

pub(in crate::lang::click) fn verify_click_theorems_with_c_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let sources = c_sources.iter().copied().collect::<BTreeMap<_, _>>();
    let layouts = parse_c_struct_layouts(&sources)?;
    let file = parser::parse_with_struct_layouts(click_source, layouts)?;
    verify_click_file_theorems(&file)
}

pub(in crate::lang::click) fn parse_c0_click_file(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<ClickFile, ClickError> {
    let sources = c_sources.iter().copied().collect::<BTreeMap<_, _>>();
    let struct_layouts = parse_c_struct_layouts(&sources)?;
    parser::parse_with_struct_layouts(click_source, struct_layouts)
}

pub(in crate::lang::click) fn proof_unit_erased_click_file(
    mut file: ClickFile,
    target: &VerificationTarget,
) -> ClickFile {
    if let VerificationTarget::Theorem(target_name) = target {
        for theorem in &mut file.theorem_definitions {
            if theorem.name == *target_name {
                for ensure in &mut theorem.ensures {
                    ensure.proof = Proof::Default;
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
            function.grouped_proof = Some(Proof::Default);
        }
        for ensure in &mut function.ensures {
            ensure.proof = Proof::Default;
        }
        for effect in &mut function.effects {
            effect.proof = Proof::Default;
        }
        for clause in &mut function.structural_clauses {
            // Omitted loop-phase proofs and explicit default/expanded proofs
            // are all syntax for the selected function's proof unit.  Erase
            // presence as well as contents so inserting an expansion for an
            // omitted phase does not look like an interface change.
            clause.initialize_proof = None;
            clause.preserve_proof = None;
            for item in &mut clause.items {
                item.proof = Proof::Default;
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
pub(in crate::lang::click) fn verify_c0_sources_with_expansion_capture(
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
            for dependency in c0_statement_calls(function.body()).into_iter().flatten() {
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

pub(in crate::lang::click) fn verify_c0_sources_with_limits(
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

pub(in crate::lang::click) fn verify_c0_sources_targeted(
    click_source: &str,
    c_sources: &[(&str, &str)],
    verification_target: Option<VerificationTarget>,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    verify_c0_sources_with_environment(click_source, c_sources, verification_target, None, None)
        .map(|(verified, _)| verified)
}

pub(in crate::lang::click) fn verify_c0_sources_with_environment(
    click_source: &str,
    c_sources: &[(&str, &str)],
    verification_target: Option<VerificationTarget>,
    initial_function_environment: Option<CExecutionEnvironment>,
    mut expansion_capture: Option<&mut ExpansionCapture>,
) -> Result<(Vec<VerifiedCTheorem>, CExecutionEnvironment), ClickError> {
    check_verification_deadline()?;
    let (file, parsed_sources, selected_functions) = {
        let _timing = VerificationTimingPhase::new("frontend");
        let c_sources: BTreeMap<&str, &str> = c_sources.iter().copied().collect();
        let struct_layouts = parse_c_struct_layouts(&c_sources)?;
        let file = parser::parse_with_struct_layouts(click_source, struct_layouts)?;
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
        let click_function_environment = ClickFunctionEnvironment::new(&click_function_definitions);
        let resource_environment = ResourceEnvironment::new(&resource_definitions);
        let built_function_environment = build_function_environment(
            &parsed_sources,
            file.function_blocks(),
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
            theorem
                .theorem_definition
                .parameters()
                .iter()
                .all(|parameter| matches!(parameter.c_type(), C0Type::Int32))
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
            if let Some(authority) = &theorem.kernel_authority {
                theorem_certification_authorities
                    .entry(theorem.theorem_definition.name().to_string())
                    .or_default()
                    .push(authority.clone());
            }
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
    check_verification_deadline()?;
    let mut verified = Vec::new();

    for function_block in file.function_blocks {
        check_verification_deadline()?;
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
            proof: Proof::Tactic(SmartTactic::Auto),
        };
        let mut claims = function_claims(&function_block);
        let has_explicit_claims = !claims.is_empty();
        if !has_explicit_claims {
            claims.push(FunctionClaimRef::Ensure(0, &implicit_safety_clause));
        }
        let mut function_verified = Vec::new();
        if let Some(grouped_proof) = function_block.grouped_proof() {
            let theorems = match grouped_proof {
                Proof::Tactic(SmartTactic::Auto) => prove_claims_by_grouped_auto(
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
                Proof::Script(tactics) => prove_claims_by_grouped_script(
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
                Proof::Default | Proof::Tactic(SmartTactic::Simp | SmartTactic::Frame) => {
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
                    Proof::Default | Proof::Tactic(SmartTactic::Auto) => prove_claim_by_auto(
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
                    Proof::Tactic(SmartTactic::Frame) => prove_claim_by_frame(
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
                    Proof::Tactic(SmartTactic::Simp) => prove_claim_by_simp(
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
                    Proof::Script(tactics) => prove_claim_by_script(
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
        // A frontier-local proof constructs loop annotations and checked
        // rules while replaying the actual execution path. Final whole-contract
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
        // A sized array parameter spelling (`int32 p[2]`) declares its span
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
                base: base.clone(),
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
            if matches!(
                contract_execution.limit(),
                Some(crate::kernel::ExecutionLimit::Deadline)
            ) {
                return Err(ClickError::new(format!(
                    "verification budget exhausted inside {}",
                    instrumentation::deadline_context()
                )));
            }
            if instrumentation::enabled() {
                instrumentation::emit(VerificationEvent::ContractExecutionFinished {
                    function: function_block.signature.name().to_string(),
                    elapsed: certification_started.elapsed(),
                });
            }
            let claims_started = std::time::Instant::now();
            if contract_execution.path_count() == 0 && contract_execution.limit().is_none() {
                return Err(ClickError::new(format!(
                    "could not certify contract for `{}`: exact symbolic execution produced no valid paths",
                    function_block.signature.name(),
                )));
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
                    let name = termination_measure_name(
                        measure,
                        &format!(
                            "frontier-local loop {loop_index} `decreases` in `{}`",
                            function_block.signature.name()
                        ),
                    )?;
                    if let Some(previous) = loop_measures.insert(*loop_index, name.clone())
                        && previous != name
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
            let certified_claims = {
                let _certification_timing = VerificationTimingPhase::new("certification");
                c_verified_function_contract_claims(&contract_function, &contract_execution)
            };
            if instrumentation::enabled() {
                instrumentation::emit(VerificationEvent::ContractClaimsFinished {
                    function: function_block.signature.name().to_string(),
                    elapsed: claims_started.elapsed(),
                });
            }
            let Some(certified_claims) = certified_claims else {
                let detail = match c_unverified_function_contract_claims(
                    &contract_function,
                    &contract_execution,
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
            let proof_objects = function_verified
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
            let rule =
                c_verified_function_rule(contract_function, &proof_objects).ok_or_else(|| {
                    ClickError::new(format!(
                        "could not package verified contract for `{}`",
                        function_block.signature.name()
                    ))
                })?;
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
    let termination_rules =
        c_verified_function_termination_rules(&partial_rules, &termination_plans).map_err(
            |error| ClickError::new(format!("could not certify C termination: {error}")),
        )?;
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

pub(in crate::lang::click) fn tactic_expansion_required_functions(
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
        CProofClaim::Grouped => function_block.grouped_proof().and_then(Proof::tactics),
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
    let statement_calls = c0_statement_calls(parsed_function.body());
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
            pending.extend(c0_statement_calls(parsed.body()).into_iter().flatten());
        }
    }
    Ok(required)
}

pub(in crate::lang::click) fn tactic_expansion_dependency_context(
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
        for dependency in c0_statement_calls(function.body())
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

pub(in crate::lang::click) fn verification_required_functions(
    file: &ClickFile,
    parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>,
    function_name: &str,
) -> Result<BTreeSet<String>, ClickError> {
    if !file
        .function_blocks()
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
        let parsed = &parsed_sources
            .get(&name)
            .ok_or_else(|| ClickError::new(format!("no C source defines `{name}`")))?
            .1;
        pending.extend(c0_statement_calls(parsed.body()).into_iter().flatten());
    }
    Ok(required)
}

pub(in crate::lang::click) fn c0_statement_calls(
    statement: &syntax::C0Statement,
) -> Vec<BTreeSet<String>> {
    fn visit(statement: &syntax::C0Statement, calls: &mut Vec<BTreeSet<String>>) {
        match statement {
            syntax::C0Statement::Skip => {}
            syntax::C0Statement::Seq(first, second) => {
                visit(first, calls);
                visit(second, calls);
            }
            syntax::C0Statement::If {
                then_branch,
                else_branch,
                ..
            } => {
                calls.push(BTreeSet::new());
                visit(then_branch, calls);
                visit(else_branch, calls);
            }
            syntax::C0Statement::While { body, .. } => {
                calls.push(BTreeSet::new());
                visit(body, calls);
            }
            syntax::C0Statement::CallAssign { function_name, .. } => {
                calls.push(BTreeSet::from([function_name.clone()]));
            }
            syntax::C0Statement::Call { function_name, .. } => {
                calls.push(BTreeSet::from([function_name.clone()]));
            }
            syntax::C0Statement::Declare { .. }
            | syntax::C0Statement::Assign { .. }
            | syntax::C0Statement::HeapAllocate { .. }
            | syntax::C0Statement::HeapFree { .. }
            | syntax::C0Statement::Return(_)
            | syntax::C0Statement::Store { .. } => calls.push(BTreeSet::new()),
        }
    }

    let mut calls = Vec::new();
    visit(statement, &mut calls);
    calls
}

pub(in crate::lang::click) fn termination_measure_name(
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

pub(in crate::lang::click) fn c_function_termination_plans(
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
            let name = termination_measure_name(
                measure,
                &format!(
                    "loop {index} `decreases` in `{}`",
                    function.signature().name()
                ),
            )?;
            if loop_measures.insert(*index, name).is_some() {
                return Err(ClickError::new(format!(
                    "duplicate `decreases` measure for loop {index} in `{}`",
                    function.signature().name()
                )));
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

pub(in crate::lang::click) fn parse_c_struct_layouts(
    c_sources: &BTreeMap<&str, &str>,
) -> Result<BTreeMap<String, syntax::C0StructLayout>, ClickError> {
    let mut layouts = BTreeMap::new();
    for (source_path, c_source) in c_sources {
        let function = syntax::parse_function(c_source).map_err(|error| {
            ClickError::new(format!("failed to parse C source `{source_path}`: {error}"))
        })?;
        for (name, layout) in function.structs() {
            if let Some(previous) = layouts.insert(name.clone(), layout.clone())
                && previous != *layout
            {
                return Err(ClickError::new(format!(
                    "conflicting declarations for struct `{name}`"
                )));
            }
        }
    }
    Ok(layouts)
}

pub(in crate::lang::click) fn parse_verified_sources(
    file: &ClickFile,
    c_sources: &BTreeMap<&str, &str>,
) -> Result<BTreeMap<String, (String, syntax::C0Function)>, ClickError> {
    if file.verifying_sources.is_empty() {
        if file.function_blocks().is_empty() {
            return Ok(BTreeMap::new());
        }
        return Err(ClickError::new(
            "`.click` file must declare at least one `verifying \"source.c\";`",
        ));
    }

    let mut parsed = BTreeMap::new();
    for source_path in &file.verifying_sources {
        let c_source = *c_sources.get(source_path.as_str()).ok_or_else(|| {
            ClickError::new(format!(
                "`verifying` refers to missing C source `{source_path}`"
            ))
        })?;
        let function = syntax::parse_function(c_source).map_err(|error| {
            ClickError::new(format!("failed to parse C source `{source_path}`: {error}"))
        })?;
        let function_name = function.name().to_string();
        let previous = parsed.insert(function_name.clone(), (source_path.clone(), function));
        if previous.is_some() {
            return Err(ClickError::new(format!(
                "more than one `verifying` source defines function `{function_name}`"
            )));
        }
    }

    Ok(parsed)
}

pub(in crate::lang::click) fn build_function_environment(
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
                    function_resource_summary(function_block, resource_environment)?;
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
                function
                    .to_kernel_function()
                    .with_resource_summary(resource_requires, resource_ensures)
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
                    )
            }
            None => function.to_kernel_function(),
        };
        environment = environment.with_function(function);
    }
    Ok(environment)
}

pub(in crate::lang::click) fn function_resource_summary(
    function_block: &FunctionBlock,
    resource_environment: &ResourceEnvironment,
) -> Result<(Vec<CResourceSpec>, Vec<CResourceSpec>), ClickError> {
    let mut requires = Vec::new();
    for requirement in function_block.requires() {
        let Requirement::Resource(resource) = requirement.inner() else {
            continue;
        };
        append_entry_resource_specs(resource, resource_environment, &mut requires)?;
    }
    let ensures = function_block
        .ensures()
        .iter()
        .filter_map(|ensure| match ensure.ensure() {
            Ensure::Resource(resource) => Some(resource_clause_to_resource_spec(resource)),
            _ => None,
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((requires, ensures))
}

pub(in crate::lang::click) fn composite_resource_definitions(
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
        let observes_its_population = body.facts().iter().any(proposition_contains_resource_count);
        definitions.push(if observes_its_population {
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
        });
    }
    Ok(definitions)
}

pub(in crate::lang::click) fn append_entry_resource_specs(
    resource: &ResourceClause,
    _resource_environment: &ResourceEnvironment,
    specs: &mut Vec<CResourceSpec>,
) -> Result<(), ClickError> {
    specs.push(resource_clause_to_resource_spec(resource)?);
    Ok(())
}

pub(in crate::lang::click) fn resource_argument_contract_substitutions(
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

pub(in crate::lang::click) fn substitute_resource_clause_for_summary(
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
        ResourceClause::Read(segment) => Ok(ResourceClause::Read(substitute_contract_segment(
            segment,
            substitutions,
        )?)),
        ResourceClause::Write(segment) => Ok(ResourceClause::Write(substitute_contract_segment(
            segment,
            substitutions,
        )?)),
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

pub(in crate::lang::click) fn substitute_contract_segment(
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

pub(in crate::lang::click) fn resource_clause_to_resource_spec(
    resource: &ResourceClause,
) -> Result<CResourceSpec, ClickError> {
    match resource {
        ResourceClause::Quantified { quantity, resource } => Ok(CResourceSpec::Quantified {
            quantity: resource_argument_to_c_expression(quantity)?,
            resource: Box::new(resource_clause_to_resource_spec(resource)?),
        }),
        ResourceClause::Read(segment) => Ok(CResourceSpec::Read(CMemorySegment::new(
            segment.base.clone(),
            segment.start.clone(),
            segment.end.clone(),
        ))),
        ResourceClause::Write(segment) => Ok(CResourceSpec::Write(CMemorySegment::new(
            segment.base.clone(),
            segment.start.clone(),
            segment.end.clone(),
        ))),
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

pub(in crate::lang::click) fn resource_access_to_kernel(
    access: ResourceAccessMode,
) -> CResourceAccessMode {
    match access {
        ResourceAccessMode::Own => CResourceAccessMode::Own,
        ResourceAccessMode::View => CResourceAccessMode::View,
    }
}

pub(in crate::lang::click) fn function_claim_label(
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

pub(in crate::lang::click) fn implication_body(proposition: &Proposition) -> &Proposition {
    match proposition {
        Proposition::Implies(_, body) => implication_body(body),
        _ => proposition,
    }
}

pub(in crate::lang::click) fn assumptions_from_propositions(
    propositions: &[Proposition],
) -> PureFactContext {
    propositions
        .iter()
        .cloned()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition)
}

pub(in crate::lang::click) fn check_signature(
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

pub(in crate::lang::click) fn describe_parameter_type(
    c_type: C0Type,
    struct_name: Option<&str>,
) -> String {
    match struct_name {
        Some(name) => format!("struct {name}*"),
        None => format!("{c_type:?}"),
    }
}

pub(in crate::lang::click) fn validate_region_proof_clauses(
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
                        Proof::Script(tactics)
                            if SimpleProof::from_proof_tactics(tactics).is_ok()
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

pub(in crate::lang::click) fn validate_loop_phase_proof(
    phase: &str,
    proof: Option<&Proof>,
) -> Result<(), ClickError> {
    let Some(Proof::Script(tactics)) = proof else {
        return Ok(());
    };
    if phase == "preserve" {
        return Ok(());
    }
    validate_loop_initialization_tactics(tactics)
}

pub(in crate::lang::click) fn validate_loop_initialization_tactics(
    tactics: &[ProofTactic],
) -> Result<(), ClickError> {
    for tactic in tactics {
        match tactic {
            ProofTactic::UnfoldPredicate(_)
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
