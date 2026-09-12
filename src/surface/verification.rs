use super::validation::combined_algebraic_type_definitions;
use super::*;
use crate::languages::c::compiler_import::PreparedCImport;
#[cfg(test)]
use std::cell::Cell;
use std::cell::RefCell;
use std::sync::Arc;

/// Typed input boundary for C verification. The bundle variant preserves the
/// legacy source map while leaving room for compiler-prepared inputs without
/// ambient or global state.
pub(in crate::surface) struct CSourceContext<'a> {
    bundle: Option<BTreeMap<&'a str, &'a str>>,
    imports: Option<&'a [PreparedCImport]>,
    prepared_by_source: Option<BTreeMap<&'a str, &'a PreparedCImport>>,
    prepared_project_identity: Option<String>,
    prepared_duplicates: bool,
    parsed_units: RefCell<BTreeMap<String, Arc<syntax::C0TranslationUnit>>>,
    #[cfg(test)]
    prepared_parse_count: Cell<usize>,
}

impl<'a> CSourceContext<'a> {
    pub(in crate::surface) fn bundle(sources: &[(&'a str, &'a str)]) -> Self {
        Self {
            bundle: Some(sources.iter().copied().collect()),
            imports: None,
            prepared_by_source: None,
            prepared_project_identity: None,
            prepared_duplicates: false,
            parsed_units: RefCell::new(BTreeMap::new()),
            #[cfg(test)]
            prepared_parse_count: Cell::new(0),
        }
    }

    pub(in crate::surface) fn prepared(imports: &'a [PreparedCImport]) -> Self {
        let mut identities = imports
            .iter()
            .map(|import| import.identity().to_string())
            .collect::<Vec<_>>();
        identities.sort();
        identities.dedup();
        let duplicate_logical_source = imports
            .iter()
            .map(|import| import.logical_source())
            .collect::<BTreeSet<_>>()
            .len()
            != imports.len();
        let project_identity = if imports.len() == 1 {
            imports[0].identity().to_string()
        } else {
            let mut framed = String::from("project:");
            for identity in &identities {
                framed.push_str(&identity.len().to_string());
                framed.push(':');
                framed.push_str(identity);
                framed.push(';');
            }
            use sha2::{Digest, Sha256};
            format!("{:x}", Sha256::digest(framed.as_bytes()))
        };
        Self {
            bundle: None,
            imports: Some(imports),
            prepared_by_source: Some(
                imports
                    .iter()
                    .map(|import| (import.logical_source(), import))
                    .collect(),
            ),
            prepared_project_identity: Some(project_identity),
            prepared_duplicates: duplicate_logical_source,
            parsed_units: RefCell::new(BTreeMap::new()),
            #[cfg(test)]
            prepared_parse_count: Cell::new(0),
        }
    }

    fn bundle_sources(&self) -> Result<&BTreeMap<&'a str, &'a str>, ClickError> {
        self.bundle.as_ref().ok_or_else(|| {
            ClickError::new(
                "incremental source comparison is unavailable for compiler-prepared imports",
            )
        })
    }
}

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
            ProofTactic::CloseInvariantsBy(body) => collect_applied_theorems(body, names),
            ProofTactic::Both(both) => {
                collect_applied_theorems(&both.left_tactics, names);
                collect_applied_theorems(&both.right_tactics, names);
            }
            ProofTactic::Cases(proof_cases) => {
                collect_applied_theorems(&proof_cases.left_tactics, names);
                collect_applied_theorems(&proof_cases.right_tactics, names);
            }
            ProofTactic::StructuralInduct {
                hypothesis, arms, ..
            } => {
                for arm in arms {
                    let mut arm_names = BTreeSet::new();
                    collect_applied_theorems(&arm.tactics, &mut arm_names);
                    arm_names.remove(hypothesis);
                    names.extend(arm_names);
                }
            }
            ProofTactic::Match(proof_match) => {
                for arm in &proof_match.arms {
                    collect_applied_theorems(&arm.tactics, names);
                }
            }
            ProofTactic::Branch(proof_branch) => {
                collect_applied_theorems(&proof_branch.then_tactics, names);
                collect_applied_theorems(&proof_branch.else_tactics, names);
            }
            ProofTactic::Loop(clause) => {
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
    for clause in function.structural_clauses() {
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

/// Whether a theorem's binders are all kernel sorts that certification can
/// quantify over, so its verified statement can become a certification fact.
fn theorem_has_certification_binders(theorem: &TheoremDefinition) -> bool {
    theorem.parameters().iter().all(|parameter| {
        matches!(
            parameter.click_type(),
            ClickType::C(C0Type::Int32 | C0Type::FunctionPointer(_))
        )
    })
}

/// Records verified pure theorems over supported kernel binders as closed
/// universally-quantified facts with their kernel authority, so kernel
/// contract certification can discharge obligations the surface proof
/// established by `apply`.
fn record_theorem_certification_authority(
    verified_theorems: &[VerifiedPureTheorem],
    facts: &mut BTreeMap<String, Vec<Proposition>>,
    authorities: &mut BTreeMap<String, Vec<CVerifiedPureTheorem>>,
) {
    for theorem in verified_theorems.iter().filter(|theorem| {
        theorem.kernel_authority.is_some()
            && theorem_has_certification_binders(&theorem.theorem_definition)
    }) {
        let implication = theorem
            .requires
            .iter()
            .rev()
            .fold(theorem.conclusion.clone(), |body, requirement| {
                Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
            });
        let fact = theorem
            .theorem_definition
            .parameters()
            .iter()
            .enumerate()
            .rev()
            .fold(implication, |body, (index, parameter)| {
                let sort = match parameter.c_type() {
                    C0Type::Int32 => crate::kernel::Sort::CInt32,
                    C0Type::FunctionPointer(_) => {
                        crate::kernel::Sort::CPointer(parameter.c_type().to_kernel_type())
                    }
                    _ => unreachable!("the theorem binder filter admits only supported types"),
                };
                Proposition::ForAll {
                    var: crate::kernel::Variable(index as u64),
                    sort,
                    body: Box::new(body),
                }
            });
        facts
            .entry(theorem.theorem_definition.name().to_string())
            .or_default()
            .push(fact);
        let authority = theorem
            .kernel_authority
            .as_ref()
            .expect("theorem certification facts require kernel authority");
        authorities
            .entry(theorem.theorem_definition.name().to_string())
            .or_default()
            .push(authority.clone());
    }
}

/// The file's own theorems that this verification must prove: all of them, or
/// for a targeted verification the dependency closure of the selected
/// functions and theorem. Standard-library theorems are dependencies and are
/// never selected.
fn selected_theorem_definitions(
    file: &ClickFile,
    selected_functions: Option<&BTreeSet<String>>,
    verification_target: Option<&VerificationTarget>,
) -> Vec<TheoremDefinition> {
    let definitions = file.theorem_definitions();
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
        .filter(|definition| required.contains(definition.name()))
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
    verify_click_file_theorems_with_environment(file, None)
}

fn verify_click_file_theorems_with_environment(
    file: &ClickFile,
    function_environment: Option<&CExecutionEnvironment>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let predicate_definitions = combined_predicate_definitions(file)?;
    let click_function_definitions = combined_click_function_definitions(file)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions)
        .with_contracts(file.contract_definitions());
    let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
        &click_function_definitions,
        &combined_algebraic_type_definitions(file)?,
    );
    let function_source_registry = Arc::new(FunctionSourceRegistry::from_function_blocks(
        &combined_external_function_blocks(file)?,
    )?);
    verify_theorem_definitions(
        standard_library_theorem_definitions()?,
        file.theorem_definitions(),
        &predicate_environment,
        &click_function_environment,
        function_environment,
        &ResourceEnvironment::new(&combined_resource_definitions(file)?),
        function_source_registry,
    )
}

/// Proves every standard-library theorem.
///
/// Ordinary verification applies standard-library theorems as dependency
/// declarations without re-proving them, the way a caller uses a verified
/// function's contract. This is the entry point that proves them, against the
/// standard library alone, and the gate runs it.
pub fn verify_standard_library() -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let empty = parse("")?;
    let predicate_definitions = combined_predicate_definitions(&empty)?;
    let click_function_definitions = combined_click_function_definitions(&empty)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
    let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
        &click_function_definitions,
        &combined_algebraic_type_definitions(&empty)?,
    );
    let function_source_registry = Arc::new(FunctionSourceRegistry::from_function_blocks(
        &combined_external_function_blocks(&empty)?,
    )?);
    verify_theorem_definitions(
        &[],
        standard_library_theorem_definitions()?,
        &predicate_environment,
        &click_function_environment,
        None,
        &ResourceEnvironment::new(&combined_resource_definitions(&empty)?),
        function_source_registry,
    )
}

#[cfg(test)]
pub(in crate::surface) fn verify_click_theorems_with_c_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    verify_click_theorems_with_context(click_source, &sources)
}

pub(in crate::surface) fn verify_click_theorems_with_context(
    click_source: &str,
    sources: &CSourceContext<'_>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let (
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
    ) = parse_c_layouts(click_source, sources)?;
    let file = parser::parse_with_layouts_and_aggregate_objects(
        click_source,
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
    )?;
    let parsed_sources = parse_verified_sources_context(&file, sources)?;
    let predicate_definitions = combined_predicate_definitions(&file)?;
    let click_function_definitions = combined_click_function_definitions(&file)?;
    let resource_definitions = combined_resource_definitions(&file)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions)
        .with_contracts(file.contract_definitions());
    let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
        &click_function_definitions,
        &combined_algebraic_type_definitions(&file)?,
    );
    let resource_environment = ResourceEnvironment::new(&resource_definitions);
    let external_and_user_function_blocks = combined_external_function_blocks(&file)?;
    let mut function_environment = build_function_environment(
        &parsed_sources,
        &external_and_user_function_blocks,
        file.contract_definitions(),
        &predicate_environment,
        &click_function_environment,
        &resource_environment,
    )?;
    let refinement_targets = file
        .theorem_definitions()
        .iter()
        .flat_map(|theorem| contract_refinement_targets(&file, theorem.name()))
        .collect::<BTreeSet<_>>();
    for target in refinement_targets {
        let Some(function) = function_environment.get_function(&target).cloned() else {
            continue;
        };
        if let Some(hypothesis) = crate::kernel::c_recursive_function_contract_hypothesis(function)
        {
            function_environment = function_environment.with_verified_function_rule(hypothesis);
        }
    }
    verify_click_file_theorems_with_environment(&file, Some(&function_environment))
}

fn contract_refinement_targets(file: &ClickFile, theorem_name: &str) -> BTreeSet<String> {
    let contract_names = file
        .contract_definitions()
        .iter()
        .map(ContractDefinition::name)
        .collect::<BTreeSet<_>>();
    let mut targets = BTreeSet::new();
    let Some(theorem) = file
        .theorem_definitions()
        .iter()
        .find(|theorem| theorem.name() == theorem_name)
    else {
        return targets;
    };
    for ensure in theorem.ensures() {
        let Ensure::Proposition(ClickProposition::PredicateCall { name, arguments }) =
            ensure.ensure()
        else {
            continue;
        };
        if !contract_names.contains(name.as_str()) {
            continue;
        }
        let [argument] = arguments.as_slice() else {
            continue;
        };
        if let Some(target) = contract_expression_function_address(argument) {
            targets.insert(target.to_string());
        }
    }
    targets
}

pub(in crate::surface) fn parse_c0_click_file(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<ClickFile, ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    parse_c0_click_file_context(click_source, &sources)
}

fn parse_c0_click_file_context(
    click_source: &str,
    sources: &CSourceContext<'_>,
) -> Result<ClickFile, ClickError> {
    let (
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
    ) = parse_c_layouts(click_source, sources)?;
    parser::parse_with_layouts_and_aggregate_objects(
        click_source,
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
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
        for clause in &mut function.structural_clauses {
            // Omitted loop-phase proofs and explicit default/expanded proofs
            // are all syntax for the selected function's proof unit.  Erase
            // presence as well as contents so inserting an expansion for an
            // omitted phase does not look like an interface change.
            clause.initialize_proof = None;
            clause.preserve_proof = None;
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

/// Verifies compiler-prepared translation units through the same engine used
/// by legacy source bundles.
pub fn verify_c0_prepared_sources(
    click_source: &str,
    imports: &[PreparedCImport],
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = CSourceContext::prepared(imports);
        verify_c0_sources_with_context(click_source, &sources, None, None, None)
            .map(|(verified, _)| verified)
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

pub(in crate::surface) fn verify_c0_sources_with_expansion_capture_context(
    click_source: &str,
    c_sources: &CSourceContext<'_>,
    expansion_capture: &mut ExpansionCapture,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        verify_c0_sources_with_context(click_source, c_sources, None, None, Some(expansion_capture))
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

fn c0_imported_headers(
    file: &ClickFile,
    c_sources: &BTreeMap<&str, &str>,
) -> Result<BTreeMap<String, BTreeSet<String>>, ClickError> {
    let mut imported = BTreeMap::new();
    for source_path in &file.verifying_sources {
        let mut pending = vec![source_path.clone()];
        let mut seen = BTreeSet::new();
        let mut headers = BTreeSet::new();
        while let Some(path) = pending.pop() {
            if !seen.insert(path.clone()) {
                continue;
            }
            let source = c_sources.get(path.as_str()).copied().ok_or_else(|| {
                ClickError::new(format!(
                    "source bundle is missing `{path}` while tracking local C headers"
                ))
            })?;
            for include in crate::languages::c::source::local_include_paths(&path, source).map_err(
                |error| {
                    ClickError::new(format!(
                        "failed to process local C headers for `{path}`: {error}"
                    ))
                },
            )? {
                headers.insert(include.clone());
                pending.push(include);
            }
        }
        imported.insert(source_path.clone(), headers);
    }
    Ok(imported)
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
    let current_source_map = CSourceContext::bundle(current_c_sources);
    let baseline_source_map = CSourceContext::bundle(baseline_c_sources);
    let current_parsed = parse_verified_sources_context(&current_file, &current_source_map)?;
    let baseline_parsed = parse_verified_sources_context(&baseline_file, &baseline_source_map)?;
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

    // Every file-level declaration a proof can depend on belongs here. A
    // function block that names one is byte-identical when only the
    // declaration changes, so nothing else would pull it back in: a weakened
    // `contract` would leave every caller reused and the run green while a
    // full verification of the same tree fails.
    let shared_environment_changed = current_file.predicate_definitions()
        != baseline_file.predicate_definitions()
        || current_file.click_function_definitions() != baseline_file.click_function_definitions()
        || current_file.resource_definitions() != baseline_file.resource_definitions()
        || current_file.theorem_definitions() != baseline_file.theorem_definitions()
        || current_file.contract_definitions() != baseline_file.contract_definitions()
        || current_file.algebraic_type_definitions() != baseline_file.algebraic_type_definitions();
    if shared_environment_changed {
        return Ok(C0IncrementalSelection {
            selected_functions: current_names.iter().cloned().collect(),
            reused_functions: Vec::new(),
            reasons: vec![
                "shared predicate, pure function, resource, theorem, contract, or algebraic type definitions changed"
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

    let current_imports = c0_imported_headers(&current_file, current_source_map.bundle_sources()?)?;
    let baseline_imports =
        c0_imported_headers(&baseline_file, baseline_source_map.bundle_sources()?)?;
    for source_path in &current_file.verifying_sources {
        let current_headers = current_imports.get(source_path).into_iter().flatten();
        let baseline_headers = baseline_imports.get(source_path).into_iter().flatten();
        let headers = current_headers
            .chain(baseline_headers)
            .cloned()
            .collect::<BTreeSet<_>>();
        let current_bundle = current_source_map.bundle_sources()?;
        let baseline_bundle = baseline_source_map.bundle_sources()?;
        let changed_headers = headers
            .into_iter()
            .filter(|header| {
                current_bundle.get(header.as_str()).copied()
                    != baseline_bundle.get(header.as_str()).copied()
            })
            .collect::<Vec<_>>();
        if changed_headers.is_empty() {
            continue;
        }
        for (name, (function_source, _)) in &current_parsed {
            if function_source == source_path {
                changed.insert(name.clone());
                reasons.push(format!(
                    "`{name}` imports changed local header(s): {}",
                    changed_headers.join(", ")
                ));
            }
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

pub fn verify_c0_prepared_sources_functions(
    click_source: &str,
    imports: &[PreparedCImport],
    functions: impl IntoIterator<Item = String>,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    let functions = functions.into_iter().collect::<BTreeSet<_>>();
    instrumentation::with_default_tactic_limits(|| {
        let sources = CSourceContext::prepared(imports);
        verify_c0_sources_with_context(
            click_source,
            &sources,
            Some(VerificationTarget::Functions(functions)),
            None,
            None,
        )
        .map(|(verified, _)| verified)
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

    /// Starts a reusable verification session over compiler-prepared inputs.
    /// The opaque artifacts are retained for all subsequent rewrite checks.
    pub fn new_prepared(
        click_source: &str,
        imports: &[PreparedCImport],
    ) -> Result<(Self, Vec<VerifiedCTheorem>), ClickError> {
        instrumentation::with_default_tactic_limits(|| {
            let sources = CSourceContext::prepared(imports);
            let (verified, verified_function_environment) =
                verify_c0_sources_with_context(click_source, &sources, None, None, None)?;
            let baseline_file = parse_c0_click_file_context(click_source, &sources)?;
            Ok((
                Self {
                    c_sources: Vec::new(),
                    prepared_imports: Some(imports.to_vec()),
                    baseline_file,
                    verified_function_environment,
                },
                verified,
            ))
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
                prepared_imports: None,
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

    /// Verifies a rewritten proof location against this prepared-input
    /// session, preserving the import identity across certification.
    pub fn verify_at_prepared(
        &self,
        click_source: &str,
        line: usize,
        column: usize,
    ) -> Result<Vec<VerifiedCTheorem>, ClickError> {
        let imports = self.prepared_imports.as_ref().ok_or_else(|| {
            ClickError::new("verification session does not contain prepared imports")
        })?;
        instrumentation::with_default_tactic_limits(|| {
            let sources = CSourceContext::prepared(imports);
            let target = verification_target_at_context(click_source, &sources, line, column)?;
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
            let rewritten_file = parse_c0_click_file_context(click_source, &sources)?;
            let baseline_interface =
                proof_unit_erased_click_file(self.baseline_file.clone(), &target);
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
                VerificationTarget::Theorem(_) | VerificationTarget::Functions(_) => None,
            };
            verify_c0_sources_with_context(
                click_source,
                &sources,
                Some(target),
                initial_environment,
                None,
            )
            .map(|(verified, _)| verified)
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

pub fn verify_c0_prepared_sources_at(
    click_source: &str,
    imports: &[PreparedCImport],
    line: usize,
    column: usize,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = CSourceContext::prepared(imports);
        let target = verification_target_at_context(click_source, &sources, line, column)?;
        verify_c0_sources_with_context(click_source, &sources, Some(target), None, None)
            .map(|(verified, _)| verified)
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
    expansion_capture: Option<&mut ExpansionCapture>,
) -> Result<(Vec<VerifiedCTheorem>, CExecutionEnvironment), ClickError> {
    let sources = CSourceContext::bundle(c_sources);
    verify_c0_sources_with_context(
        click_source,
        &sources,
        verification_target,
        initial_function_environment,
        expansion_capture,
    )
}

fn verify_c0_sources_with_context(
    click_source: &str,
    c_sources: &CSourceContext<'_>,
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
        let (
            struct_layouts,
            union_layouts,
            aggregate_objects,
            aggregate_array_objects,
            global_array_shapes,
            qualified_objects,
        ) = parse_c_layouts(click_source, c_sources)?;
        let file = parser::parse_with_layouts_and_aggregate_objects(
            click_source,
            struct_layouts,
            union_layouts,
            aggregate_objects,
            aggregate_array_objects,
            global_array_shapes,
            qualified_objects,
        )?;
        let parsed_sources = parse_verified_sources_context(&file, c_sources)?;
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
                Some(VerificationTarget::Theorem(theorem_name)) => {
                    let mut required = BTreeSet::new();
                    for function_name in contract_refinement_targets(&file, theorem_name) {
                        required.extend(verification_required_functions(
                            &file,
                            &parsed_sources,
                            &function_name,
                        )?);
                    }
                    Some(required)
                }
                None => None,
            }
        };
        check_verification_deadline()?;
        (file, parsed_sources, selected_functions)
    };
    check_verification_deadline()?;
    let external_and_user_function_blocks = combined_external_function_blocks(&file)?;
    let function_source_registry = Arc::new(FunctionSourceRegistry::from_function_blocks(
        &external_and_user_function_blocks,
    )?);
    let (mut termination_plans, mut requested_termination) =
        c_function_termination_plans(&file, selected_functions.as_ref())?;
    let standard_library_theorems = standard_library_theorem_definitions()?;
    let (
        predicate_environment,
        click_function_environment,
        resource_environment,
        mut function_environment,
        mut theorem_certification_facts,
        mut theorem_certification_authorities,
        theorem_environment,
    ) = {
        let _timing = VerificationTimingPhase::new("environment");
        let predicate_definitions = combined_predicate_definitions(&file)?;
        let click_function_definitions = combined_click_function_definitions(&file)?;
        let resource_definitions = combined_resource_definitions(&file)?;
        let theorem_definitions = selected_theorem_definitions(
            &file,
            selected_functions.as_ref(),
            verification_target.as_ref(),
        );
        let predicate_environment = PredicateEnvironment::new(&predicate_definitions)
            .with_contracts(file.contract_definitions());
        let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
            &click_function_definitions,
            &combined_algebraic_type_definitions(&file)?,
        );
        let resource_environment = ResourceEnvironment::new(&resource_definitions);
        // Frame evidence may look through composite definitions to decide
        // that a call's mutable ranges or a store's written cell cannot
        // touch a loaded pointer inside a composite's footprint. Definitions
        // are file-global, so one guard covers this verification; nothing is
        // published, so nested composites still require `observe(...)` before
        // a user's `separate(...)` goal can cite them.
        let built_function_environment = build_function_environment(
            &parsed_sources,
            &external_and_user_function_blocks,
            file.contract_definitions(),
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
            standard_library_theorems,
            &theorem_definitions,
            &predicate_environment,
            &click_function_environment,
            Some(&function_environment),
            &resource_environment,
            function_source_registry.clone(),
        )?;
        let mut theorem_certification_facts = BTreeMap::<String, Vec<Proposition>>::new();
        let mut theorem_certification_authorities =
            BTreeMap::<String, Vec<CVerifiedPureTheorem>>::new();
        record_theorem_certification_authority(
            &verified_theorems,
            &mut theorem_certification_facts,
            &mut theorem_certification_authorities,
        );
        let theorem_environment = TheoremEnvironment::new(
            &standard_library_theorems
                .iter()
                .chain(&theorem_definitions)
                .cloned()
                .collect::<Vec<_>>(),
        );
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
    // Standard-library theorems already checked for their certification
    // authority during this verification; see the certification loop below.
    let mut checked_standard_library_theorems = BTreeSet::<String>::new();

    for function_block in file.function_blocks {
        check_verification_deadline()?;
        // Load-variable origins are first-seen per verified function: an
        // origin minted while verifying an earlier function belongs to a
        // memory DAG this function's effect snapshots never connect to.
        crate::kernel::begin_load_origin_epoch();
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
        let (_, source_path, parsed_function) =
            parsed_function_for_source_name(&parsed_sources, function_block.signature.name())?
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
            function_source_registry.clone(),
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
            borrowed: false,
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
                    function_source_registry.clone(),
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
                    function_source_registry.clone(),
                    tactics,
                )?,
                SourceProof::Default | SourceProof::Tactic(SmartTactic::Simp) => {
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
                            function_source_registry.clone(),
                        )?
                    }
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
                        function_source_registry.clone(),
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
                        function_source_registry.clone(),
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
        // The checked C transition certificate does not retain pure
        // theorem-application bookkeeping. Select those authorities from the
        // exact source proofs as well as any retained checked tactics.
        collect_function_theorem_dependencies(&function_block, &mut certification_theorems);
        for verified in &function_verified {
            if let Some(tactics) = &verified.proof_tactics {
                collect_applied_theorems(tactics, &mut certification_theorems);
            }
        }
        let mut certification_pure_theorems = Vec::new();
        for theorem_name in certification_theorems {
            // A cited standard-library theorem is a dependency: the proof
            // used its declaration without re-proving it. The kernel accepts
            // a pure theorem into certification only with authority from a
            // checked proof, so check just this cited theorem, once, against
            // the library declarations before it.
            if !theorem_certification_facts.contains_key(&theorem_name)
                && checked_standard_library_theorems.insert(theorem_name.clone())
                && let Some(index) = standard_library_theorem_index(&theorem_name)
                && theorem_has_certification_binders(&standard_library_theorems[index])
            {
                let verified_dependency = verify_theorem_definitions(
                    &standard_library_theorems[..index],
                    &standard_library_theorems[index..=index],
                    &predicate_environment,
                    &click_function_environment,
                    None,
                    &resource_environment,
                    function_source_registry.clone(),
                )?;
                record_theorem_certification_authority(
                    &verified_dependency,
                    &mut theorem_certification_facts,
                    &mut theorem_certification_authorities,
                );
            }
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
        )?;
        if contract_function.resource_derived_mutable_frame() {
            let loop_assumptions = assumptions_from_propositions(&certification_facts);
            let mut loop_budget = crate::kernel::ExecutionBudget::default();
            let Some(loop_entry_state) = crate::kernel::c_function_entry_state(
                &certification_state,
                &contract_function,
                &certification_arguments,
            ) else {
                return Err(ClickError::new(format!(
                    "could not construct the resource-derived loop entry for `{}`",
                    function_block.signature.name()
                )));
            };
            match crate::kernel::validate_resource_derived_loop_frames(
                &contract_function,
                &loop_entry_state,
                &loop_assumptions,
                &mut loop_budget,
            ) {
                Ok(Ok(())) => {}
                Ok(Err(message)) => {
                    return Err(ClickError::new(format!(
                        "could not validate resource-derived loop frames for `{}`: {message}",
                        function_block.signature.name()
                    )));
                }
                Err(limit) => {
                    return Err(ClickError::new(format!(
                        "resource-derived loop-frame validation for `{}` exceeded its execution budget: {limit:?}",
                        function_block.signature.name()
                    )));
                }
            }
        }
        // A resource-bearing contract without an effect clause frames caller
        // memory through the resource transition at each store, but file-scope
        // and static storage is not external memory: its writes must lie inside
        // the owned footprint (startup resources, owned ranges, and composite
        // bodies). Otherwise a view, or ownership of a neighboring cell, would
        // authorize a store into storage the contract does not own.
        if !contract_function.contract_mutable().is_empty()
            || !contract_function.resource_requires().is_empty()
            || contract_function.resource_derived_mutable_frame()
        {
            let Some(storage_entry_state) = crate::kernel::c_function_entry_state(
                &certification_state,
                &contract_function,
                &certification_arguments,
            ) else {
                return Err(ClickError::new(format!(
                    "could not construct the storage-check entry for `{}`",
                    function_block.signature.name()
                )));
            };
            for verified in &function_verified {
                for (path_index, path) in verified.checked_execution.paths().iter().enumerate() {
                    let Proposition::CFunctionVerifies { outcome, .. } =
                        implication_body(path.theorem().proposition())
                    else {
                        return Err(ClickError::new(format!(
                            "could not check storage writes for `{}`: checked path has no function outcome",
                            function_block.signature.name()
                        )));
                    };
                    if !matches!(outcome, CFunctionOutcome::Return { .. }) {
                        continue;
                    }
                    let mut available_pure_facts = certification_facts.clone();
                    available_pure_facts
                        .extend(path.facts().iter().map(|fact| fact.proposition().clone()));
                    let assumptions = assumptions_from_propositions(&available_pure_facts);
                    let storage_pointer = |pointer: &crate::kernel::Pointer| {
                        pointer.block.starts_with("global:") || pointer.block.starts_with("static:")
                    };
                    let has_storage_effect = crate::kernel::memory_effect_write_pointers(
                        path.effect_facts(),
                    )
                    .iter()
                    .any(storage_pointer)
                        || path.effect_facts().iter().any(|fact| {
                            matches!(
                                fact.proposition(),
                                Proposition::CMemoryEffectSummary { mutable_ranges, .. }
                                    if mutable_ranges.iter().any(|range| storage_pointer(range.base()))
                            )
                        });
                    let checked_transition = if has_storage_effect
                        && contract_function.resource_derived_mutable_frame()
                    {
                        let mut transition_budget = crate::kernel::ExecutionBudget::default();
                        match crate::kernel::evaluate_function_resource_context_with_metadata(
                            &storage_entry_state,
                            contract_function.resource_requires(),
                            contract_function.composite_resource_definitions(),
                            &assumptions,
                            &mut transition_budget,
                        ) {
                            Ok(Ok((_, checked))) => Some(checked),
                            Ok(Err(error)) => {
                                return Err(ClickError::new(format!(
                                    "`{}` path {path_index}: could not evaluate the checked resource transition: {error:?}",
                                    function_block.signature.name()
                                )));
                            }
                            Err(limit) => {
                                return Err(ClickError::new(format!(
                                    "`{}` path {path_index}: checked resource transition exceeded its execution budget: {limit:?}",
                                    function_block.signature.name()
                                )));
                            }
                        }
                    } else {
                        None
                    };
                    match crate::kernel::storage_writes_outside_owned_footprint(
                        &contract_function,
                        &storage_entry_state,
                        path.effect_facts(),
                        &assumptions,
                        checked_transition.as_deref(),
                    ) {
                        Ok(Some(outside)) if outside.is_empty() => {}
                        Ok(Some(outside)) => {
                            return Err(ClickError::new(format!(
                                "`{}` path {path_index}: write to storage outside the owned footprint: {}; own the written cells or declare them in a `mutable` clause",
                                function_block.signature.name(),
                                outside.join(", ")
                            )));
                        }
                        Ok(None) => {
                            return Err(ClickError::new(format!(
                                "`{}` path {path_index}: could not evaluate the owned footprint to check its storage writes",
                                function_block.signature.name()
                            )));
                        }
                        Err(error) => {
                            return Err(ClickError::new(format!(
                                "`{}` path {path_index}: storage write check failed: {error:?}",
                                function_block.signature.name()
                            )));
                        }
                    }
                }
            }
        }
        // An omitted function-level effect clause is an empty footprint. The
        // Check the same write-footprint obligation here so a violation is
        // reported at the write that crossed the boundary, like an explicit
        // `immutable` clause. Resource-derived frames are checked by their
        // resource transition and, for storage, by the owned-footprint check
        // above; they intentionally do not enter this path.
        if contract_function.contract_mutable().is_empty()
            && !contract_function.resource_derived_mutable_frame()
        {
            if function_verified.is_empty() {
                return Err(ClickError::new(format!(
                    "could not check implicit empty effect for `{}`: no checked execution",
                    function_block.signature.name()
                )));
            }
            for verified in &function_verified {
                for (path_index, path) in verified.checked_execution.paths().iter().enumerate() {
                    let Proposition::CFunctionVerifies { outcome, .. } =
                        implication_body(path.theorem().proposition())
                    else {
                        return Err(ClickError::new(format!(
                            "could not check implicit empty effect for `{}`: checked path has no function outcome",
                            function_block.signature.name()
                        )));
                    };
                    // A path that does not return has no caller-visible
                    // post-state to frame. Preserve the existing
                    // partial-correctness treatment for divergent paths;
                    // returning paths still have to prove the omitted
                    // footprint is empty.
                    if !matches!(outcome, CFunctionOutcome::Return { .. }) {
                        continue;
                    }
                    let mut available_pure_facts = certification_facts.clone();
                    available_pure_facts
                        .extend(path.facts().iter().map(|fact| fact.proposition().clone()));
                    prove_empty_write_footprint(
                        &format!("{}.implicit_effect", function_block.signature.name()),
                        path_index,
                        path.effect_facts(),
                        &available_pure_facts,
                        parsed_function.parameters(),
                        &certification_arguments,
                        &certification_state,
                        outcome,
                    )?;
                }
            }
        }
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
                    let CodeRegion::Loop(loop_index) = clause.region() else {
                        continue;
                    };
                    let Some(expressions) = loop_termination_measure(
                        clause,
                        &format!(
                            "frontier-local loop {loop_index} `decreases` in `{}`",
                            function_block.signature.name()
                        ),
                    )?
                    else {
                        continue;
                    };
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
            if !contract_function.is_program_entry() {
                let rule = c_verified_function_rule(contract_function, &certified_claims)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "could not package verified contract for `{}`",
                            function_block.signature.name()
                        ))
                    })?;
                function_environment = function_environment.with_verified_function_rule(rule);
            }
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

    if c_sources.imports.is_some() {
        for theorem in &mut verified {
            theorem.import_identity = c_sources.prepared_project_identity.clone();
        }
    }
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
    }
    .ok_or_else(|| {
        ClickError::new(format!(
            "selected {claim:?} proof for `{function_name}` is not an explicit tactic script"
        ))
    })?;
    let Some((kernel_name, _, _)) =
        parsed_function_for_source_name(parsed_sources, &function_name)?
    else {
        return Err(ClickError::new(format!(
            "no C source defines `{function_name}`"
        )));
    };
    let mut required = BTreeSet::new();
    // Expansion is defined only for an already-correct complete proof unit.
    // Capturing some post-execution tactics also legitimately continues past
    // their source location before the surface certificate is complete. Load
    // every callee of the selected function so capture and final rewritten
    // verification use the same dependency closure. Unrelated functions are
    // still excluded by this targeted traversal.
    let mut pending = vec![kernel_name.clone()];
    while let Some(dependency) = pending.pop() {
        if !required.insert(dependency.clone()) {
            continue;
        }
        if let Some((_, parsed)) = parsed_sources.get(&dependency) {
            pending.extend(c0_statement_calls(parsed).into_iter().flatten());
        }
    }
    required.insert(function_name);
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
    let source_map = CSourceContext::bundle(c_sources);
    let file = parse_c0_click_file(click_source, c_sources)?;
    let parsed_sources = parse_verified_sources_context(&file, &source_map)?;
    let required = tactic_expansion_required_functions(
        &file,
        &parsed_sources,
        (site.clone(), Some(tactic_index)),
    )?;
    if required.len() <= 1 {
        return Ok(None);
    }

    let root_kernel_name = parsed_function_for_source_name(&parsed_sources, function_name)?
        .map(|(kernel_name, _, _)| kernel_name.clone())
        .ok_or_else(|| ClickError::new(format!("no C source defines `{function_name}`")))?;
    let mut paths = BTreeMap::from([(root_kernel_name.clone(), vec![function_name.clone()])]);
    let mut pending = vec![root_kernel_name];
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
    let mut pending = if let Some((kernel_name, _, _)) =
        parsed_function_for_source_name(parsed_sources, function_name)?
    {
        vec![kernel_name.clone()]
    } else if function_blocks
        .iter()
        .any(|function| function.is_external() && function.signature().name() == function_name)
    {
        vec![function_name.to_string()]
    } else {
        return Err(ClickError::new(format!(
            "no C source defines `{function_name}`"
        )));
    };
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
    required.insert(function_name.to_string());
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
    let sources = CSourceContext::bundle(c_sources);
    c0_external_dependencies_context(click_source, &sources)
}

/// Reports the same explicit external-contract assumptions for compiler imports.
pub fn c0_prepared_external_dependencies(
    click_source: &str,
    imports: &[PreparedCImport],
) -> Result<BTreeMap<String, Vec<String>>, ClickError> {
    let sources = CSourceContext::prepared(imports);
    c0_external_dependencies_context(click_source, &sources)
}

fn c0_external_dependencies_context(
    click_source: &str,
    sources: &CSourceContext<'_>,
) -> Result<BTreeMap<String, Vec<String>>, ClickError> {
    let (
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
    ) = parse_c_layouts(click_source, sources)?;
    let file = parser::parse_with_layouts_and_aggregate_objects(
        click_source,
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
    )?;
    let parsed_sources = parse_verified_sources_context(&file, sources)?;
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

fn is_c0_builtin_function(name: &str) -> bool {
    matches!(name, "malloc" | "calloc" | "realloc" | "free")
}

pub(in crate::surface) fn c0_statement_calls(
    function: &syntax::C0Function,
) -> Vec<BTreeSet<String>> {
    fn collect_function_pointer_names(
        statement: &syntax::C0Statement,
        names: &mut BTreeSet<String>,
    ) {
        match statement {
            syntax::C0Statement::Declare {
                c_type: syntax::C0Type::FunctionPointer(_),
                name,
                ..
            } => {
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
            | syntax::C0Statement::SequentialStore { .. }
            | syntax::C0Statement::AggregateCopy { .. }
            | syntax::C0Statement::Update { .. }
            | syntax::C0Statement::Assert { .. } => {}
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
            syntax::C0Expression::StatementExpression { value, .. } => {
                collect_function_addresses(value, names);
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
            | syntax::C0Expression::CheckedArrayIndex {
                index: expression, ..
            }
            | syntax::C0Expression::Not(expression)
            | syntax::C0Expression::BitwiseNot(expression)
            | syntax::C0Expression::Load(expression)
            | syntax::C0Expression::SequentialRead {
                target: expression, ..
            } => {
                collect_function_addresses(expression, names);
            }
            syntax::C0Expression::SequentialWrite { target, value, .. } => {
                collect_function_addresses(target, names);
                collect_function_addresses(value, names);
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
                if !function_pointer_names.contains(function_name)
                    && !is_c0_builtin_function(function_name)
                {
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
                if !function_pointer_names.contains(function_name)
                    && !is_c0_builtin_function(function_name)
                {
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
            syntax::C0Statement::SequentialStore { target, value, .. } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(target, &mut dependencies);
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
            syntax::C0Statement::Assert { condition, .. } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(condition, &mut dependencies);
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
        ContractExpression::Binding(name)
        | ContractExpression::CFragment(CExpression::Variable(name))
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

/// The bare source name a one-component `decreases` clause spells, if any.
fn termination_measure_binder_name(measure: &TerminationMeasure) -> Option<&str> {
    let [component] = measure.components() else {
        return None;
    };
    match component {
        ContractExpression::Binding(name)
        | ContractExpression::CBinding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) => Some(name),
        _ => None,
    }
}

/// Classifies one loop's `decreases` clause (D6).
///
/// The clause is one expression, and a loop's own `owns name: resource(args);`
/// binders are the names that make it a structural measure; anything else is
/// the existing int32 ranking measure. The decision reads this loop's own
/// declarations, so it costs the clause and the loop header.
pub(in crate::surface) fn loop_termination_measure(
    clause: &StructuralClause,
    context: &str,
) -> Result<Option<crate::kernel::CLoopTerminationMeasure>, ClickError> {
    let Some(measure) = clause.decreases() else {
        return Ok(None);
    };
    if let Some(name) = termination_measure_binder_name(measure)
        && clause.resources().iter().any(|resource| {
            matches!(resource, ResourceClause::Named { binding, .. } if binding.name == name)
        })
    {
        return Ok(Some(crate::kernel::CLoopTerminationMeasure::Structural(
            name.to_string(),
        )));
    }
    Ok(Some(crate::kernel::CLoopTerminationMeasure::Ranking(
        termination_measure_expressions(measure, context)?,
    )))
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
                CFunctionDecrease::Unresolved(_) => Err(ClickError::new(format!(
                    "function-level `decreases` in `{}` was never classified; declared-resource expansion did not run",
                    function.signature().name()
                ))),
                CFunctionDecrease::Binder(binder) => {
                    // `decreases t;` names one of this contract's own resource
                    // binders. The kernel measure is an index into the entry
                    // resource requirements, so find the clause that declares
                    // the binder and count the resource requirements before it.
                    let mut resource_index = 0;
                    let mut matched = None;
                    for requirement in function.requires() {
                        let Requirement::Resource(required) = requirement.inner() else {
                            continue;
                        };
                        if matches!(
                            required,
                            ResourceClause::Named { binding, .. } if &binding.name == binder
                        ) {
                            matched = Some(resource_index);
                            break;
                        }
                        resource_index += 1;
                    }
                    let index = matched.ok_or_else(|| {
                        ClickError::new(format!(
                            "function-level `decreases {binder}` in `{}` must name an owned or viewed entry resource binder",
                            function.signature().name()
                        ))
                    })?;
                    Ok(crate::kernel::CFunctionTerminationMeasure::ResourceRequirement(index))
                }
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
                            "function-level `decreases` in `{}` must name one composite resource",
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
                            "function-level `decreases {measure_name}(...)` in `{}` must exactly match an owned or viewed entry resource",
                            function.signature().name()
                        ))
                    })?;
                    Ok(crate::kernel::CFunctionTerminationMeasure::ResourceRequirement(index))
                }
            })
            .transpose()?;
        let mut loop_measures = BTreeMap::new();
        for clause in function.structural_clauses() {
            if clause.decreases().is_none() {
                continue;
            }
            let CodeRegion::Loop(index) = clause.region() else {
                return Err(ClickError::new(format!(
                    "`decreases` is supported only for loop regions, not {:?} in `{}`",
                    clause.region(),
                    function.signature().name()
                )));
            };
            let Some(expressions) = loop_termination_measure(
                clause,
                &format!(
                    "loop {index} `decreases` in `{}`",
                    function.signature().name()
                ),
            )?
            else {
                continue;
            };
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
                if let Some(expressions) = loop_termination_measure(
                    clause,
                    &format!(
                        "loop {index} `decreases` in `{}`",
                        function.signature().name()
                    ),
                )? && loop_measures.insert(index, expressions).is_some()
                {
                    return Err(ClickError::new(format!(
                        "duplicate `decreases` measure for loop {index} in `{}`",
                        function.signature().name()
                    )));
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

fn parse_c_source_unit(
    source_path: &str,
    c_sources: &CSourceContext<'_>,
) -> Result<syntax::C0TranslationUnit, ClickError> {
    if let Some(unit) = c_sources.parsed_units.borrow().get(source_path) {
        return Ok((**unit).clone());
    }
    let unit = if let Some(bundle) = &c_sources.bundle {
        let expanded =
            crate::languages::c::source::expand_includes(source_path, bundle).map_err(|error| {
                ClickError::new(format!(
                    "failed to resolve includes for C source `{source_path}`: {error}"
                ))
            })?;
        for header_path in expanded.dependencies() {
            let header = crate::languages::c::source::expand_includes(header_path, bundle)
                .map_err(|error| {
                    ClickError::new(format!(
                        "failed to resolve includes for C header `{header_path}`: {error}"
                    ))
                })?;
            syntax::validate_header(header.source(), header.line_map()).map_err(|error| {
                ClickError::new(format!("failed to parse C header `{header_path}`: {error}"))
            })?;
        }
        syntax::parse_translation_unit_for_source(
            expanded.source(),
            source_path,
            expanded.line_map(),
        )
        .map_err(|error| {
            ClickError::new(format!("failed to parse C source `{source_path}`: {error}"))
        })?
    } else {
        #[cfg(test)]
        c_sources
            .prepared_parse_count
            .set(c_sources.prepared_parse_count.get() + 1);
        let import = c_sources
            .prepared_by_source
            .as_ref()
            .and_then(|imports| imports.get(source_path).copied())
            .ok_or_else(|| {
                ClickError::new(format!(
                    "import configuration has no prepared translation unit for verifying source `{source_path}`"
                ))
            })?;
        syntax::parse_translation_unit_for_import(
            import.source(),
            import.logical_source(),
            import.source_map(),
        )
        .map_err(|error| {
            ClickError::new(format!(
                "failed to parse compiler-prepared C source `{source_path}`: {error}"
            ))
        })?
    };
    c_sources
        .parsed_units
        .borrow_mut()
        .insert(source_path.to_string(), Arc::new(unit.clone()));
    Ok(unit)
}

/// Looks up a C definition using the spelling visible to Click. Header-local
/// inline bodies have a translation-unit-qualified kernel name, so sidecar
/// contracts must match `C0Function::source_name()` rather than the execution
/// identity returned by `C0Function::name()`.
fn parsed_function_for_source_name<'a>(
    parsed_sources: &'a BTreeMap<String, (String, syntax::C0Function)>,
    source_name: &str,
) -> Result<Option<(&'a String, &'a String, &'a syntax::C0Function)>, ClickError> {
    let mut matches = parsed_sources
        .iter()
        .filter(|(_, (_, function))| function.source_name() == source_name)
        .map(|(kernel_name, (source_path, function))| (kernel_name, source_path, function));
    let Some(first) = matches.next() else {
        return Ok(None);
    };
    if matches.next().is_some() {
        return Err(ClickError::new(format!(
            "source-named inline function `{source_name}` has multiple translation-unit-local definitions"
        )));
    }
    Ok(Some(first))
}

pub(in crate::surface) fn parse_c_layouts(
    click_source: &str,
    c_sources: &CSourceContext<'_>,
) -> Result<
    (
        BTreeMap<String, syntax::C0StructLayout>,
        BTreeMap<String, syntax::C0UnionLayout>,
        BTreeMap<String, BTreeMap<String, String>>,
        BTreeMap<String, BTreeSet<String>>,
        BTreeMap<String, BTreeMap<String, parser::GlobalArrayShape>>,
        BTreeMap<String, BTreeMap<String, parser::QualifiedCObject>>,
    ),
    ClickError,
> {
    let mut layouts = BTreeMap::new();
    let mut union_layouts = BTreeMap::new();
    let mut aggregate_objects = BTreeMap::new();
    let mut aggregate_array_objects = BTreeMap::new();
    let mut global_array_shapes = BTreeMap::new();
    let mut qualified_objects = BTreeMap::new();
    let verifying_paths = super::verifying_source_paths(click_source)?;
    if let Some(imports) = c_sources.imports {
        if c_sources.prepared_duplicates {
            return Err(ClickError::new(
                "prepared imports contain duplicate logical translation-unit sources",
            ));
        }
        let expected = verifying_paths.iter().cloned().collect::<BTreeSet<_>>();
        let actual = imports
            .iter()
            .map(|import| import.logical_source().to_string())
            .collect::<BTreeSet<_>>();
        if expected != actual {
            return Err(ClickError::new(format!(
                "prepared import logical sources must exactly match verifying clauses (expected {}, received {})",
                expected.iter().cloned().collect::<Vec<_>>().join(", "),
                actual.iter().cloned().collect::<Vec<_>>().join(", "),
            )));
        }
    }
    for source_path in verifying_paths {
        let unit = parse_c_source_unit(&source_path, c_sources)?;
        let mut objects = BTreeMap::new();
        for (name, global) in &unit.globals {
            if let Some(pointer_type) = global.c_type().pointer_type() {
                let pointer = CMemory::global_pointer(global.kernel_name());
                let value_type = global.c_type().to_kernel_type();
                let mut value = if value_type.is_object_pointer() {
                    crate::kernel::stable_symbolic_pointer_cell_value(&pointer, value_type)
                } else {
                    CValue::typed_pointer(pointer.clone(), pointer_type.to_kernel_type())
                };
                value = value
                    .with_pointer_pointee_constant(global.is_constant())
                    .with_pointer_pointee_volatile(global.pointee_is_volatile());
                let expression = if value_type.is_object_pointer() {
                    CExpression::Value(value)
                } else {
                    CExpression::TypedLoad {
                        pointer: Box::new(CExpression::Value(value)),
                        value_type,
                        volatile: false,
                    }
                };
                objects.insert(
                    name.clone(),
                    parser::QualifiedCObject {
                        expression,
                        address: Some(CExpression::Value(CValue::typed_pointer(
                            CMemory::global_pointer(global.kernel_name()),
                            pointer_type.to_kernel_type(),
                        ))),
                        struct_name: global.struct_name().map(str::to_owned),
                        array_shape: None,
                        ambiguous: false,
                    },
                );
            }
        }
        for (name, array) in &unit.global_arrays {
            if let Some(pointer_type) = array.element_type().pointer_type() {
                objects.insert(
                    name.clone(),
                    parser::QualifiedCObject {
                        expression: CExpression::Value(
                            CValue::typed_pointer_with_pointee_constant(
                                CMemory::global_pointer(array.kernel_name()),
                                pointer_type.to_kernel_type(),
                                array.is_constant(),
                            ),
                        ),
                        address: None,
                        struct_name: None,
                        array_shape: array.index_shape(),
                        ambiguous: false,
                    },
                );
            }
        }
        for (name, aggregate) in &unit.global_aggregates {
            objects.insert(
                name.clone(),
                parser::QualifiedCObject {
                    expression: CExpression::Value(CValue::typed_pointer_with_pointee_constant(
                        CMemory::global_pointer(aggregate.kernel_name()),
                        CType::Int32Pointer,
                        aggregate.is_constant(),
                    )),
                    address: None,
                    struct_name: Some(aggregate.struct_name().to_owned()),
                    array_shape: None,
                    ambiguous: false,
                },
            );
        }
        for (name, aggregate_array) in &unit.global_aggregate_arrays {
            if let Some(length) = aggregate_array.array_length() {
                objects.insert(
                    name.clone(),
                    parser::QualifiedCObject {
                        expression: CExpression::Value(
                            CValue::typed_pointer_with_pointee_constant(
                                CMemory::global_pointer(aggregate_array.kernel_name()),
                                CType::Int32Pointer,
                                aggregate_array.is_constant(),
                            ),
                        ),
                        address: None,
                        struct_name: Some(aggregate_array.struct_name().to_owned()),
                        array_shape: Some(vec![length]),
                        ambiguous: false,
                    },
                );
            }
        }
        for function in &unit.functions {
            let mut names = BTreeMap::<&str, usize>::new();
            for name in function
                .static_locals()
                .values()
                .map(|object| object.name())
                .chain(
                    function
                        .static_arrays()
                        .values()
                        .map(|object| object.name()),
                )
                .chain(
                    function
                        .static_aggregates()
                        .values()
                        .map(|object| object.name()),
                )
                .chain(
                    function
                        .static_aggregate_arrays()
                        .values()
                        .map(|object| object.name()),
                )
            {
                *names.entry(name).or_default() += 1;
            }
            for local in function.static_locals().values() {
                if let Some(pointer_type) = local.c_type().pointer_type() {
                    let pointer = CMemory::static_pointer(function.name(), local.kernel_name());
                    let value_type = local.c_type().to_kernel_type();
                    let mut value = if value_type.is_object_pointer() {
                        crate::kernel::stable_symbolic_pointer_cell_value(&pointer, value_type)
                    } else {
                        CValue::typed_pointer(pointer.clone(), pointer_type.to_kernel_type())
                    };
                    value = value
                        .with_pointer_pointee_constant(local.is_constant())
                        .with_pointer_pointee_volatile(local.pointee_is_volatile());
                    let expression = if value_type.is_object_pointer() {
                        CExpression::Value(value)
                    } else {
                        CExpression::TypedLoad {
                            pointer: Box::new(CExpression::Value(value)),
                            value_type,
                            volatile: false,
                        }
                    };
                    objects.insert(
                        format!("{}::{}", function.name(), local.name()),
                        parser::QualifiedCObject {
                            expression,
                            address: Some(CExpression::Value(CValue::typed_pointer(
                                CMemory::static_pointer(function.name(), local.kernel_name()),
                                pointer_type.to_kernel_type(),
                            ))),
                            struct_name: None,
                            array_shape: None,
                            ambiguous: names[local.name()] > 1,
                        },
                    );
                }
            }
            for array in function.static_arrays().values() {
                if let Some(pointer_type) = array.element_type().pointer_type() {
                    objects.insert(
                        format!("{}::{}", function.name(), array.name()),
                        parser::QualifiedCObject {
                            expression: CExpression::Value(
                                CValue::typed_pointer_with_pointee_constant(
                                    CMemory::static_pointer(function.name(), array.kernel_name()),
                                    pointer_type.to_kernel_type(),
                                    array.is_constant(),
                                ),
                            ),
                            address: None,
                            struct_name: None,
                            array_shape: Some(array.shape().to_vec()),
                            ambiguous: names[array.name()] > 1,
                        },
                    );
                }
            }
            for aggregate in function.static_aggregates().values() {
                objects.insert(
                    format!("{}::{}", function.name(), aggregate.name()),
                    parser::QualifiedCObject {
                        expression: CExpression::Value(
                            CValue::typed_pointer_with_pointee_constant(
                                CMemory::static_pointer(function.name(), aggregate.kernel_name()),
                                CType::Int32Pointer,
                                aggregate.is_constant(),
                            ),
                        ),
                        address: None,
                        struct_name: Some(aggregate.struct_name().to_owned()),
                        array_shape: None,
                        ambiguous: names[aggregate.name()] > 1,
                    },
                );
            }
            for aggregate_array in function.static_aggregate_arrays().values() {
                objects.insert(
                    format!("{}::{}", function.name(), aggregate_array.name()),
                    parser::QualifiedCObject {
                        expression: CExpression::Value(
                            CValue::typed_pointer_with_pointee_constant(
                                CMemory::static_pointer(
                                    function.name(),
                                    aggregate_array.kernel_name(),
                                ),
                                CType::Int32Pointer,
                                aggregate_array.is_constant(),
                            ),
                        ),
                        address: None,
                        struct_name: Some(aggregate_array.struct_name().to_owned()),
                        array_shape: Some(vec![aggregate_array.length()]),
                        ambiguous: false,
                    },
                );
            }
        }
        qualified_objects.insert(source_path.clone(), objects);
        for (name, layout) in &unit.structs {
            if let Some(previous) = layouts.insert(name.clone(), layout.clone())
                && previous != *layout
            {
                return Err(ClickError::new(format!(
                    "conflicting declarations for struct `{name}`"
                )));
            }
        }
        for (name, layout) in &unit.unions {
            if let Some(previous) = union_layouts.insert(name.clone(), layout.clone())
                && previous != *layout
            {
                return Err(ClickError::new(format!(
                    "conflicting declarations for union `{name}`"
                )));
            }
        }
        for function in unit.functions {
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
            let function_global_array_shapes = function
                .global_arrays()
                .iter()
                .filter_map(|(name, array)| {
                    array.index_shape().map(|shape| {
                        (
                            name.clone(),
                            parser::GlobalArrayShape {
                                shape,
                                element_type: array.element_type().to_kernel_type(),
                            },
                        )
                    })
                })
                .chain(function.static_arrays().values().map(|array| {
                    (
                        array.name().to_string(),
                        parser::GlobalArrayShape {
                            shape: array.shape().to_vec(),
                            element_type: array.element_type().to_kernel_type(),
                        },
                    )
                }))
                .collect();
            global_array_shapes.insert(function.name().to_string(), function_global_array_shapes);
        }
    }
    Ok((
        layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
    ))
}

#[cfg(test)]
pub(in crate::surface) fn parse_verified_sources(
    file: &ClickFile,
    c_sources: &BTreeMap<&str, &str>,
) -> Result<BTreeMap<String, (String, syntax::C0Function)>, ClickError> {
    let context = CSourceContext {
        bundle: Some(c_sources.clone()),
        imports: None,
        prepared_by_source: None,
        prepared_project_identity: None,
        prepared_duplicates: false,
        parsed_units: RefCell::new(BTreeMap::new()),
        #[cfg(test)]
        prepared_parse_count: Cell::new(0),
    };
    parse_verified_sources_context(file, &context)
}

pub(in crate::surface) fn parse_verified_sources_context(
    file: &ClickFile,
    c_sources: &CSourceContext<'_>,
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
    let mut units = BTreeMap::new();
    for source_path in &file.verifying_sources {
        let mut unit = parse_c_source_unit(source_path, c_sources)?;
        for function in std::mem::take(&mut unit.functions) {
            let function_name = function.name().to_string();
            let previous = parsed.insert(function_name.clone(), (source_path.clone(), function));
            if previous.is_some() {
                return Err(ClickError::new(format!(
                    "more than one `verifying` source defines function `{function_name}`"
                )));
            }
        }
        units.insert(source_path.clone(), unit);
    }

    // Check C source compatibility before kernel lowering erases distinctions
    // such as plain char versus unsigned char. Retain declarations once per
    // translation unit, including prototypes in files without a definition.
    let mut function_declarations = BTreeMap::<&str, (&str, &syntax::C0FunctionHeader)>::new();
    for (source_path, unit) in &units {
        for declaration in unit.function_declarations.values() {
            let name = declaration.linkage_name();
            if let Some((previous_source, previous)) = function_declarations.get(name) {
                if !previous.compatible_with(declaration) {
                    return Err(ClickError::new(format!(
                        "conflicting C function declarations for `{name}` in `{previous_source}` and `{source_path}`"
                    )));
                }
            } else {
                function_declarations.insert(name, (source_path, declaration));
            }
        }
    }

    // Link declarations once per translation unit, including data-only files.
    // Every kernel function receives the same externally linked global layout.
    // File-scope `static` declarations stay in their own
    // translation unit and are linked below only into that unit's functions.
    let mut globals_by_source = BTreeMap::<String, BTreeMap<String, syntax::C0Global>>::new();
    for (source_path, unit) in &units {
        let source_globals = globals_by_source.entry(source_path.clone()).or_default();
        for (name, global) in &unit.globals {
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
                Some(previous)
                    if previous.is_initialized_definition()
                        && global.is_initialized_definition() =>
                {
                    if previous != global {
                        return Err(ClickError::new(format!(
                            "conflicting definitions for global `{name}` in `{source_path}`"
                        )));
                    }
                }
                _ => {
                    let merged = match source_globals.get(name) {
                        Some(previous) if previous.is_initialized_definition() => previous.clone(),
                        Some(_) if global.is_initialized_definition() => global.clone(),
                        Some(previous) if previous.is_tentative() => previous.clone(),
                        None => global.clone(),
                        Some(_) => global.clone(),
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
                Some(previous)
                    if previous.is_initialized_definition()
                        && global.is_initialized_definition() =>
                {
                    return Err(ClickError::new(format!(
                        "multiple definitions of global `{name}`"
                    )));
                }
                _ => {
                    let merged = match globals.get(name) {
                        Some(previous) if previous.is_initialized_definition() => previous.clone(),
                        Some(_) if global.is_initialized_definition() => global.clone(),
                        Some(previous) if previous.is_tentative() => previous.clone(),
                        None => global.clone(),
                        Some(_) => global.clone(),
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
    for (source_path, unit) in &units {
        let source_arrays = global_arrays_by_source
            .entry(source_path.clone())
            .or_default();
        for (name, array) in &unit.global_arrays {
            if globals_by_source
                .get(source_path)
                .is_some_and(|source_globals| source_globals.contains_key(name))
            {
                return Err(ClickError::new(format!(
                    "global `{name}` conflicts with a scalar global declaration"
                )));
            }
            match source_arrays.get(name) {
                Some(previous)
                    if previous.element_type() != array.element_type()
                        || !syntax::array_shapes_compatible(previous, array) =>
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for global array `{name}`"
                    )));
                }
                Some(previous)
                    if previous.is_initialized_definition()
                        && array.is_initialized_definition() =>
                {
                    if previous != array {
                        return Err(ClickError::new(format!(
                            "conflicting definitions for global array `{name}` in `{source_path}`"
                        )));
                    }
                }
                _ => {
                    let merged = syntax::merge_global_array_declarations(
                        source_arrays.get(name),
                        array.clone(),
                    );
                    source_arrays.insert(name.clone(), merged);
                }
            }
        }
    }
    for (source_path, source_arrays) in &global_arrays_by_source {
        if let Some((name, _)) = source_arrays
            .iter()
            .find(|(_, array)| array.is_file_static() && !array.is_defined())
        {
            return Err(ClickError::new(format!(
                "file-scope static array `{name}` has an incomplete tentative definition but no complete definition in `{source_path}`"
            )));
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
                Some(previous)
                    if previous.element_type() != array.element_type()
                        || !syntax::array_shapes_compatible(previous, array) =>
                {
                    return Err(ClickError::new(format!(
                        "conflicting declarations for global array `{name}`"
                    )));
                }
                Some(previous)
                    if previous.is_initialized_definition()
                        && array.is_initialized_definition() =>
                {
                    return Err(ClickError::new(format!(
                        "multiple definitions of global array `{name}`"
                    )));
                }
                _ => {
                    let merged = syntax::merge_global_array_declarations(
                        global_arrays.get(name),
                        array.clone(),
                    );
                    global_arrays.insert(name.clone(), merged);
                }
            }
        }
    }
    if let Some((name, array)) = global_arrays.iter().find(|(_, array)| !array.is_defined()) {
        let message = if array.is_tentative() {
            format!(
                "global array `{name}` has an incomplete tentative definition but no complete definition"
            )
        } else {
            format!("global array `{name}` is declared `extern` but has no definition")
        };
        return Err(ClickError::new(message));
    }
    let mut global_aggregates_by_source =
        BTreeMap::<String, BTreeMap<String, syntax::C0GlobalAggregate>>::new();
    for (source_path, unit) in &units {
        let source_aggregates = global_aggregates_by_source
            .entry(source_path.clone())
            .or_default();
        for (name, aggregate) in &unit.global_aggregates {
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
                Some(previous)
                    if previous.is_initialized_definition()
                        && aggregate.is_initialized_definition() =>
                {
                    if previous != aggregate {
                        return Err(ClickError::new(format!(
                            "conflicting definitions for aggregate global `{name}` in `{source_path}`"
                        )));
                    }
                }
                _ => {
                    let merged = match source_aggregates.get(name) {
                        Some(previous) if previous.is_initialized_definition() => previous.clone(),
                        Some(_) if aggregate.is_initialized_definition() => aggregate.clone(),
                        Some(previous) if previous.is_tentative() => previous.clone(),
                        None => aggregate.clone(),
                        Some(_) => aggregate.clone(),
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
                Some(previous)
                    if previous.is_initialized_definition()
                        && aggregate.is_initialized_definition() =>
                {
                    return Err(ClickError::new(format!(
                        "multiple definitions of aggregate global `{name}`"
                    )));
                }
                _ => {
                    let merged = match global_aggregates.get(name) {
                        Some(previous) if previous.is_initialized_definition() => previous.clone(),
                        Some(_) if aggregate.is_initialized_definition() => aggregate.clone(),
                        Some(previous) if previous.is_tentative() => previous.clone(),
                        None => aggregate.clone(),
                        Some(_) => aggregate.clone(),
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
    for (source_path, unit) in &units {
        let source_aggregate_arrays = global_aggregate_arrays_by_source
            .entry(source_path.clone())
            .or_default();
        for (name, aggregate) in &unit.global_aggregate_arrays {
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
                        || !syntax::array_lengths_compatible(
                            previous.array_length(),
                            aggregate.array_length(),
                        ) =>
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
                Some(previous)
                    if previous.is_initialized_definition()
                        && aggregate.is_initialized_definition() =>
                {
                    if previous != aggregate {
                        return Err(ClickError::new(format!(
                            "conflicting definitions for aggregate global array `{name}` in `{source_path}`"
                        )));
                    }
                }
                _ => {
                    let merged = match source_aggregate_arrays.get(name) {
                        Some(previous) if previous.is_initialized_definition() => previous.clone(),
                        Some(_) if aggregate.is_initialized_definition() => aggregate.clone(),
                        Some(previous) if previous.is_tentative() => previous.clone(),
                        None => aggregate.clone(),
                        Some(_) => aggregate.clone(),
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
                        || !syntax::array_lengths_compatible(
                            previous.array_length(),
                            aggregate.array_length(),
                        ) =>
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
                Some(previous)
                    if previous.is_initialized_definition()
                        && aggregate.is_initialized_definition() =>
                {
                    return Err(ClickError::new(format!(
                        "multiple definitions of aggregate global array `{name}`"
                    )));
                }
                _ => {
                    let merged = match global_aggregate_arrays.get(name) {
                        Some(previous) if previous.is_initialized_definition() => previous.clone(),
                        Some(_) if aggregate.is_initialized_definition() => aggregate.clone(),
                        Some(previous) if previous.is_tentative() => previous.clone(),
                        None => aggregate.clone(),
                        Some(_) => aggregate.clone(),
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

    for (source_path, function) in parsed.values() {
        function.validate_static_initializers().map_err(|error| {
            ClickError::new(format!(
                "failed to resolve static initializer in `{source_path}`: {error}"
            ))
        })?;
    }

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

    if parsed.contains_key("main") {
        let mut storage_functions = parsed
            .values()
            .map(|(_, function)| function.to_kernel_static_storage(function.name() == "main"))
            .collect::<Vec<_>>();
        // Main already supplies the linked external objects and its own
        // translation unit's private objects. Visit each remaining unit's
        // declarations once, including data-only files; do not copy every
        // function body or its whole visible global map at startup.
        let main_source = &parsed["main"].0;
        for source_path in units.keys().filter(|path| *path != main_source) {
            let visible_globals = globals_by_source[source_path]
                .iter()
                .map(|(name, object)| {
                    (
                        name.clone(),
                        if object.is_file_static() {
                            object
                        } else {
                            &globals[name]
                        }
                        .clone(),
                    )
                })
                .collect();
            let visible_arrays = global_arrays_by_source[source_path]
                .iter()
                .map(|(name, object)| {
                    (
                        name.clone(),
                        if object.is_file_static() {
                            object
                        } else {
                            &global_arrays[name]
                        }
                        .clone(),
                    )
                })
                .collect();
            let visible_aggregates = global_aggregates_by_source[source_path]
                .iter()
                .map(|(name, object)| {
                    (
                        name.clone(),
                        if object.is_file_static() {
                            object
                        } else {
                            &global_aggregates[name]
                        }
                        .clone(),
                    )
                })
                .collect();
            let visible_aggregate_arrays = global_aggregate_arrays_by_source[source_path]
                .iter()
                .map(|(name, object)| {
                    (
                        name.clone(),
                        if object.is_file_static() {
                            object
                        } else {
                            &global_aggregate_arrays[name]
                        }
                        .clone(),
                    )
                })
                .collect();
            let storage = syntax::C0Function::external(syntax::C0Type::Void, String::new(), vec![])
                .with_globals(visible_globals)
                .with_global_arrays(visible_arrays)
                .with_global_aggregates(visible_aggregates)
                .with_global_aggregate_arrays(visible_aggregate_arrays);
            storage
                .validate_static_initializers()
                .map_err(|error| ClickError::new(error.to_string()))?;
            storage_functions.push(storage.to_kernel_static_storage(true));
        }
        parsed
            .get_mut("main")
            .expect("main was found")
            .1
            .program_entry_state = Some(std::sync::Arc::new(
            crate::kernel::initialize_c_program_storage(storage_functions),
        ));
    }
    Ok(parsed)
}

pub(in crate::surface) fn external_c0_function(
    function_block: &FunctionBlock,
) -> syntax::C0Function {
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
    .with_return_pointee_constant(function_block.signature().return_pointee_is_constant())
}

pub(in crate::surface) fn build_function_environment(
    parsed_sources: &BTreeMap<String, (String, syntax::C0Function)>,
    function_blocks: &[FunctionBlock],
    contract_definitions: &[ContractDefinition],
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    resource_environment: &ResourceEnvironment,
) -> Result<CExecutionEnvironment, ClickError> {
    let mut environment = CExecutionEnvironment::new();
    for definition in contract_definitions {
        let function_block = definition.function_block();
        let parsed_function = external_c0_function(function_block);
        let (state, arguments, _, _) = initial_claim_context(
            function_block,
            &parsed_function,
            resource_environment,
            predicate_environment,
            click_function_environment,
            &format!("{}.named contract", definition.name()),
        )
        .map_err(|error| {
            ClickError::new(format!(
                "could not prepare named contract `{}`: {}",
                definition.name(),
                error.message()
            ))
        })?;
        let function = annotated_function(
            function_block,
            &parsed_function,
            &state,
            &arguments,
            predicate_environment,
            click_function_environment,
            resource_environment,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "could not lower named contract `{}`: {}",
                definition.name(),
                error.message()
            ))
        })?;
        let contract = CFunctionContract::new(definition.name(), function).ok_or_else(|| {
            ClickError::new(format!(
                "named contract `{}` cannot be applied opaquely",
                definition.name()
            ))
        })?;
        let proof_parameters = definition
            .proof_parameters()
            .unwrap_or(&[])
            .iter()
            .map(|parameter| {
                resource_clause_to_resource_spec_with_parameters(
                    parameter,
                    parsed_function.parameters(),
                    None,
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        environment =
            environment.with_function_contract(contract.with_proof_parameters(proof_parameters));
    }
    for (_, function) in parsed_sources.values() {
        let function = match function_blocks
            .iter()
            .find(|block| block.signature().name() == function.source_name())
        {
            Some(function_block) => {
                let (resource_requires, resource_ensures) =
                    function_resource_summary(function_block, function, resource_environment)?;
                let resource_constructors = function_resource_constructors(function_block)?;
                let (
                    contract_requires,
                    contract_requirement_sources,
                    contract_ensures,
                    contract_mutable,
                    resource_derived_mutable,
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
                let resource_derived_mutable_frame = function_block
                    .requires()
                    .iter()
                    .any(|requirement| matches!(requirement.inner(), Requirement::Resource(_)));
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
                    )
                    .with_contract_requirement_sources(contract_requirement_sources);
                let function =
                    function.with_resource_derived_mutable_segments(resource_derived_mutable);
                if resource_derived_mutable_frame {
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
    let borrowed_resources = function_block
        .ensures()
        .iter()
        .filter(|ensure| ensure.borrowed())
        .filter_map(|ensure| match ensure.ensure() {
            Ensure::Resource(resource) => Some(resource),
            Ensure::Proposition(_) => None,
        })
        .collect::<Vec<_>>();
    let mut borrowed_requirements = vec![false; borrowed_resources.len()];
    let mut requires = Vec::new();
    let resource_clause_count = function_block
        .requires()
        .iter()
        .filter(|requirement| matches!(requirement.inner(), Requirement::Resource(_)))
        .count();
    let mut resource_clause_index = 0;
    for requirement in function_block.requires() {
        let Requirement::Resource(resource) = requirement.inner() else {
            continue;
        };
        let first_spec = requires.len();
        append_entry_resource_specs(
            resource,
            parsed_function.parameters(),
            resource_environment,
            &mut requires,
        )?;
        let borrowed_index = borrowed_resources
            .iter()
            .enumerate()
            .find(|(index, borrowed)| !borrowed_requirements[*index] && **borrowed == resource)
            .map(|(index, _)| index);
        let role = if requires[first_spec..].iter().any(CResourceSpec::is_view)
            || borrowed_index.is_some()
        {
            if let Some(index) = borrowed_index {
                borrowed_requirements[index] = true;
            }
            CResourceTransferRole::Borrow
        } else {
            CResourceTransferRole::Consume
        };
        for spec in &mut requires[first_spec..] {
            *spec = spec
                .clone()
                .with_role(role)
                .with_snapshot(CResourceSnapshot::Entry)
                .with_clause_position(resource_clause_index, resource_clause_count);
        }
        resource_clause_index += 1;
    }
    let mut ensures = Vec::new();
    let ensure_clause_count = function_block
        .ensures()
        .iter()
        .filter(|ensure| matches!(ensure.ensure(), Ensure::Resource(_)))
        .count();
    let mut ensure_clause_index = 0;
    for ensure in function_block.ensures() {
        let Ensure::Resource(resource) = ensure.ensure() else {
            continue;
        };
        let role = if ensure.borrowed() {
            CResourceTransferRole::Borrow
        } else {
            CResourceTransferRole::Produce
        };
        let snapshot = if ensure.borrowed() {
            CResourceSnapshot::Entry
        } else {
            CResourceSnapshot::Post
        };
        let specs = resource_clause_to_resource_specs_with_metadata(
            resource,
            parsed_function.parameters(),
            Some(parsed_function.return_type().to_kernel_type()),
            role,
            snapshot,
        )?;
        for mut spec in specs {
            // Instance ownership is identity-borrowed but field-produced: its
            // selected identity comes from entry while its declared fields are
            // checked against the post-call instance.  Keep that exceptional
            // snapshot explicit in the normalized descriptor.
            if ensure.borrowed() && spec.is_instance() {
                spec = spec.with_snapshot(CResourceSnapshot::Post);
            }
            ensures.push(spec.with_clause_position(ensure_clause_index, ensure_clause_count));
        }
        ensure_clause_index += 1;
    }
    Ok((requires, ensures))
}

pub(in crate::surface) fn function_resource_constructors(
    function_block: &FunctionBlock,
) -> Result<Vec<CResourceSpec>, ClickError> {
    function_block
        .constructs()
        .iter()
        .map(|resource| {
            resource_clause_to_resource_spec_with_metadata(
                resource,
                &[],
                None,
                CResourceTransferRole::Produce,
                CResourceSnapshot::Current,
            )
        })
        .collect()
}

pub(in crate::surface) fn composite_resource_definitions(
    resource_environment: &ResourceEnvironment,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<CCompositeResourceDefinition>, ClickError> {
    let mut definitions = Vec::new();
    // Resource-match Integer binders are logical atoms in the lowered arm
    // facts. Allocate them once for the complete function environment so
    // unrelated resources cannot accidentally share a carrier identity.
    let mut next_integer_binding_variable = 9_100_000_000u64;
    for definition in resource_environment.definitions.values() {
        // Field-bearing definitions retain their schema; only checked
        // instance exchanges may expose their bodies without erasing identity.
        let Some(body) = definition.composite_body() else {
            continue;
        };
        // The body's memory clauses take their element widths from the
        // definition's own parameters and field types, as contract clauses
        // do, so a `uint64` field is one 8-byte element on both sides of
        // an unfold.
        let definition_parameters = definition
            .parameters()
            .iter()
            .map(|parameter| {
                syntax::C0Parameter::new(
                    parameter.c_type(),
                    parameter.name().to_string(),
                    parameter.struct_name().map(str::to_string),
                )
            })
            .collect::<Vec<_>>();
        let contains = body
            .contains()
            .iter()
            .map(|resource| {
                resource_clause_to_resource_spec_for_body(resource, &definition_parameters, None)
            })
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
        let matched = if let Some(matched) = &body.matched {
            let schema = definition
                .field_schema()
                .ok_or_else(|| ClickError::new("resource match requires a checked field schema"))?;
            let field_index = definition
                .fields()
                .iter()
                .position(|field| field.name == matched.field)
                .ok_or_else(|| ClickError::new("unknown resource match field"))?;
            let crate::kernel::ResourceFieldType::Algebraic(algebraic_type) =
                &schema.fields()[field_index].1
            else {
                return Err(ClickError::new(
                    "resource match requires an algebraic field",
                ));
            };
            let scopes = validation::resource_match_arm_scopes(
                definition,
                |name| {
                    click_function_environment
                        .algebraic_type_definitions
                        .get(name)
                },
                |name| resource_environment.get(name),
            )?;
            let mut arms = Vec::new();
            for (variant, bindings, arm) in scopes {
                let mut integer_binding_variables = BTreeMap::new();
                let mut binding_variables = Vec::with_capacity(bindings.len());
                for (name, ty) in &bindings {
                    if *ty == ClickType::Integer {
                        let variable = crate::kernel::Variable(next_integer_binding_variable);
                        next_integer_binding_variable = next_integer_binding_variable
                            .checked_add(1)
                            .ok_or_else(|| {
                                ClickError::new("resource match Integer binding identity exhausted")
                            })?;
                        integer_binding_variables.insert(name.clone(), variable);
                        binding_variables.push(Some(variable));
                    } else {
                        binding_variables.push(None);
                    }
                }
                let parameters = arm
                    .parameters()
                    .iter()
                    .map(|parameter| {
                        syntax::C0Parameter::new(
                            parameter.c_type(),
                            parameter.name().to_string(),
                            parameter.struct_name().map(str::to_string),
                        )
                    })
                    .collect::<Vec<_>>();
                let contains = arm
                    .composite_body()
                    .unwrap()
                    .contains()
                    .iter()
                    .map(|resource| {
                        resource_clause_to_resource_spec_for_body(resource, &parameters, None)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let facts = lower_composite_resource_facts_with_bindings(
                    &arm,
                    predicate_environment,
                    click_function_environment,
                    &bindings,
                    &integer_binding_variables,
                )?;
                let binding_types = algebraic_type
                    .variants
                    .iter()
                    .find(|entry| entry.name == variant)
                    .ok_or_else(|| ClickError::new("unknown resource match constructor"))?
                    .fields
                    .clone();
                arms.push(crate::kernel::CResourceMatchArm {
                    children: arm
                        .composite_body()
                        .unwrap()
                        .children
                        .iter()
                        .map(|child| {
                            Ok(crate::kernel::CResourceChildSpec {
                                name: child.name.clone(),
                                resource: child.resource.clone(),
                                binding: child.identity,
                                arguments: child
                                    .arguments
                                    .iter()
                                    .map(resource_argument_to_c_expression)
                                    .collect::<Result<_, _>>()?,
                                field_bindings: child.field_bindings.clone(),
                            })
                        })
                        .collect::<Result<_, ClickError>>()?,
                    variant,
                    bindings: bindings.into_iter().map(|(name, _)| name).collect(),
                    binding_types,
                    binding_variables,
                    contains,
                    facts,
                });
            }
            Some(crate::kernel::CResourceMatchBody {
                field_index,
                algebraic_type: algebraic_type.clone(),
                arms,
            })
        } else {
            None
        };
        // A matched definition keeps its children inside the arms, so the
        // unmatched `contains` walk above never sees them. `recursive`
        // describes that unmatched memory body, which instance fold/unfold
        // rewrites, so it stays as computed; the definition-level answer,
        // which expansion cycle guards and structural measures ask for, also
        // counts a same-family child declared inside an arm.
        let matched_recursive = matched.as_ref().is_some_and(|matched| {
            matched.arms.iter().any(|arm| {
                arm.children
                    .iter()
                    .any(|child| child.resource == definition.name())
            })
        });
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
            .with_witnesses(witnesses)
            .with_resource_match_body(matched)
            .with_matched_recursion(matched_recursive)
            .with_instance_schema(definition.field_schema().cloned()),
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
    specs.extend(resource_clause_to_resource_specs_with_metadata(
        resource,
        parameters,
        None,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )?);
    Ok(())
}

fn resource_clause_to_resource_specs_with_metadata(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    result_type: Option<crate::kernel::CType>,
    role: crate::kernel::CResourceTransferRole,
    snapshot: crate::kernel::CResourceSnapshot,
) -> Result<Vec<CResourceSpec>, ClickError> {
    if let ResourceClause::MemoryAggregate { access, segments } = resource {
        return segments
            .iter()
            .map(|segment| {
                let leaf = match access {
                    ResourceAccessMode::Own => ResourceClause::OwnMemory(segment.clone()),
                    ResourceAccessMode::View => ResourceClause::ViewMemory(segment.clone()),
                };
                resource_clause_to_resource_spec_with_metadata(
                    &leaf,
                    parameters,
                    result_type,
                    role,
                    snapshot,
                )
            })
            .collect();
    }
    Ok(vec![resource_clause_to_resource_spec_with_metadata(
        resource,
        parameters,
        result_type,
        role,
        snapshot,
    )?])
}

fn resource_clause_to_resource_spec_with_parameters(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    result_type: Option<crate::kernel::CType>,
) -> Result<CResourceSpec, ClickError> {
    resource_clause_to_resource_spec_with_metadata(
        resource,
        parameters,
        result_type,
        crate::kernel::CResourceTransferRole::Borrow,
        crate::kernel::CResourceSnapshot::Entry,
    )
}

fn resource_clause_to_resource_spec_for_body(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    result_type: Option<crate::kernel::CType>,
) -> Result<CResourceSpec, ClickError> {
    let role = match resource {
        ResourceClause::Named { .. } | ResourceClause::Quantified { .. } => {
            CResourceTransferRole::Consume
        }
        ResourceClause::ViewMemory(_) => CResourceTransferRole::Borrow,
        ResourceClause::OwnMemory(_) => CResourceTransferRole::Consume,
        ResourceClause::MemoryAggregate { access, .. }
        | ResourceClause::Declared { access, .. } => match access {
            ResourceAccessMode::Own => CResourceTransferRole::Consume,
            ResourceAccessMode::View => CResourceTransferRole::Borrow,
        },
    };
    resource_clause_to_resource_spec_with_metadata(
        resource,
        parameters,
        result_type,
        role,
        CResourceSnapshot::Current,
    )
}

fn resource_clause_to_resource_spec_with_metadata(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    result_type: Option<crate::kernel::CType>,
    role: crate::kernel::CResourceTransferRole,
    snapshot: crate::kernel::CResourceSnapshot,
) -> Result<CResourceSpec, ClickError> {
    match resource {
        ResourceClause::Named { binding, resource } => {
            let inner = resource_clause_to_resource_spec_with_metadata(
                resource,
                parameters,
                result_type,
                role,
                snapshot,
            )?;
            CResourceSpec::instance(
                binding.identity,
                binding.name.clone(),
                binding.schema.clone().ok_or_else(|| {
                    ClickError::new("resource binding has no checked field schema")
                })?,
                inner,
                role,
                snapshot,
            )
            .map_err(|error| ClickError::new(error.to_string()))
        }
        ResourceClause::Quantified { quantity, resource } => {
            let inner = resource_clause_to_resource_spec_with_metadata(
                resource,
                parameters,
                result_type,
                role,
                snapshot,
            )?;
            CResourceSpec::quantified(
                resource_argument_to_c_expression(quantity)?,
                inner,
                role,
                snapshot,
            )
            .map_err(|error| ClickError::new(error.to_string()))
        }
        ResourceClause::ViewMemory(segment) => Ok(CResourceSpec::memory(
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
            CResourceAccessMode::View,
            role,
            snapshot,
        )),
        ResourceClause::OwnMemory(segment) => Ok(CResourceSpec::memory(
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
            CResourceAccessMode::Own,
            role,
            snapshot,
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
            CResourceSpec::declared(
                match kind {
                    ResourceKind::Composite => ResourceFamily::Composite,
                    ResourceKind::Token => ResourceFamily::Token,
                },
                access,
                name.clone(),
                arguments,
                parameter_types,
                role,
                snapshot,
            )
            .map_err(|error| ClickError::new(error.to_string()))
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

pub(in crate::surface) fn substitute_resource_clause_for_summary<'a>(
    resource: &ResourceClause,
    substitutions: impl Into<ContractSubstitutions<'a>>,
) -> Result<ResourceClause, String> {
    substitute_resource_clause_for_summary_in(resource, &substitutions.into())
}

pub(in crate::surface) fn substitute_resource_clause_for_summary_in(
    resource: &ResourceClause,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ResourceClause, String> {
    match resource {
        ResourceClause::Named { binding, resource } => Ok(ResourceClause::Named {
            binding: match substitutions.instance_rename(&binding.name, binding.identity) {
                Some(name) => ResourceInstanceBinding {
                    name,
                    ..binding.clone()
                },
                None => binding.clone(),
            },
            resource: Box::new(substitute_resource_clause_for_summary_in(
                resource,
                substitutions,
            )?),
        }),
        ResourceClause::Quantified { quantity, resource } => Ok(ResourceClause::Quantified {
            quantity: substitute_contract_expression_in(quantity, substitutions)?,
            resource: Box::new(substitute_resource_clause_for_summary_in(
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
                .map(|argument| substitute_contract_expression_in(argument, substitutions))
                .collect::<Result<Vec<_>, _>>()?,
            parameter_types: parameter_types.clone(),
        }),
    }
}

pub(in crate::surface) fn substitute_contract_segment(
    segment: &ContractSegment,
    substitutions: &ContractSubstitutions<'_>,
) -> Result<ContractSegment, String> {
    let surface = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression_in(base, substitutions)?,
            start: substitute_contract_expression_in(start, substitutions)?,
            end: substitute_contract_expression_in(end, substitutions)?,
        },
        surface => surface.clone(),
    };
    Ok(ContractSegment {
        state: segment.state,
        base: substitute_c_fragment_in(&segment.base, substitutions)?,
        start: substitute_c_fragment_in(&segment.start, substitutions)?,
        end: substitute_c_fragment_in(&segment.end, substitutions)?,
        surface,
    })
}

pub(in crate::surface) fn resource_clause_to_resource_spec(
    resource: &ResourceClause,
) -> Result<CResourceSpec, ClickError> {
    resource_clause_to_resource_spec_with_metadata(
        resource,
        &[],
        None,
        crate::kernel::CResourceTransferRole::Borrow,
        crate::kernel::CResourceSnapshot::Current,
    )
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

    if signature.return_pointee_is_constant() != parsed_function.return_pointee_is_constant() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click return pointee const is {}, C return pointee const is {}",
            signature.name(),
            signature.return_pointee_is_constant(),
            parsed_function.return_pointee_is_constant()
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
            || expected.pointee_is_constant() != actual.pointee_is_constant()
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

        validate_loop_phase_proof("initialize", region_proof_clause.initialize_proof())?;
        validate_loop_phase_proof("preserve", region_proof_clause.preserve_proof())?;
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
            ProofTactic::Both(both) => {
                validate_loop_initialization_tactics(&both.left_tactics)?;
                validate_loop_initialization_tactics(&both.right_tactics)?;
            }
            ProofTactic::UnfoldPredicate(_)
            | ProofTactic::UnfoldFunction(_)
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::Have(_)
            | ProofTactic::Assumption
            | ProofTactic::Normalize
            | ProofTactic::NormalizeUsing(_)
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

#[cfg(test)]
mod prepared_scaling_tests {
    use super::*;
    use crate::languages::c::compiler_import::PreparedCImport;

    fn imports(size: usize) -> Vec<PreparedCImport> {
        (0..size)
            .map(|index| {
                PreparedCImport::for_test(
                    &format!("unit{index}.c"),
                    &format!("int unit{index}(int value) {{ return value; }}\n"),
                )
            })
            .collect()
    }

    fn click(size: usize) -> String {
        (0..size)
            .map(|index| format!("verifying \"unit{index}.c\";\n"))
            .collect()
    }

    #[test]
    fn functions_share_one_prepared_parse_across_sizes() {
        for size in [16usize, 32, 64, 128] {
            let source = (0..size)
                .map(|index| format!("int function{index}(int value) {{ return value; }}\n"))
                .collect::<String>();
            let imports = [PreparedCImport::for_test("shared.c", &source)];
            let sources = CSourceContext::prepared(&imports);
            let click = "verifying \"shared.c\";\n";
            let file = parse_c0_click_file_context(click, &sources).unwrap();
            let functions = parse_verified_sources_context(&file, &sources).unwrap();
            assert_eq!(functions.len(), size);
            assert_eq!(sources.prepared_parse_count.get(), 1);
            parse_c_layouts(click, &sources).unwrap();
            assert_eq!(sources.prepared_parse_count.get(), 1);
        }
    }

    #[test]
    fn prepared_translation_units_parse_once_and_cache_across_sizes() {
        for size in [16usize, 32, 64, 128] {
            let imports = imports(size);
            let sources = CSourceContext::prepared(&imports);
            parse_c_layouts(&click(size), &sources).expect("prepared layouts parse");
            assert_eq!(sources.prepared_parse_count.get(), size);
            let file = parse_c0_click_file_context(&click(size), &sources)
                .expect("prepared click file parse");
            parse_verified_sources_context(&file, &sources)
                .expect("prepared verified sources parse");
            assert_eq!(sources.prepared_parse_count.get(), size);
        }
    }
}
