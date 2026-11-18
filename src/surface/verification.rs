use super::validation::{combined_algebraic_type_definitions, standard_library_function_block};
use super::*;
use crate::languages::PreparedProgram;
use crate::languages::c::compiler_import::PreparedCImport;
use crate::languages::c::target::CTarget;
use sha2::{Digest, Sha256};
#[cfg(test)]
use std::cell::Cell;
use std::cell::RefCell;
use std::sync::Arc;

mod c_frontend;
use c_frontend::file_scope_object_names;

/// Fixed-size identity attached to a checked C proof artifact.
///
/// The digest covers the immutable C input bundle, the canonical Click source
/// being checked, the target/profile, and the resource semantics boundary.
/// The session keeps the same shape as an environment identity, but theorem
/// artifacts must include the Click source digest too.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ProofArtifactIdentity {
    digest: [u8; 32],
    pub resource_semantics_version: u32,
}

impl ProofArtifactIdentity {
    pub fn digest(&self) -> &[u8; 32] {
        &self.digest
    }

    fn for_components(input_digest: [u8; 32], click_digest: [u8; 32], target: &str) -> Self {
        let version = crate::kernel::RESOURCE_SEMANTICS_VERSION.to_be_bytes();
        let digest = digest_framed_parts([
            b"click-c-proof-artifact-v3".as_slice(),
            &input_digest,
            &click_digest,
            target.as_bytes(),
            &version,
        ]);
        Self {
            digest,
            resource_semantics_version: crate::kernel::RESOURCE_SEMANTICS_VERSION,
        }
    }
}

fn digest_framed_parts<'a>(parts: impl IntoIterator<Item = &'a [u8]>) -> [u8; 32] {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update((part.len() as u64).to_be_bytes());
        digest.update(part);
    }
    digest.finalize().into()
}

thread_local! {
    static SORRY_ADMISSIONS: RefCell<Vec<SorryAdmission>> = const { RefCell::new(Vec::new()) };
}

/// One proof unit closed by `sorry` instead of a checked proof.
///
/// This is a development-only hole for reducing a failure to its minimal
/// shape. It is never sound: anything that consumed an admission as if it
/// were a checked proof would launder an unproved claim. Containment is by
/// construction — `sorry` parses only while [`with_allow_sorry`] is active
/// (set solely by `click verify --allow-sorry`), admissions are recorded
/// here rather than as kernel theorems, and `click audit`, `click expand`,
/// the mdtest harness, and `scripts/check.sh` never enable the flag.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SorryAdmission {
    /// Human-readable proof label, e.g. `child_release.contract`.
    pub label: String,
    /// Source file that holds the `sorry`.
    pub source_path: String,
}

/// Runs `verify` with the dev-only `sorry` proof hole enabled.
///
/// Off by default. The flag scopes the calling thread and restores the
/// previous setting when `verify` returns or unwinds. Never enable this in
/// `click audit`, `click expand`, test harnesses, or `scripts/check.sh`.
pub fn with_allow_sorry<T>(verify: impl FnOnce() -> T) -> T {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            crate::kernel::sorry::set_sorry_allowed(self.0);
        }
    }
    let _restore = Restore(crate::kernel::sorry::set_sorry_allowed(true));
    verify()
}

pub(crate) fn sorry_is_allowed() -> bool {
    crate::kernel::sorry::sorry_is_allowed()
}

/// Records one `sorry` admission for later loud reporting. Callers must have
/// already checked [`sorry_is_allowed`].
pub(crate) fn record_sorry_admission(label: String, source_path: String) {
    SORRY_ADMISSIONS.with(|admissions| {
        admissions
            .borrow_mut()
            .push(SorryAdmission { label, source_path })
    });
}

/// Drains recorded `sorry` admissions. `click verify` calls this to report
/// them loudly after a run.
pub fn take_sorry_admissions() -> Vec<SorryAdmission> {
    SORRY_ADMISSIONS.with(|admissions| std::mem::take(&mut *admissions.borrow_mut()))
}

/// Typed input boundary for C verification. The bundle variant preserves the
/// plain source map while leaving room for compiler-prepared inputs without
/// ambient or global state.
pub(in crate::surface) struct ProgramSourceContext<'a> {
    source: ProgramSource<'a>,
    input_digest: [u8; 32],
    specification_digest: Option<[u8; 32]>,
    parsed_units: RefCell<BTreeMap<String, Arc<syntax::CTranslationUnit>>>,
    /// Bundle sources extracted from a larger file, from the Click project.
    /// Their locations are reported as lines of that file.
    c_source_containers: BTreeMap<String, crate::source::SourceContainer>,
    /// Keeps a prepared program's model accessors bound for printing while
    /// this context lives.
    _model_accessors: Option<super::diagnostics::ModelAccessorScope>,
    #[cfg(test)]
    prepared_parse_count: Cell<usize>,
}

/// The program a [`ProgramSourceContext`] verifies.
enum ProgramSource<'a> {
    /// C sources, by path.
    Bundle(BTreeMap<&'a str, &'a str>),
    /// Compiler-prepared C imports, by logical source.
    PreparedC {
        imports: &'a [PreparedCImport],
        by_source: BTreeMap<&'a str, &'a PreparedCImport>,
        project_identity: String,
        /// Whether two imports claim the same logical source.
        duplicates: bool,
    },
    /// A prepared program of another language and its lowered execution.
    Program {
        import: PreparedProgram,
        execution: Arc<crate::languages::PreparedExecution>,
    },
}

/// The C translation units or prepared program a Click project verifies.
pub enum ProgramInputs<'a> {
    /// C sources, by path.
    Bundle(Vec<(&'a str, &'a str)>),
    /// Compiler-prepared C imports.
    Prepared(&'a [PreparedCImport]),
    /// A prepared program of another language.
    Program(PreparedProgram),
}

impl ProgramInputs<'_> {
    /// The inputs of a prepared program of another language.
    pub fn program(import: impl Into<PreparedProgram>) -> Self {
        Self::Program(import.into())
    }
}

impl<'a> ProgramSourceContext<'a> {
    pub(in crate::surface) fn bundle(sources: &[(&'a str, &'a str)]) -> Self {
        let bundle = sources.iter().copied().collect::<BTreeMap<_, _>>();
        let mut parts = Vec::with_capacity(bundle.len() * 2 + 1);
        parts.push(b"click-c-source-bundle-v1".as_slice());
        for (path, source) in &bundle {
            parts.push(path.as_bytes());
            parts.push(source.as_bytes());
        }
        let input_digest = digest_framed_parts(parts);
        Self {
            source: ProgramSource::Bundle(bundle),
            input_digest,
            specification_digest: None,
            parsed_units: RefCell::new(BTreeMap::new()),
            c_source_containers: BTreeMap::new(),
            _model_accessors: None,
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
            format!("{:x}", Sha256::digest(framed.as_bytes()))
        };
        let mut import_pairs = imports
            .iter()
            .map(|import| {
                (
                    import.logical_source().to_string(),
                    import.identity().to_string(),
                )
            })
            .collect::<Vec<_>>();
        import_pairs.sort();
        let mut identity_parts = Vec::with_capacity(import_pairs.len() * 2 + 1);
        identity_parts.push(b"click-c-prepared-project-v1".as_slice());
        for (logical_source, identity) in &import_pairs {
            identity_parts.push(logical_source.as_bytes());
            identity_parts.push(identity.as_bytes());
        }
        Self {
            source: ProgramSource::PreparedC {
                imports,
                by_source: imports
                    .iter()
                    .map(|import| (import.logical_source(), import))
                    .collect(),
                project_identity,
                duplicates: duplicate_logical_source,
            },
            input_digest: digest_framed_parts(identity_parts),
            specification_digest: None,
            parsed_units: RefCell::new(BTreeMap::new()),
            c_source_containers: BTreeMap::new(),
            _model_accessors: None,
            #[cfg(test)]
            prepared_parse_count: Cell::new(0),
        }
    }

    /// The contracts the prepared frontend supplies for library functions the
    /// program calls, parsed after the sidecar's own declarations.
    pub(in crate::surface) fn library_contracts(&self) -> &str {
        match &self.source {
            ProgramSource::Program { execution, .. } => &execution.library_contracts,
            _ => "",
        }
    }

    /// The functions [`Self::library_contracts`] declares.
    fn library_models(&self) -> Option<&BTreeSet<String>> {
        match &self.source {
            ProgramSource::Program { execution, .. } => Some(&execution.library_models),
            _ => None,
        }
    }

    /// `click_source` followed by [`Self::library_contracts`]. Appending
    /// keeps every position in the sidecar unchanged.
    pub(in crate::surface) fn with_library_contracts<'s>(
        &self,
        click_source: &'s str,
    ) -> std::borrow::Cow<'s, str> {
        match self.library_contracts() {
            "" => std::borrow::Cow::Borrowed(click_source),
            contracts => std::borrow::Cow::Owned(format!("{click_source}\n{contracts}")),
        }
    }

    pub(in crate::surface) fn program(
        import: impl Into<PreparedProgram>,
    ) -> Result<Self, ClickError> {
        let program = import.into();
        let program_execution = program.prepare_execution().map_err(ClickError::new)?;
        let model_accessors =
            super::diagnostics::ModelAccessorScope::enter(&program_execution.layouts);
        let input_digest = digest_framed_parts([
            b"click-typed-prepared-project-v1".as_slice(),
            program.language().name().as_bytes(),
            program.logical_sources().join("\0").as_bytes(),
            program.identity().as_bytes(),
        ]);
        Ok(Self {
            source: ProgramSource::Program {
                import: program,
                execution: program_execution,
            },
            input_digest,
            specification_digest: None,
            parsed_units: RefCell::new(BTreeMap::new()),
            c_source_containers: BTreeMap::new(),
            _model_accessors: model_accessors,
            #[cfg(test)]
            prepared_parse_count: Cell::new(0),
        })
    }

    /// Identity of this context's immutable inputs under `target`. Two runs
    /// over the same sources for different C targets are different proof
    /// environments and must never share a session or an incremental result.
    #[cfg(test)]
    pub(in crate::surface) fn environment_identity(
        &self,
        target: CTarget,
    ) -> ProofArtifactIdentity {
        self.environment_identity_with_runtime(target, Default::default())
    }

    pub(in crate::surface) fn environment_identity_with_runtime(
        &self,
        target: CTarget,
        runtime: crate::languages::c::thread_runtime::CThreadRuntime,
    ) -> ProofArtifactIdentity {
        let profile = runtime
            .identity_suffix()
            .map(|suffix| format!("{}:{suffix}", target.name()))
            .unwrap_or_else(|| target.name().to_string());
        ProofArtifactIdentity::for_components(
            self.input_digest,
            self.specification_digest.unwrap_or([0; 32]),
            &profile,
        )
    }

    #[cfg(test)]
    pub(in crate::surface) fn artifact_identity(
        &self,
        click_source: &str,
        target: CTarget,
    ) -> ProofArtifactIdentity {
        self.artifact_identity_with_runtime(click_source, target, Default::default())
    }

    pub(in crate::surface) fn artifact_identity_with_runtime(
        &self,
        click_source: &str,
        target: CTarget,
        runtime: crate::languages::c::thread_runtime::CThreadRuntime,
    ) -> ProofArtifactIdentity {
        let click_digest = self.specification_digest.unwrap_or_else(|| {
            digest_framed_parts([
                b"click-sidecar-source-v1".as_slice(),
                click_source.as_bytes(),
            ])
        });
        let profile = runtime
            .identity_suffix()
            .map(|suffix| format!("{}:{suffix}", target.name()))
            .unwrap_or_else(|| target.name().to_string());
        ProofArtifactIdentity::for_components(self.input_digest, click_digest, &profile)
    }

    pub(in crate::surface) fn with_click_project(mut self, project: &ClickProject) -> Self {
        self.c_source_containers = project.c_source_containers().clone();
        let mut modules = project.modules().iter().collect::<Vec<_>>();
        modules.sort_by_key(|module| module.identity());
        let mut hasher = Sha256::new();
        for part in [
            b"click-specification-project-v1".as_slice(),
            project.entry().as_bytes(),
        ] {
            hasher.update((part.len() as u64).to_be_bytes());
            hasher.update(part);
        }
        for module in modules {
            for part in [module.identity().as_bytes(), module.source().as_bytes()] {
                hasher.update((part.len() as u64).to_be_bytes());
                hasher.update(part);
            }
            let mut imports = module.imports().to_vec();
            imports.sort();
            for imported in imports {
                hasher.update((imported.len() as u64).to_be_bytes());
                hasher.update(imported.as_bytes());
            }
        }
        if let Some(profile) = project.c_profile() {
            for part in [
                b"click-c-project-profile-v1".as_slice(),
                profile
                    .target
                    .map(|target| target.name())
                    .unwrap_or("")
                    .as_bytes(),
                profile
                    .runtime
                    .and_then(|runtime| runtime.name())
                    .unwrap_or("")
                    .as_bytes(),
            ] {
                hasher.update((part.len() as u64).to_be_bytes());
                hasher.update(part);
            }
        }
        self.specification_digest = Some(hasher.finalize().into());
        self
    }

    pub(in crate::surface) fn of(inputs: &ProgramInputs<'a>) -> Result<Self, ClickError> {
        match inputs {
            ProgramInputs::Bundle(sources) => Ok(Self::bundle(sources)),
            ProgramInputs::Prepared(imports) => Ok(Self::prepared(imports)),
            ProgramInputs::Program(import) => Self::program(import),
        }
    }

    fn bundle_sources(&self) -> Result<&BTreeMap<&'a str, &'a str>, ClickError> {
        let ProgramSource::Bundle(bundle) = &self.source else {
            return Err(ClickError::new(
                "incremental source comparison is unavailable for compiler-prepared imports",
            ));
        };
        Ok(bundle)
    }

    /// The compiler-prepared C import for `source_path`.
    fn prepared_c_import(&self, source_path: &str) -> Option<&'a PreparedCImport> {
        match &self.source {
            ProgramSource::PreparedC { by_source, .. } => by_source.get(source_path).copied(),
            _ => None,
        }
    }

    /// The identity of a compiler-prepared program; `None` for C sources.
    fn prepared_project_identity(&self) -> Option<&str> {
        match &self.source {
            ProgramSource::Bundle(_) => None,
            ProgramSource::PreparedC {
                project_identity, ..
            } => Some(project_identity),
            ProgramSource::Program { import, .. } => Some(import.identity()),
        }
    }
}

fn collect_applied_theorems(tactics: &[ProofTactic], names: &mut BTreeSet<String>) {
    for (index, tactic) in tactics.iter().enumerate() {
        match tactic {
            ProofTactic::Induct { hypothesis, .. } => {
                let mut subsequent = BTreeSet::new();
                collect_applied_theorems(&tactics[index + 1..], &mut subsequent);
                subsequent.remove(hypothesis);
                names.extend(subsequent);
                break;
            }
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
            ProofTactic::StepProved { proof, .. } => match proof {
                StepProof::By(body) => collect_applied_theorems(body, names),
                StepProof::Requires(entries) => {
                    for entry in entries {
                        if let SourceProof::Script(tactics) = &entry.have.proof {
                            collect_applied_theorems(tactics, names);
                        }
                    }
                }
            },
            ProofTactic::Both(both) => {
                collect_applied_theorems(&both.left_tactics, names);
                collect_applied_theorems(&both.right_tactics, names);
            }
            ProofTactic::Cases(proof_cases) => {
                for arm in proof_cases.arms() {
                    collect_applied_theorems(arm.tactics(), names);
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

pub(in crate::surface) fn collect_applied_theorems_from_proof(
    proof: &SourceProof,
    names: &mut BTreeSet<String>,
) {
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
}

/// Whether a theorem's binders are all kernel sorts that certification can
/// quantify over, so its verified statement can become a certification fact.
fn theorem_has_certification_binders(theorem: &TheoremDefinition) -> bool {
    theorem.parameters().iter().all(|parameter| {
        matches!(
            parameter.click_type(),
            ClickType::Program(InterfaceType::Int32 | InterfaceType::FunctionPointer(_))
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
    authorities: &mut BTreeMap<String, Vec<KernelVerifiedPureTheorem>>,
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
                let sort = match parameter.interface_type() {
                    InterfaceType::Int32 => crate::kernel::Sort::ProgramInt32,
                    InterfaceType::FunctionPointer(_) => crate::kernel::Sort::ProgramPointer(
                        parameter.interface_type().to_kernel_type(),
                    ),
                    _ => unreachable!("the theorem binder filter admits only supported types"),
                };
                Proposition::ForAll {
                    var: crate::kernel::Variable(index as u64),
                    sort,
                    body: Box::new(body),
                    name: crate::kernel::BinderName::written(parameter.name()),
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

fn record_assumed_theorem_certification_authority(
    assumed: Vec<(String, Proposition, KernelVerifiedPureTheorem)>,
    facts: &mut BTreeMap<String, Vec<Proposition>>,
    authorities: &mut BTreeMap<String, Vec<KernelVerifiedPureTheorem>>,
) {
    for (name, fact, authority) in assumed {
        facts.entry(name.clone()).or_default().push(fact);
        authorities.entry(name).or_default().push(authority);
    }
}

/// The entry module's theorem proofs selected by the CLI scope. Imported
/// theorem statements and unselected local statements are interfaces; using
/// one does not recursively select its proof body.
fn selected_theorem_definitions(
    file: &ClickFile,
    selected_functions: Option<&BTreeSet<String>>,
    verification_target: Option<&VerificationTarget>,
) -> Vec<TheoremDefinition> {
    if let Some(VerificationTarget::Theorem(name)) = verification_target {
        return file
            .theorem_definitions()
            .iter()
            .filter(|definition| definition.name() == name && file.theorem_is_selected(name))
            .map(clone_theorem_definition_iteratively)
            .collect();
    }
    if selected_functions.is_some() {
        return Vec::new();
    }
    file.theorem_definitions()
        .iter()
        .filter(|definition| file.theorem_is_selected(definition.name()))
        .map(clone_theorem_definition_iteratively)
        .collect()
}

/// Parses a sidecar under the C target it selects, or the default target.
pub fn parse(source: &str) -> Result<ClickFile, ClickError> {
    parser::parse_for_target(
        source,
        crate::surface::expansion::selected_c_target(source)?,
    )
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
    function_environment: Option<&ExecutionEnvironment>,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let predicate_definitions = combined_predicate_definitions(file)?;
    let click_function_definitions = combined_click_function_definitions(file)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions)
        .with_contracts(file.contract_definitions(), &file.program_function_names);
    let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
        &click_function_definitions,
        &combined_algebraic_type_definitions(file)?,
    );
    let function_source_registry = Arc::new(FunctionSourceRegistry::from_function_blocks(
        &combined_external_function_blocks(file)?,
    )?);
    verify_theorem_definitions(
        TheoremEnvironment::with_standard_library(&[])?.with_discovery_library(file)?,
        file.theorem_definitions(),
        SpecDefinitions::new(&predicate_environment, &click_function_environment)
            .with_struct_sizes(&file.struct_sizes),
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
    let mut empty = parse("")?;
    empty.library_imports = CLICK_LIBRARY_MODULES
        .iter()
        .map(|(identity, _)| (*identity).to_string())
        .collect();
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
        TheoremEnvironment::new(&[]),
        standard_library_theorem_definitions()?,
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        None,
        &ResourceEnvironment::new(&combined_resource_definitions(&empty)?),
        function_source_registry,
    )
}

pub(in crate::surface) fn verify_click_theorem_context(
    click_source: &str,
    sources: &ProgramSourceContext<'_>,
    theorem_name: &str,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let layouts = parse_c_layouts(click_source, sources)?;
    let file = parser::parse_with_layouts_and_aggregate_objects(
        &sources.with_library_contracts(click_source),
        layouts,
    )?;
    verify_click_file_theorem_context(file, sources, theorem_name)
}

pub(in crate::surface) fn verify_click_project_theorem_context(
    project: &ClickProject,
    sources: &ProgramSourceContext<'_>,
    theorem_name: &str,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    let file = resolve_click_project_context(project, sources)?;
    if !file.theorem_is_selected(theorem_name) {
        return Err(ClickError::new(format!(
            "theorem `{theorem_name}` is declared by an imported module, not the selected entry module"
        )));
    }
    verify_click_file_theorem_context(file, sources, theorem_name)
}

fn verify_click_file_theorem_context(
    file: ClickFile,
    sources: &ProgramSourceContext<'_>,
    theorem_name: &str,
) -> Result<Vec<VerifiedPureTheorem>, ClickError> {
    modules::reject_theorem_justification_cycles(&file)?;
    let parsed_sources = parse_verified_sources_context(&file, sources)?;
    let (file, parsed_sources) = with_tactic_procedures(file, parsed_sources)?;
    let theorem = file
        .theorem_definitions()
        .iter()
        .find(|definition| definition.name() == theorem_name)
        .ok_or_else(|| ClickError::new(format!("unknown theorem `{theorem_name}`")))?;
    let predicate_definitions = combined_predicate_definitions(&file)?;
    let click_function_definitions = combined_click_function_definitions(&file)?;
    let resource_definitions = combined_resource_definitions(&file)?;
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions)
        .with_contracts(file.contract_definitions(), &file.program_function_names);
    let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
        &click_function_definitions,
        &combined_algebraic_type_definitions(&file)?,
    );
    let spec_definitions =
        SpecDefinitions::new(&predicate_environment, &click_function_environment)
            .with_struct_sizes(&file.struct_sizes);
    let resource_environment = ResourceEnvironment::new(&resource_definitions);
    let external_and_user_function_blocks = combined_external_function_blocks(&file)?;
    let mut function_environment = build_function_environment(
        &parsed_sources,
        &external_and_user_function_blocks,
        file.contract_definitions(),
        spec_definitions,
        &resource_environment,
    )?
    .with_byte_order(file.selected_c_target().byte_order());
    function_environment = with_unselected_tactic_interfaces(&file, function_environment);
    for target in contract_refinement_targets(&file, theorem_name) {
        let Some(function) = function_environment
            .get_function(file.program_function_names.get(&target).unwrap_or(&target))
            .cloned()
        else {
            continue;
        };
        if let Some(hypothesis) =
            crate::kernel::program_recursive_function_contract_hypothesis(function)
        {
            function_environment = function_environment.with_verified_function_rule(hypothesis);
        }
    }
    let theorem_environment =
        TheoremEnvironment::with_standard_library(file.theorem_definitions())?
            .with_discovery_library(&file)?;
    if theorem.executes.is_some() {
        let registry = std::sync::Arc::new(FunctionSourceRegistry::from_function_blocks(
            &external_and_user_function_blocks,
        )?);
        let dependencies = TheoremEnvironment::with_standard_library(
            file.theorem_definitions()
                .iter()
                .take_while(|definition| definition.name() != theorem_name),
        )?
        .with_discovery_library(&file)?;
        return verify_theorem_definitions(
            dependencies,
            std::slice::from_ref(theorem),
            spec_definitions,
            Some(&function_environment),
            &resource_environment,
            registry,
        );
    }
    verify_theorem_definition(
        theorem,
        spec_definitions,
        &theorem_environment,
        Some(&function_environment),
    )
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
        // Contract value parameters follow the function pointer. They do
        // not change which function's interface the refinement depends on.
        let Some(argument) = arguments.first() else {
            continue;
        };
        if let Some(target) = contract_expression_function_address(argument) {
            targets.insert(target.to_string());
        }
    }
    targets
}

pub(in crate::surface) fn parse_click_file_with_c_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<ClickFile, ClickError> {
    let sources = ProgramSourceContext::bundle(c_sources);
    parse_click_file_with_program_sources(click_source, &sources)
}

fn parse_click_file_with_program_sources(
    click_source: &str,
    sources: &ProgramSourceContext<'_>,
) -> Result<ClickFile, ClickError> {
    if super::selected_thread_runtime(click_source)?
        == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread
        && super::selected_c_target(click_source)? != CTarget::X86_64LinuxUserspace
    {
        return Err(ClickError::new(
            "modeled-pthread runtime requires mode `userspace`",
        ));
    }
    let layouts = parse_c_layouts(click_source, sources)?;
    parser::parse_with_layouts_and_aggregate_objects(
        &sources.with_library_contracts(click_source),
        layouts,
    )
}

/// Adds every user-defined tactic to the run as the contract of a procedure
/// whose whole body is `return;`.
///
/// A tactic runs no code, so its contract holds of the proof state exactly
/// when it holds of that empty procedure: certifying the procedure is
/// certifying the tactic, through the same contract, recursion, and
/// termination checks every C function has, and the packaged rule is what an
/// application of the tactic applies. The tactic's own script runs first;
/// then the one `return` is stepped, and every claim is closed by
/// `known`, so the script must already have established each produced
/// instance and each `ensures` as an available fact.
fn with_tactic_procedures(
    mut file: ClickFile,
    mut parsed_sources: BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
) -> Result<
    (
        ClickFile,
        BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    ),
    ClickError,
> {
    for tactic in file.tactic_definitions.clone() {
        let name = tactic.name().to_string();
        if parsed_sources.contains_key(&name)
            || file
                .function_blocks
                .iter()
                .any(|function| function.signature().name() == name)
        {
            return Err(ClickError::new(format!(
                "tactic `{name}` has the name of a C function; give the tactic its own name"
            )));
        }
        let mut block = tactic.function_block().clone();
        block.tactic_procedure = true;
        let Some(SourceProof::Script(mut script)) = block
            .grouped_proof
            .take()
            .map(std::sync::Arc::unwrap_or_clone)
        else {
            return Err(ClickError::new(format!(
                "tactic `{name}` must be proved by an explicit `by {{ ... }}` script"
            )));
        };
        if let Some(executing) = first_executing_tactic(&script) {
            return Err(ClickError::new(format!(
                "tactic `{name}` runs no code, so its proof cannot use `{executing}`; a \
                 tactic's proof folds, unfolds, applies, and proves facts at one point"
            )));
        }
        let mut suffix = vec![ProofTactic::Synthetic(Box::new(ProofTactic::Step))];
        suffix.extend(std::iter::repeat_n(
            ProofTactic::Synthetic(Box::new(ProofTactic::Known)),
            block.ensures.len(),
        ));
        append_on_every_path(&mut script, &suffix);
        block.grouped_proof = Some(std::sync::Arc::new(SourceProof::Script(script)));
        let procedure = external_c_function(&block).with_proof_body(syntax::CStatement::Return(
            syntax::CExpression::Void,
            syntax::CSite::NONE,
        ));
        parsed_sources.insert(name, ("<tactic>".to_string(), procedure));
        file.function_blocks.push(block);
    }
    Ok((file, parsed_sources))
}

/// Theorem-only checking selects no tactic body. Its procedure contracts are
/// the same scoped declaration assumptions used by ordinary selected proofs.
fn with_unselected_tactic_interfaces(
    file: &ClickFile,
    mut environment: ExecutionEnvironment,
) -> ExecutionEnvironment {
    for block in file
        .function_blocks()
        .iter()
        .filter(|block| block.is_tactic_procedure())
    {
        let Some(function) = environment.get_function(block.signature().name()).cloned() else {
            continue;
        };
        if let Some(rule) = crate::kernel::program_unselected_function_contract_assumption(function)
        {
            environment = environment.with_external_function_rule(rule);
        }
    }
    environment
}

/// Appends `suffix` where every path of `script` ends. A proof `match` must
/// complete the proof in each arm, so a script ending in one gets the suffix
/// at the end of each arm instead. Refuted paths have no continuation; keep
/// their terminal contradiction last so the match checker can certify them.
fn append_on_every_path(script: &mut Vec<ProofTactic>, suffix: &[ProofTactic]) {
    if let Some(ProofTactic::Match(proof_match)) = script.last_mut() {
        for arm in &mut std::sync::Arc::make_mut(proof_match).arms {
            append_on_every_path(&mut arm.tactics, suffix);
        }
    } else if !matches!(script.last(), Some(ProofTactic::Contradiction(_))) {
        script.extend(suffix.iter().cloned());
    }
}

/// The first tactic in `tactics`, at any depth of proof control, that runs
/// C or addresses a C control-flow point, by its source name.
fn first_executing_tactic(tactics: &[ProofTactic]) -> Option<&'static str> {
    tactics.iter().find_map(|tactic| match tactic {
        ProofTactic::Step
        | ProofTactic::StepBind(_)
        | ProofTactic::StepContract(_)
        | ProofTactic::StepCall(_)
        | ProofTactic::StepProved { .. } => Some("step"),
        ProofTactic::SmartExecute => Some("implicit tail"),
        ProofTactic::ExecuteUntil(_) => Some("step_until"),
        ProofTactic::Loop(_) => Some("loop"),
        ProofTactic::Branch(_) => Some("branch"),
        ProofTactic::CallOutcomes(_) => Some("outcomes"),
        ProofTactic::CloseInvariantsBy(_) => Some("close_invariants"),
        // A `have` or other obligation proves a proposition, where C cannot
        // run; only the blocks that continue the proof can execute.
        tactic => tactic.children().into_iter().find_map(|child| match child {
            TacticChild::Continuing(ChildProof::Script(tactics)) => first_executing_tactic(tactics),
            _ => None,
        }),
    })
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
    for function in file.function_blocks.iter_mut().chain(
        file.tactic_definitions
            .iter_mut()
            .map(TacticDefinition::function_block_mut),
    ) {
        if function.signature.name != *target_name {
            continue;
        }
        // Expansion may make the implicit grouped proof explicit.
        function.grouped_proof = None;
        // A grouped proof supplies both normal and exceptional clauses.
        // Erase their proof annotations together, retaining the contracts.
        for ensure in function
            .ensures
            .iter_mut()
            .chain(&mut function.exceptional_ensures)
        {
            ensure.proof = SourceProof::Default;
        }
    }
    file
}

/// Whether `rewritten` differs from `baseline` outside the proof of
/// `target`. Expansion also adds the `import click::...;` lines its written
/// citations need; a library import only lets a proof cite that module's
/// theorems, which proof checking always has, so an added one is no change.
fn changed_outside_proof_unit(
    baseline: &ClickFile,
    rewritten: ClickFile,
    target: &VerificationTarget,
) -> bool {
    let mut rewritten = proof_unit_erased_click_file(rewritten, target);
    // Import locations are diagnostic metadata. Expansion may prepend a
    // library import, moving an unchanged file import to another line.
    // Preserve the ordered paths as part of the semantic boundary.
    if baseline
        .imports
        .iter()
        .map(|import| &import.path)
        .eq(rewritten.imports.iter().map(|import| &import.path))
    {
        rewritten.imports = baseline.imports.clone();
    }
    if baseline
        .library_imports
        .iter()
        .all(|module| rewritten.library_imports.contains(module))
    {
        rewritten.library_imports = baseline.library_imports.clone();
    }
    rewritten != proof_unit_erased_click_file(baseline.clone(), target)
}

pub fn verify_c_sources(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::bundle(c_sources);
        let result = verify_program_with_context(click_source, &sources, None, None, None, None)
            .map(|(verified, _)| verified);
        if let Err(error) = &result {
            error.emit_timing_failure();
        }
        result
    })
}

pub(in crate::surface) fn resolve_click_project_context(
    project: &ClickProject,
    sources: &ProgramSourceContext<'_>,
) -> Result<ClickFile, ClickError> {
    let _timing = VerificationTimingPhase::new("source resolution");
    let click_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let layouts = parse_c_layouts_for_target(
        click_source,
        sources,
        super::selected_project_c_target(project)?,
    )?;
    check_verification_deadline()?;
    modules::resolve_click_project_with_layouts(project, sources.library_contracts(), layouts)
}

/// Verifies exactly the proofs owned by a loaded entry module. Imported
/// theorem statements and declarations are available as conditional
/// interfaces, but their proof bodies are not executed.
pub fn verify_c_project(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::bundle(c_sources).with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        let source = project.entry_source().expect("resolved entry source");
        let result = verify_program_with_context(source, &sources, None, None, None, Some(file))
            .map(|(verified, _)| verified);
        if let Err(error) = &result {
            error.emit_timing_failure();
        }
        result
    })
}

/// Verifies only the proof unit at an entry-module source location.
pub fn verify_project_at(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    line: usize,
    column: usize,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        let source = project.entry_source().expect("resolved entry source");
        let target = expansion::verification_target_at_file(source, &file, line, column)?;
        verify_program_with_context(source, &sources, Some(target), None, None, Some(file))
            .map(|(verified, _)| verified)
    })
}

pub fn verify_project_functions(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    functions: impl IntoIterator<Item = String>,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    let functions = functions.into_iter().collect::<BTreeSet<_>>();
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        for name in &functions {
            if !file.function_is_selected(name)
                && let Some(owner) = file
                    .declaration_owner(&DeclarationIdentity::ProgramFunction(name.clone()))
                    .or_else(|| file.declaration_owner(&DeclarationIdentity::Tactic(name.clone())))
            {
                return Err(ClickError::new(format!(
                    "`{name}` is imported from `{owner}`; select that module to verify its proof"
                )));
            }
        }
        let source = project.entry_source().expect("resolved entry source");
        verify_program_with_context(
            source,
            &sources,
            Some(VerificationTarget::Functions(functions)),
            None,
            None,
            Some(file),
        )
        .map(|(verified, _)| verified)
    })
}

pub fn verify_c_prepared_project(
    project: &ClickProject,
    imports: &[PreparedCImport],
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::prepared(imports).with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        verify_program_with_context(
            project.entry_source().expect("resolved entry source"),
            &sources,
            None,
            None,
            None,
            Some(file),
        )
        .map(|(verified, _)| verified)
    })
}

/// Verifies a locked compiler-owned program through the ordinary proof engine.
/// The prepared artifact supplies declarations and direct kernel lowering;
/// ordinary verification never consults the source compiler.
pub fn verify_program_prepared_project(
    project: &ClickProject,
    import: impl Into<PreparedProgram>,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::program(import)?.with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        verify_program_with_context(
            project.entry_source().expect("resolved entry source"),
            &sources,
            None,
            None,
            None,
            Some(file),
        )
        .map(|(verified, _)| verified)
    })
}

/// Verifies only the entry module's pure theorem `theorem`. Theorems it
/// cites remain interfaces, exactly as when a source location selects it.
pub fn verify_project_theorem(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    theorem: &str,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        verify_program_with_context(
            project.entry_source().expect("resolved entry source"),
            &sources,
            Some(VerificationTarget::Theorem(theorem.to_owned())),
            None,
            None,
            Some(file),
        )
        .map(|(verified, _)| verified)
    })
}

/// Verifies compiler-prepared translation units through the same engine used
/// by legacy source bundles.
pub fn verify_c_prepared_sources(
    click_source: &str,
    imports: &[PreparedCImport],
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::prepared(imports);
        verify_program_with_context(click_source, &sources, None, None, None, None)
            .map(|(verified, _)| verified)
    })
}

/// Runs one ordinary verification while filling in the given expansion
/// capture. Verification behaves identically with or without the capture;
/// only the capture's `result` differs.
pub(in crate::surface) fn verify_c_sources_with_expansion_capture(
    click_source: &str,
    c_sources: &[(&str, &str)],
    expansion_capture: &mut ExpansionCapture,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        verify_c_sources_with_environment(
            click_source,
            c_sources,
            None,
            None,
            Some(expansion_capture),
        )
        .map(|(verified, _)| verified)
    })
}

pub(in crate::surface) fn verify_program_with_expansion_capture_context(
    click_source: &str,
    c_sources: &ProgramSourceContext<'_>,
    expansion_capture: &mut ExpansionCapture,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        verify_program_with_context(
            click_source,
            c_sources,
            None,
            None,
            Some(expansion_capture),
            None,
        )
        .map(|(verified, _)| verified)
    })
}

pub(in crate::surface) fn verify_project_with_expansion_capture(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
    expansion_capture: &mut ExpansionCapture,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
        let file = resolve_click_project_context(project, &sources)?;
        verify_program_with_context(
            project.entry_source().expect("resolved entry source"),
            &sources,
            None,
            None,
            Some(expansion_capture),
            Some(file),
        )
        .map(|(verified, _)| verified)
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct IncrementalSelection {
    pub selected_functions: Vec<String>,
    pub reused_functions: Vec<String>,
    pub reasons: Vec<String>,
    pub full_rebuild: bool,
}

pub fn c_source_function_names(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<Vec<String>, ClickError> {
    Ok(parse_click_file_with_c_sources(click_source, c_sources)?
        .function_blocks()
        .iter()
        .map(|function| function.signature().name().to_string())
        .collect())
}

pub fn c_project_function_names(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
) -> Result<Vec<String>, ClickError> {
    let sources = ProgramSourceContext::bundle(c_sources).with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    Ok(file
        .function_blocks()
        .iter()
        .filter(|function| file.function_is_selected(function.signature().name()))
        .map(|function| function.signature().name().to_string())
        .collect())
}

pub fn project_selected_proof_names(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
) -> Result<Vec<String>, ClickError> {
    let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    Ok(selected_entry_proof_names(&file))
}

fn selected_entry_proof_names(file: &ClickFile) -> Vec<String> {
    file.theorem_definitions()
        .iter()
        .filter(|theorem| file.theorem_is_selected(theorem.name()))
        .map(|theorem| format!("theorem:{}", theorem.name()))
        .chain(
            file.function_blocks()
                .iter()
                .filter(|function| file.function_is_selected(function.signature().name()))
                .map(|function| format!("function:{}", function.signature().name())),
        )
        .chain(
            file.tactic_definitions()
                .iter()
                .filter(|tactic| file.function_is_selected(tactic.name()))
                .map(|tactic| format!("tactic:{}", tactic.name())),
        )
        .collect()
}

fn c_imported_headers(
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
            for include in crate::languages::c::source::local_include_paths_for_target(
                &path,
                source,
                file.selected_c_target(),
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "failed to process local C headers for `{path}`: {error}"
                ))
            })? {
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
pub fn c_incremental_selection(
    current_click_source: &str,
    current_c_sources: &[(&str, &str)],
    baseline_click_source: &str,
    baseline_c_sources: &[(&str, &str)],
) -> Result<IncrementalSelection, ClickError> {
    let current_file = parse_click_file_with_c_sources(current_click_source, current_c_sources)?;
    let baseline_file = parse_click_file_with_c_sources(baseline_click_source, baseline_c_sources)?;
    let current_source_map = ProgramSourceContext::bundle(current_c_sources);
    let baseline_source_map = ProgramSourceContext::bundle(baseline_c_sources);
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
        return Ok(IncrementalSelection {
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

    let current_imports = c_imported_headers(&current_file, current_source_map.bundle_sources()?)?;
    let baseline_imports =
        c_imported_headers(&baseline_file, baseline_source_map.bundle_sources()?)?;
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
            for dependency in c_statement_calls(function).into_iter().flatten() {
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
    Ok(IncrementalSelection {
        selected_functions: affected.into_iter().collect(),
        reused_functions: reused,
        reasons,
        full_rebuild: false,
    })
}

/// Verifies exactly a selected function set in one native verifier
/// transaction. Called-function contracts are scoped assumptions; their
/// implementation proofs are not added to the selection.
pub fn verify_c_sources_functions(
    click_source: &str,
    c_sources: &[(&str, &str)],
    functions: impl IntoIterator<Item = String>,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    let functions = functions.into_iter().collect::<BTreeSet<_>>();
    instrumentation::with_default_tactic_limits(|| {
        verify_c_sources_targeted(
            click_source,
            c_sources,
            Some(VerificationTarget::Functions(functions)),
        )
    })
}

pub fn verify_c_prepared_sources_functions(
    click_source: &str,
    imports: &[PreparedCImport],
    functions: impl IntoIterator<Item = String>,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    let functions = functions.into_iter().collect::<BTreeSet<_>>();
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::prepared(imports);
        verify_program_with_context(
            click_source,
            &sources,
            Some(VerificationTarget::Functions(functions)),
            None,
            None,
            None,
        )
        .map(|(verified, _)| verified)
    })
}

fn ensure_environment_identity(
    expected: &ProofArtifactIdentity,
    sources: &ProgramSourceContext<'_>,
    target: CTarget,
    runtime: crate::languages::c::thread_runtime::CThreadRuntime,
) -> Result<(), ClickError> {
    let actual = sources.environment_identity_with_runtime(target, runtime);
    if expected == &actual {
        return Ok(());
    }
    Err(ClickError::new(format!(
        "verification session identity mismatch: inputs, view semantics, or resource semantics version changed (expected {:?}, got {:?})",
        expected, actual
    )))
}

impl ProgramVerificationSession {
    pub fn new(
        click_source: &str,
        c_sources: &[(&str, &str)],
    ) -> Result<(Self, Vec<VerifiedProgramTheorem>), ClickError> {
        Self::start(
            None,
            click_source,
            &ProgramInputs::Bundle(c_sources.to_vec()),
        )
    }

    /// Starts a reusable verification session over compiler-prepared inputs.
    /// The opaque artifacts are retained for all subsequent rewrite checks.
    pub fn new_prepared(
        click_source: &str,
        imports: &[PreparedCImport],
    ) -> Result<(Self, Vec<VerifiedProgramTheorem>), ClickError> {
        Self::start(None, click_source, &ProgramInputs::Prepared(imports))
    }

    pub fn new_program_prepared(
        click_source: &str,
        import: impl Into<PreparedProgram>,
    ) -> Result<(Self, Vec<VerifiedProgramTheorem>), ClickError> {
        Self::start(None, click_source, &ProgramInputs::program(import))
    }

    /// Starts a reusable verification session over a loaded Click module graph.
    pub fn new_project(
        project: &ClickProject,
        c_sources: &[(&str, &str)],
    ) -> Result<(Self, Vec<VerifiedProgramTheorem>), ClickError> {
        Self::start_project(project, &ProgramInputs::Bundle(c_sources.to_vec()))
    }

    pub fn new_prepared_project(
        project: &ClickProject,
        imports: &[PreparedCImport],
    ) -> Result<(Self, Vec<VerifiedProgramTheorem>), ClickError> {
        Self::start_project(project, &ProgramInputs::Prepared(imports))
    }

    pub fn new_program_prepared_project(
        project: &ClickProject,
        import: impl Into<PreparedProgram>,
    ) -> Result<(Self, Vec<VerifiedProgramTheorem>), ClickError> {
        Self::start_project(project, &ProgramInputs::program(import))
    }

    fn start_project(
        project: &ClickProject,
        inputs: &ProgramInputs<'_>,
    ) -> Result<(Self, Vec<VerifiedProgramTheorem>), ClickError> {
        let source = project.entry_source().ok_or_else(|| {
            ClickError::new(format!("missing entry module `{}`", project.entry()))
        })?;
        Self::start(Some(project), source, inputs)
    }

    /// Verifies the inputs once and retains them, with the resulting function
    /// environment, for later rewrite checks.
    fn start(
        project: Option<&ClickProject>,
        click_source: &str,
        inputs: &ProgramInputs<'_>,
    ) -> Result<(Self, Vec<VerifiedProgramTheorem>), ClickError> {
        instrumentation::with_default_tactic_limits(|| {
            let sources = ProgramSourceContext::of(inputs)?;
            // Parse the file once: verification starts from it and the
            // session keeps it as the baseline for later rewrite checks.
            let (sources, baseline_file) = match project {
                Some(project) => {
                    let sources = sources.with_click_project(project);
                    let baseline_file = resolve_click_project_context(project, &sources)?;
                    (sources, baseline_file)
                }
                None => {
                    let baseline_file =
                        parse_click_file_with_program_sources(click_source, &sources)?;
                    (sources, baseline_file)
                }
            };
            let (verified, verified_function_environment) = verify_program_with_context(
                click_source,
                &sources,
                None,
                None,
                None,
                Some(baseline_file.clone()),
            )?;
            let environment_identity = sources.environment_identity_with_runtime(
                baseline_file.selected_c_target(),
                baseline_file.selected_thread_runtime(),
            );
            Ok((
                Self {
                    c_sources: match inputs {
                        ProgramInputs::Bundle(c_sources) => c_sources
                            .iter()
                            .map(|(name, source)| ((*name).to_string(), (*source).to_string()))
                            .collect(),
                        _ => Vec::new(),
                    },
                    click_project: project.cloned(),
                    prepared_imports: match inputs {
                        ProgramInputs::Prepared(imports) => Some(imports.to_vec()),
                        _ => None,
                    },
                    prepared_program_import: match inputs {
                        ProgramInputs::Program(import) => Some(import.clone()),
                        _ => None,
                    },
                    baseline_file,
                    verified_function_environment,
                    environment_identity,
                    kernel_generation: crate::kernel::verification_session_generation(),
                    kernel_state: crate::kernel::VerificationSession::capture_state(),
                },
                verified,
            ))
        })
    }

    /// Reports whether the kernel produced separate termination evidence for
    /// this function. Ordinary partial-contract verification does not consult
    /// this stronger result.
    pub fn function_termination_is_verified(&self, name: &str) -> bool {
        self.verified_function_environment
            .has_verified_function_termination(name)
    }

    /// Refuses to reuse the retained environment once another verification
    /// on this thread has started fresh kernel tables. The environment's
    /// states name entries of the tables it was built under; against a
    /// replaced arena they would resolve to unrelated derivations, which at
    /// best makes proof work depend on whatever ran in between (a tactic
    /// exhausting its budget only in the session) and at worst lets a
    /// state inherit another verification's facts. Keep a session on a
    /// thread of its own when other verification runs on the same thread.
    /// On success, the tables are first restored to the state captured when
    /// the environment was built, so a check starts from that state alone and
    /// what an earlier check interned, named, or memoized is gone. The
    /// returned guard then joins those tables for the check, so a check that
    /// starts no retained environment (a theorem target) still runs inside
    /// them rather than replacing them for later checks.
    fn ensure_kernel_state_retained(
        &self,
    ) -> Result<crate::kernel::VerificationSession, ClickError> {
        if crate::kernel::verification_session_generation() == self.kernel_generation
            && crate::kernel::VerificationSession::restore_state(&self.kernel_state)
        {
            return Ok(crate::kernel::VerificationSession::resume());
        }
        Err(ClickError::new(
            "this verification session's kernel state was replaced by another verification on the same thread; keep a reusable verification session on a thread that runs no other verification",
        ))
    }

    pub fn verify_at(
        &self,
        click_source: &str,
        line: usize,
        column: usize,
    ) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
        let _kernel_tables = self.ensure_kernel_state_retained()?;
        instrumentation::with_default_tactic_limits(|| {
            self.verify_at_with_limits(click_source, line, column)
        })
    }

    /// Checks an entry-module rewrite against this session's unchanged imports.
    pub fn verify_at_project(
        &self,
        click_source: &str,
        line: usize,
        column: usize,
    ) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
        let _kernel_tables = self.ensure_kernel_state_retained()?;
        let baseline_project = self.click_project.as_ref().ok_or_else(|| {
            ClickError::new("verification session does not contain a Click module graph")
        })?;
        instrumentation::with_default_tactic_limits(|| {
            let project = baseline_project.with_entry_source(click_source.to_string());
            let c_sources = self
                .c_sources
                .iter()
                .map(|(name, source)| (name.as_str(), source.as_str()))
                .collect::<Vec<_>>();
            let sources = if let Some(import) = self.prepared_program_import.as_ref() {
                ProgramSourceContext::program(import)?.with_click_project(&project)
            } else if let Some(imports) = self.prepared_imports.as_ref() {
                ProgramSourceContext::prepared(imports).with_click_project(&project)
            } else {
                ProgramSourceContext::bundle(&c_sources).with_click_project(&project)
            };
            let rewritten_file = resolve_click_project_context(&project, &sources)?;
            let target = expansion::verification_target_at_file(
                click_source,
                &rewritten_file,
                line,
                column,
            )?;
            let target_exists_in_baseline = match &target {
                VerificationTarget::Function(name) => {
                    self.baseline_file
                        .function_blocks()
                        .iter()
                        .any(|function| function.signature().name() == name)
                        || self
                            .baseline_file
                            .tactic_definitions()
                            .iter()
                            .any(|tactic| tactic.name() == name)
                }
                VerificationTarget::Theorem(name) => self.baseline_file.theorem_is_selected(name),
                VerificationTarget::Functions(_) => false,
            };
            if !target_exists_in_baseline {
                return Err(ClickError::new(
                    "rewritten source location resolves to a proof unit absent from the baseline",
                ));
            }
            if changed_outside_proof_unit(&self.baseline_file, rewritten_file.clone(), &target) {
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
            verify_program_with_context(
                click_source,
                &sources,
                Some(target),
                initial_environment,
                None,
                Some(rewritten_file),
            )
            .map(|(verified, _)| verified)
        })
    }

    /// Verifies a rewritten proof location against this prepared-input
    /// session, preserving the import identity across certification.
    pub fn verify_at_prepared(
        &self,
        click_source: &str,
        line: usize,
        column: usize,
    ) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
        let _kernel_tables = self.ensure_kernel_state_retained()?;
        instrumentation::with_default_tactic_limits(|| {
            let sources = if let Some(import) = self.prepared_program_import.as_ref() {
                ProgramSourceContext::program(import)?
            } else if let Some(imports) = self.prepared_imports.as_ref() {
                ProgramSourceContext::prepared(imports)
            } else {
                return Err(ClickError::new(
                    "verification session does not contain prepared imports",
                ));
            };
            ensure_environment_identity(
                &self.environment_identity,
                &sources,
                super::selected_c_target(click_source)?,
                super::selected_thread_runtime(click_source)?,
            )?;
            let target = verification_target_at_context(click_source, &sources, line, column)?;
            let target_exists_in_baseline = match &target {
                VerificationTarget::Function(name) => {
                    self.baseline_file
                        .function_blocks()
                        .iter()
                        .any(|function| function.signature().name() == name)
                        || self
                            .baseline_file
                            .tactic_definitions()
                            .iter()
                            .any(|tactic| tactic.name() == name)
                }
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
            let rewritten_file = parse_click_file_with_program_sources(click_source, &sources)?;
            if changed_outside_proof_unit(&self.baseline_file, rewritten_file, &target) {
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
            verify_program_with_context(
                click_source,
                &sources,
                Some(target),
                initial_environment,
                None,
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
    ) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
        let c_sources = self
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let sources = ProgramSourceContext::bundle(&c_sources);
        ensure_environment_identity(
            &self.environment_identity,
            &sources,
            super::selected_c_target(click_source)?,
            super::selected_thread_runtime(click_source)?,
        )?;
        let target = verification_target_at_context(click_source, &sources, line, column)?;
        let target_exists_in_baseline = match &target {
            VerificationTarget::Function(name) => {
                self.baseline_file
                    .function_blocks()
                    .iter()
                    .any(|function| function.signature().name() == name)
                    || self
                        .baseline_file
                        .tactic_definitions()
                        .iter()
                        .any(|tactic| tactic.name() == name)
            }
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
        let rewritten_file = parse_click_file_with_program_sources(click_source, &sources)?;
        if changed_outside_proof_unit(&self.baseline_file, rewritten_file, &target) {
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
        verify_program_with_context(
            click_source,
            &sources,
            Some(target),
            initial_environment,
            None,
            None,
        )
        .map(|(verified, _)| verified)
    }
}

/// Parses and validates the complete sidecar, then verifies only the proof
/// unit containing the one-based source location and the C functions it calls.
pub fn verify_c_sources_at(
    click_source: &str,
    c_sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    instrumentation::with_default_tactic_limits(|| {
        let target = verification_target_at(click_source, c_sources, line, column)?;
        verify_c_sources_targeted(click_source, c_sources, Some(target))
    })
}

/// Verifies only the proof unit at a source location.
pub fn verify_sources_at(
    click_source: &str,
    inputs: &ProgramInputs<'_>,
    line: usize,
    column: usize,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    if let ProgramInputs::Bundle(c_sources) = inputs {
        return verify_c_sources_at(click_source, c_sources, line, column);
    }
    instrumentation::with_default_tactic_limits(|| {
        let sources = ProgramSourceContext::of(inputs)?;
        let target = verification_target_at_context(click_source, &sources, line, column)?;
        verify_program_with_context(click_source, &sources, Some(target), None, None, None)
            .map(|(verified, _)| verified)
    })
}

pub(in crate::surface) fn verify_c_sources_targeted(
    click_source: &str,
    c_sources: &[(&str, &str)],
    verification_target: Option<VerificationTarget>,
) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    verify_c_sources_with_environment(click_source, c_sources, verification_target, None, None)
        .map(|(verified, _)| verified)
}

pub(in crate::surface) fn verify_c_sources_with_environment(
    click_source: &str,
    c_sources: &[(&str, &str)],
    verification_target: Option<VerificationTarget>,
    initial_function_environment: Option<ExecutionEnvironment>,
    expansion_capture: Option<&mut ExpansionCapture>,
) -> Result<(Vec<VerifiedProgramTheorem>, ExecutionEnvironment), ClickError> {
    let sources = ProgramSourceContext::bundle(c_sources);
    verify_program_with_context(
        click_source,
        &sources,
        verification_target,
        initial_function_environment,
        expansion_capture,
        None,
    )
}

/// [`verify_program_in_context`], with a proof failure that names no
/// source located by what was being verified when it arose.
pub(in crate::surface) fn verify_program_with_context(
    click_source: &str,
    c_sources: &ProgramSourceContext<'_>,
    verification_target: Option<VerificationTarget>,
    initial_function_environment: Option<ExecutionEnvironment>,
    expansion_capture: Option<&mut ExpansionCapture>,
    resolved_file: Option<ClickFile>,
) -> Result<(Vec<VerifiedProgramTheorem>, ExecutionEnvironment), ClickError> {
    crate::surface::clear_ambient_proof_source();
    verify_program_in_context(
        click_source,
        c_sources,
        verification_target,
        initial_function_environment,
        expansion_capture,
        resolved_file,
    )
    .map_err(ClickError::located_by_ambient_source)
}

fn verify_program_in_context(
    click_source: &str,
    c_sources: &ProgramSourceContext<'_>,
    verification_target: Option<VerificationTarget>,
    initial_function_environment: Option<ExecutionEnvironment>,
    mut expansion_capture: Option<&mut ExpansionCapture>,
    resolved_file: Option<ClickFile>,
) -> Result<(Vec<VerifiedProgramTheorem>, ExecutionEnvironment), ClickError> {
    check_verification_deadline()?;
    let preselected_runtime = resolved_file
        .as_ref()
        .map(ClickFile::selected_thread_runtime)
        .unwrap_or(super::selected_thread_runtime(click_source)?);
    let preselected_target = resolved_file
        .as_ref()
        .map(ClickFile::selected_c_target)
        .unwrap_or(super::selected_c_target(click_source)?);
    if preselected_runtime == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread
        && preselected_target != CTarget::X86_64LinuxUserspace
    {
        return Err(ClickError::new(
            "modeled-pthread runtime requires mode `userspace`",
        ));
    }
    // A verification that continues from an earlier one's environment shares
    // that environment's states and keeps its kernel session; every other
    // verification starts its own, so thread-local kernel state cannot carry
    // over from whatever verified before it on this thread.
    // The guard scopes the kernel's thread-local state to this verification
    // and is held until it finishes.
    let _session = initial_function_environment
        .is_none()
        .then(crate::kernel::VerificationSession::enter);
    let session_is_fresh = _session.as_ref().is_some_and(|session| session.is_fresh());
    let (file, parsed_sources, selected_functions, resource_struct_layouts) = {
        let _timing = VerificationTimingPhase::new("frontend");
        let layouts = parse_c_layouts_for_target(
            click_source,
            c_sources,
            match &resolved_file {
                Some(file) => file.selected_c_target(),
                None => super::selected_c_target(click_source)?,
            },
        )?;
        let resource_struct_layouts = layouts.struct_layouts.clone();
        let file = match resolved_file {
            Some(file) => file,
            None => parser::parse_with_layouts_and_aggregate_objects(
                &c_sources.with_library_contracts(click_source),
                layouts,
            )?,
        };
        modules::reject_theorem_justification_cycles(&file)?;
        let parsed_sources = parse_verified_sources_context(&file, c_sources)?;
        let (file, parsed_sources) = with_tactic_procedures(file, parsed_sources)?;
        record_never_address_taken_locals(&parsed_sources, session_is_fresh);
        if session_is_fresh {
            super::lowering::reset_input_identities();
        }
        let expansion_functions = expansion_capture
            .as_deref()
            .map(|capture| {
                tactic_expansion_required_functions(
                    &file,
                    &parsed_sources,
                    (
                        capture.site.clone(),
                        capture
                            .source_index
                            .or_else(|| capture.batch.as_ref().map(|_| 0)),
                    ),
                )
            })
            .transpose()?;
        let selected_functions = if expansion_functions.is_some() {
            expansion_functions
        } else {
            match verification_target.as_ref() {
                Some(VerificationTarget::Function(function_name)) => {
                    verification_required_functions(&file, &parsed_sources, function_name)?;
                    Some(with_modeled_pthread_workers(
                        &file,
                        BTreeSet::from([function_name.clone()]),
                        &parsed_sources,
                        file.selected_thread_runtime(),
                    )?)
                }
                Some(VerificationTarget::Functions(function_names)) => {
                    for function_name in function_names {
                        verification_required_functions(&file, &parsed_sources, function_name)?;
                    }
                    Some(with_modeled_pthread_workers(
                        &file,
                        function_names.clone(),
                        &parsed_sources,
                        file.selected_thread_runtime(),
                    )?)
                }
                Some(VerificationTarget::Theorem(theorem_name)) => {
                    for function_name in contract_refinement_targets(&file, theorem_name) {
                        verification_required_functions(&file, &parsed_sources, &function_name)?;
                    }
                    Some(BTreeSet::new())
                }
                None if file.entry_module().is_some() => Some(
                    file.function_blocks()
                        .iter()
                        .filter(|block| file.function_is_selected(block.signature().name()))
                        .map(|block| block.signature().name().to_string())
                        .collect(),
                ),
                None => None,
            }
        };
        check_verification_deadline()?;
        (
            file,
            parsed_sources,
            selected_functions,
            resource_struct_layouts,
        )
    };
    check_verification_deadline()?;
    let selected_target = file.selected_c_target();
    let selected_thread_runtime = file.selected_thread_runtime();
    let external_and_user_function_blocks = combined_external_function_blocks(&file)?;
    // A sidecar contract names a C function with its ordinary spelling, but a
    // header `static inline` body executes under a translation-unit-qualified
    // name, which is the name its call sites carry and the name the kernel
    // function has. Every termination table the kernel reads is keyed by that
    // executing name, so a helper's own ranked loop is planned where its body
    // runs instead of under a spelling no call graph mentions.
    let termination_kernel_names = executing_function_names(&parsed_sources, &file)?;
    let function_source_registry = Arc::new(
        FunctionSourceRegistry::from_function_blocks(&external_and_user_function_blocks)?
            .with_execution_names(&termination_kernel_names),
    );
    let (termination_plans, requested_termination) = program_function_termination_plans(
        &file,
        selected_functions.as_ref(),
        &termination_kernel_names,
    )?;
    let declared_diverging = external_and_user_function_blocks
        .iter()
        .filter(|function| function.signature().diverges())
        .map(|function| {
            executing_function_name(&termination_kernel_names, function.signature().name())
        })
        .collect::<BTreeSet<_>>();
    let extern_names = external_and_user_function_blocks
        .iter()
        .filter(|function| function.is_external())
        .map(|function| {
            executing_function_name(&termination_kernel_names, function.signature().name())
        })
        .collect::<BTreeSet<_>>();
    // A whole-contract `sorry` is an explicit dev-only assumption, like an
    // external declaration. It contributes neither a body goal nor a checked
    // contract; its existing admission record remains the reported result.
    let admitted_functions = file
        .function_blocks()
        .iter()
        .filter(|function| {
            matches!(function.grouped_proof(), Some(SourceProof::Script(tactics))
            if crate::surface::is_complete_sorry_body(tactics))
        })
        .map(|function| {
            executing_function_name(&termination_kernel_names, function.signature().name())
        })
        .collect::<BTreeSet<_>>();
    let bodyless_declarations = extern_names.union(&admitted_functions).cloned().collect();
    let requested_contracts = requested_termination
        .iter()
        .map(|name| executing_function_name(&termination_kernel_names, name))
        .filter(|name| !admitted_functions.contains(name))
        .collect();

    let standard_library_theorems = standard_library_theorem_definitions()?;
    let (
        predicate_environment,
        click_function_environment,
        resource_environment,
        mut function_environment,
        mut theorem_certification_facts,
        mut theorem_certification_authorities,
        theorem_environment,
        program_contracts,
    ) = {
        let _timing = VerificationTimingPhase::new("environment");
        let predicate_definitions = combined_predicate_definitions(&file)?;
        let click_function_definitions = combined_click_function_definitions(&file)?;
        let resource_definitions = combined_resource_definitions(&file)?;
        let theorem_definitions = selected_theorem_definitions(
            &file,
            selected_functions
                .as_ref()
                .filter(|_| verification_target.is_some() || expansion_capture.is_some()),
            verification_target.as_ref(),
        );
        let selected_theorem_names = theorem_definitions
            .iter()
            .map(|theorem| theorem.name())
            .collect::<BTreeSet<_>>();
        let unselected_theorem_definitions = file
            .theorem_definitions()
            .iter()
            .filter(|theorem| !selected_theorem_names.contains(theorem.name()))
            .map(clone_theorem_definition_iteratively)
            .collect::<Vec<_>>();
        let theorem_dependencies =
            TheoremEnvironment::with_standard_library(&unselected_theorem_definitions)?
                .with_discovery_library(&file)?;
        let predicate_environment = PredicateEnvironment::new(&predicate_definitions)
            .with_contracts(file.contract_definitions(), &file.program_function_names);
        let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
            &click_function_definitions,
            &combined_algebraic_type_definitions(&file)?,
        );
        let spec_definitions =
            SpecDefinitions::new(&predicate_environment, &click_function_environment)
                .with_struct_sizes(&file.struct_sizes);
        let resource_environment = ResourceEnvironment::with_struct_layouts(
            &resource_definitions,
            &resource_struct_layouts,
        );
        // Arm refutation asks what a declared predicate returns at one
        // constructor, at contract lowering, loop heads, back edges and guard
        // prefixes. None of those has a proof script to place an `unfold` in,
        // so the declared bodies are recorded once here, for this
        // verification's kernel session.
        // A pure function application is a term over its argument values and
        // the states its array-ref arguments carry, and a predicate fact a
        // term over its arguments; neither records the ambient memory. A body
        // that read a C object by name would make one such term stand for the
        // object's value before and after a store to it, so those bodies are
        // refused before any body is lowered or recorded.
        reject_pure_bodies_reading_c_objects(
            spec_definitions,
            &file_scope_object_names(click_source, c_sources, selected_target)?,
        )?;
        register_kernel_fold_read_definitions(spec_definitions, &resource_struct_layouts);
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
            spec_definitions,
            &resource_environment,
        )?;
        let modeled_mutex_definitions: BTreeMap<_, _> = if selected_thread_runtime
            == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread
        {
            composite_resource_definitions(&resource_environment, spec_definitions)?
                .into_iter()
                .map(|definition| (definition.name().to_string(), definition))
                .collect()
        } else {
            BTreeMap::new()
        };
        let mut function_environment = initial_function_environment
            .unwrap_or(built_function_environment)
            .with_modeled_pthread_binding(
                (selected_thread_runtime
                    == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread)
                    .then(crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin),
            )
            .with_modeled_mutex_definitions(modeled_mutex_definitions)
            .with_byte_order(selected_target.byte_order());
        // Contracts are declaration interfaces. A selected function receives
        // every well-formed callee contract as a scoped assumption, while its
        // own contract hypothesis supports the existing checked-recursion
        // rule. Only rules for proofs completed below escape the transaction.
        for function_block in file.function_blocks() {
            // A header `static inline` helper's body, and so its contract
            // interface, is keyed by its executing name. Looking it up by the
            // sidecar spelling would leave its callers without its contract
            // until the helper happened to be verified first, so whether a
            // call applied the contract or ran the body would depend on the
            // order of the functions in the sidecar.
            let Some(function) = function_environment
                .get_function(&executing_function_name(
                    &termination_kernel_names,
                    function_block.signature().name(),
                ))
                .cloned()
            else {
                continue;
            };
            let selected = selected_functions
                .as_ref()
                .is_none_or(|selected| selected.contains(function_block.signature().name()));
            if selected {
                if let Some(hypothesis) =
                    crate::kernel::program_recursive_function_contract_hypothesis(function)
                {
                    function_environment =
                        function_environment.with_verified_function_rule(hypothesis);
                }
            } else if let Some(assumption) =
                crate::kernel::program_unselected_function_contract_assumption(function)
            {
                function_environment = function_environment.with_external_function_rule(assumption);
            }
        }
        let program_contracts = crate::kernel::ProgramContractProof::open_ordinary(
            requested_contracts,
            declared_diverging.clone(),
            &bodyless_declarations,
            &function_environment.linked_functions(),
            &termination_plans,
            file.function_blocks()
                .iter()
                .filter(|function| {
                    !function.is_external()
                        && selected_functions
                            .as_ref()
                            .is_none_or(|selected| selected.contains(function.signature().name()))
                })
                .map(|function| {
                    executing_function_name(&termination_kernel_names, function.signature().name())
                })
                .filter(|name| !admitted_functions.contains(name))
                .collect(),
        )
        .map_err(|error| {
            ClickError::new(format!("could not open C recursion declarations: {error}"))
        })?;
        drop(_timing);
        let verified_theorems = verify_theorem_definitions(
            theorem_dependencies,
            &theorem_definitions,
            spec_definitions,
            Some(&function_environment),
            &resource_environment,
            function_source_registry.clone(),
        )
        .map_err(|error| {
            file.entry_module()
                .map_or(error.clone(), |identity| error.with_context(identity))
        })?;
        let _timing = VerificationTimingPhase::new("environment");
        let mut theorem_certification_facts = BTreeMap::<String, Vec<Proposition>>::new();
        let mut theorem_certification_authorities =
            BTreeMap::<String, Vec<KernelVerifiedPureTheorem>>::new();
        record_theorem_certification_authority(
            &verified_theorems,
            &mut theorem_certification_facts,
            &mut theorem_certification_authorities,
        );
        record_assumed_theorem_certification_authority(
            assumed_theorem_certification_authorities(
                &unselected_theorem_definitions,
                spec_definitions,
            )?,
            &mut theorem_certification_facts,
            &mut theorem_certification_authorities,
        );
        let theorem_environment =
            TheoremEnvironment::with_standard_library(file.theorem_definitions())?
                .with_discovery_library(&file)?;
        check_verification_deadline()?;
        (
            predicate_environment,
            click_function_environment,
            resource_environment,
            function_environment,
            theorem_certification_facts,
            theorem_certification_authorities,
            theorem_environment,
            program_contracts,
        )
    };
    let spec_definitions =
        SpecDefinitions::new(&predicate_environment, &click_function_environment)
            .with_struct_sizes(&file.struct_sizes);

    // Frame evidence may look through composite definitions to decide that a
    // call's mutable ranges or a store's written cell cannot touch a loaded
    // pointer inside a composite's footprint. Definitions are file-global, so
    // one guard covers this verification; nothing is published, so a nested
    // composite still needs its `observe(...)` chain before a user's
    // `separate(...)` goal can cite it.
    let _frame_composite_definitions = crate::kernel::arm_frame_composite_definitions(
        composite_resource_definitions(&resource_environment, spec_definitions).unwrap_or_default(),
    );
    check_verification_deadline()?;
    let mut verified = Vec::new();
    let mut termination_loop_rules = BTreeMap::<String, Vec<VerifiedLoopRule>>::new();
    // Imported library proof dependencies are resolved before the contract
    // root completes, once per theorem in this verification.
    let mut checked_standard_library_theorems = BTreeSet::<String>::new();
    let unselected_function_names = selected_functions.as_ref().map(|selected| {
        file.function_blocks()
            .iter()
            .filter(|function| !selected.contains(function.signature().name()))
            .map(|function| function.signature().name().to_string())
            .collect::<Vec<_>>()
    });
    let entry_module = file.entry_module().map(str::to_string);
    let entry_theorem_names = file
        .theorem_definitions()
        .iter()
        .filter(|theorem| file.theorem_is_selected(theorem.name()))
        .map(|theorem| theorem.name().to_string())
        .collect::<Vec<_>>();
    let all_theorem_names = file
        .theorem_definitions()
        .iter()
        .map(|theorem| theorem.name().to_string())
        .collect::<Vec<_>>();
    let all_function_names = file
        .function_blocks()
        .iter()
        .map(|function| function.signature().name().to_string())
        .collect::<Vec<_>>();
    // A named contract may carry the `diverges` marker too. It stands for an
    // implementation nobody here names, so the marker is the declaration that
    // one of them may not return, and a call through such a pointer is
    // admitted divergence in whichever function makes it.
    let diverging_contracts = file
        .contract_definitions()
        .iter()
        .filter(|contract| contract.function_block().signature().diverges())
        .map(|contract| contract.name().to_string())
        .collect::<BTreeSet<_>>();

    let tactic_names = file
        .tactic_definitions()
        .iter()
        .map(|tactic| tactic.name().to_string())
        .collect::<BTreeSet<_>>();
    let mut ordered_function_blocks = file.function_blocks;
    if selected_thread_runtime
        == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread
    {
        let mut create_callers = BTreeSet::new();
        for function_block in &ordered_function_blocks {
            if function_block.is_external() {
                continue;
            }
            if let Some((_, _, parsed)) = parsed_function_for_source_name(
                &parsed_sources,
                function_block.signature().name(),
                Some(function_block.signature()),
            )? && c_statement_calls(parsed)
                .iter()
                .any(|calls| calls.contains("pthread_create"))
            {
                create_callers.insert(function_block.signature().name().to_string());
            }
        }
        ordered_function_blocks
            .sort_by_key(|block| create_callers.contains(block.signature().name()));
    }
    // Name the inputs of every function this file verifies, in the order a
    // whole-file run verifies them, before any proof runs. Naming them when
    // each proof starts would number a function's inputs by how many the
    // functions verified before it in this run had, so a selected unit and
    // the same unit in a whole-file run would name them differently, and
    // a tactic's search order and work with them. A function that cannot be
    // named here reports why when it is verified; an unselected one is not.
    for function_block in &ordered_function_blocks {
        if function_block.is_external() {
            continue;
        }
        if let Ok(Some((_, _, parsed_function))) = parsed_function_for_source_name(
            &parsed_sources,
            function_block.signature().name(),
            Some(function_block.signature()),
        ) {
            let parsed_function = witnessed_function(parsed_function, function_block);
            super::lowering::reserve_input_identities(&parsed_function);
        }
    }
    let mut early_thread_termination_published = false;
    for function_block in ordered_function_blocks {
        crate::surface::enter_ambient_declaration(function_block.signature().name());
        super::diagnostics::enter_rust_spelling(Some(function_block.signature()));
        check_verification_deadline()?;
        // Load-variable origins are first-seen per verified function: an
        // origin minted while verifying an earlier function belongs to a
        // memory DAG this function's effect states never connect to.
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
        if selected_thread_runtime
            == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread
            && !early_thread_termination_published
        {
            let (_, _, parsed) = parsed_function_for_source_name(
                &parsed_sources,
                function_block.signature.name(),
                Some(function_block.signature()),
            )?
            .ok_or_else(|| ClickError::new("modeled pthread caller has no C definition"))?;
            if c_statement_calls(parsed)
                .iter()
                .any(|calls| calls.contains("pthread_create"))
            {
                let partial_rules = function_environment.verified_function_rules();
                let inline_bodies = function_environment.linked_functions();
                let declared_diverging = external_and_user_function_blocks
                    .iter()
                    .filter(|function| function.signature().diverges())
                    .map(|function| {
                        executing_function_name(
                            &termination_kernel_names,
                            function.signature().name(),
                        )
                    })
                    .collect::<BTreeSet<_>>();
                let mut assumed_terminating = external_and_user_function_blocks
                    .iter()
                    .filter(|function| function.is_external())
                    .map(|function| function.signature().name())
                    .chain(
                        unselected_function_names
                            .iter()
                            .flatten()
                            .map(String::as_str),
                    )
                    .map(|name| executing_function_name(&termination_kernel_names, name))
                    .filter(|name| !declared_diverging.contains(name))
                    .collect::<BTreeSet<_>>();
                assumed_terminating
                    .extend(admitted_functions.difference(&declared_diverging).cloned());
                assumed_terminating.extend(closure_instance_names(&parsed_sources));
                assumed_terminating.extend(object_coercion_names(&parsed_sources));
                assumed_terminating.extend(modeled_thread_runtime_names());
                let preliminary = program_contracts
                    .bootstrap_termination_rules(crate::kernel::ProgramTerminationInputs {
                        independent: crate::kernel::IndependentTerminationInputs {
                            rules: &partial_rules,
                            bodies: &inline_bodies,
                        },
                        plans: &termination_plans,
                        assumed_terminating: &assumed_terminating,
                        diverging_contracts: &diverging_contracts,
                        has_unselected_functions: false,
                    })
                    .map_err(|error| {
                        ClickError::new(format!(
                            "could not certify C termination before pthread create: {error}"
                        ))
                    })?;
                function_environment = function_environment
                    .with_verified_function_termination_rules(preliminary.rules);
                early_thread_termination_published = true;
            }
        }
        // This outer span makes otherwise-unclassified proof orchestration
        // visible at an interrupted project deadline. Nested tactic and
        // certification spans take precedence in the active-work state.
        let _verifier_core_timing = VerificationTimingPhase::new("verifier-core");
        // The entry model of each declared binder is what `old(c.rank)` names,
        // and the registry that lets a refusal spell it that way is per
        // verification, like the load-origin epoch above. One insert per field
        // of each binder this function declares.
        crate::surface::lowering::register_entry_model_fields(&function_block);
        let function_timing_start = std::time::Instant::now();
        let (_, source_path, parsed_function) = parsed_function_for_source_name(
            &parsed_sources,
            function_block.signature.name(),
            Some(function_block.signature()),
        )?
        .ok_or_else(|| {
            ClickError::new(format!(
                "`{}` is not defined by any `verifying` source",
                function_block.signature.name()
            ))
        })?;
        check_signature(
            &function_block.signature,
            function_block.witness_count(),
            parsed_function,
            source_path,
        )?;
        let parsed_function = &*witnessed_function(parsed_function, &function_block);
        validate_region_proof_clauses(&function_block, parsed_function)?;
        // Dev-only `sorry`: a contract proved entirely by `sorry` is
        // admitted without checking, like an `extern` declaration. Callers
        // keep using its declared contract. Requires
        // `click verify --allow-sorry` (enforced at parse); the admission is
        // recorded for loud reporting, never produces a kernel theorem, and
        // is rejected by audit/expand and the gate.
        if let Some(grouped_proof) = function_block.grouped_proof()
            && let SourceProof::Script(tactics) = grouped_proof
        {
            if crate::surface::is_complete_sorry_body(tactics) {
                if !sorry_is_allowed() {
                    return Err(ClickError::new(format!(
                        "`{}` uses `sorry`, which requires `click verify --allow-sorry`; it is a dev-only proof hole and never verifies in the gate",
                        function_block.signature.name()
                    )));
                }
                record_sorry_admission(
                    function_block.contract_claim_label(),
                    source_path.to_string(),
                );
                continue;
            }
            if crate::surface::sorry_outside_have_bodies(tactics) {
                return Err(ClickError::new(format!(
                    "`{}` uses `sorry` outside a `have` body; `sorry` is only allowed as a complete contract proof body or a complete `have` body",
                    function_block.signature.name()
                )));
            }
        }
        let function_source_registry = Arc::new(
            function_source_registry
                .for_contract_proof()
                .with_program(program_contracts.bodies()),
        );
        let mut verification_function_environment = function_environment.clone();
        if function_environment.has_conditional_resource_effects() {
            verification_function_environment =
                verification_function_environment.with_conditional_resource_cases();
        }
        let implicit_safety_clause = EnsureClause {
            proof_bindings: Vec::new(),
            name: None,
            ensure: Ensure::Proposition(ClickProposition::Comparison {
                left: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0))),
            }),
            proof: SourceProof::Tactic(SmartTactic::ImplicitTail),
            borrowed: false,
            condition: None,
        };
        let mut claims = function_claims(&function_block);
        let has_explicit_claims = !claims.is_empty();
        if !has_explicit_claims {
            claims.push(FunctionClaimRef::Ensure(0, &implicit_safety_clause));
        }
        let mut function_verified = Vec::new();
        // Claims with their own `by` are proved one by one below; every other
        // claim, or the body-safety claim of a contract without any, is
        // proved together by the covering proof from one execution.
        let (claims, covered_claims): (Vec<_>, Vec<_>) =
            if function_block.covering_proof().is_some() {
                claims.into_iter().partition(|claim| {
                    has_explicit_claims && !function_block.covers_claim_proof(claim.proof())
                })
            } else {
                (claims, Vec::new())
            };
        if let Some(grouped_proof) = function_block.covering_proof() {
            let theorems = match grouped_proof {
                SourceProof::Tactic(SmartTactic::ImplicitTail) => prove_claims_by_implicit_tail(
                    expansion_capture.as_deref_mut(),
                    source_path,
                    &function_block,
                    parsed_function,
                    &covered_claims,
                    &verification_function_environment,
                    spec_definitions,
                    &resource_environment,
                    &theorem_environment,
                    function_source_registry.clone(),
                )?,
                SourceProof::Script(tactics) => prove_claims_by_grouped_script(
                    expansion_capture.as_deref_mut(),
                    source_path,
                    &function_block,
                    parsed_function,
                    &covered_claims,
                    &verification_function_environment,
                    spec_definitions,
                    &resource_environment,
                    &theorem_environment,
                    function_source_registry.clone(),
                    tactics,
                )
                .map_err(|error| {
                    if function_block.is_tactic_procedure() {
                        error.with_context(format!(
                            "tactic `{}`: its proof must end with every produced instance held \
                             and every `ensures` an available fact",
                            function_block.signature().name()
                        ))
                    } else {
                        error
                    }
                })?,
                SourceProof::Default | SourceProof::Tactic(SmartTactic::Solve) => {
                    return Err(ClickError::new(format!(
                        "grouped proof for `{}` must be an explicit `by {{ ... }}` proof script; omit it to prove the claims with the implicit tail",
                        function_block.signature().name()
                    )));
                }
            };
            function_verified.extend(theorems.iter().cloned());
            verified.extend(theorems);
        }
        {
            for claim in claims {
                let claim_label = if has_explicit_claims {
                    function_claim_label(&function_block, &claim)
                } else {
                    claim_labels::body_safety_label(function_block.signature.name())
                };
                let theorems = match claim.proof() {
                    SourceProof::Default | SourceProof::Tactic(SmartTactic::ImplicitTail) => {
                        prove_claim_by_implicit_tail(
                            expansion_capture.as_deref_mut(),
                            source_path,
                            &function_block,
                            parsed_function,
                            &claim,
                            &claim_label,
                            &verification_function_environment,
                            spec_definitions,
                            &resource_environment,
                            &theorem_environment,
                            function_source_registry.clone(),
                        )?
                    }
                    SourceProof::Tactic(SmartTactic::Solve) => prove_claim_by_solve(
                        expansion_capture.as_deref_mut(),
                        source_path,
                        &function_block,
                        parsed_function,
                        &claim,
                        &claim_label,
                        &verification_function_environment,
                        spec_definitions,
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
                        spec_definitions,
                        &resource_environment,
                        &theorem_environment,
                        function_source_registry.clone(),
                        tactics,
                    )?,
                };
                function_verified.extend(theorems.iter().cloned());
                // A targeted body-safety proof must remain available to source
                // expansion even though it has no written postcondition.
                if has_explicit_claims || verification_target.is_some() {
                    verified.extend(theorems);
                }
            }
        }
        // Discharge the proof's imported theorem dependencies before closing
        // its parent root. Registration receives no pending dependency checks.
        let mut dependencies = BTreeSet::new();
        collect_function_theorem_dependencies(&function_block, &mut dependencies);
        let mut read_proof_texts = BTreeSet::new();
        for theorem in &function_verified {
            if let Some(tactics) = &theorem.proof_tactics
                && read_proof_texts.insert(Arc::as_ptr(tactics) as *const ProofTactic)
            {
                collect_applied_theorems(tactics, &mut dependencies);
            }
        }
        for name in dependencies {
            if !theorem_certification_facts.contains_key(&name)
                && checked_standard_library_theorems.insert(name.clone())
                && let Some(index) = standard_library_theorem_index(&name)
                && theorem_has_certification_binders(&standard_library_theorems[index])
            {
                let dependency = verify_theorem_definitions(
                    TheoremEnvironment::with_full_library_prefix(index, &[])?,
                    &standard_library_theorems[index..=index],
                    spec_definitions,
                    None,
                    &resource_environment,
                    function_source_registry.clone(),
                )?;
                record_theorem_certification_authority(
                    &dependency,
                    &mut theorem_certification_facts,
                    &mut theorem_certification_authorities,
                );
            }
        }
        // The parent is an ordinary proof root opened with the entry. Child
        // scripts have already joined their own checked completions into it.
        let body_proof =
            crate::surface::proof::finish_contract_body_root(&function_block, &function_verified)?;
        let executing_name =
            executing_function_name(&termination_kernel_names, function_block.signature().name());
        termination_loop_rules
            .entry(executing_name)
            .or_default()
            .extend_from_slice(body_proof.loop_rules());
        if let Some(rule) = body_proof.to_reusable_rule() {
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
    // What follows is about the whole run, not the last function verified.
    crate::surface::clear_ambient_proof_source();

    let assumed_unselected_names = unselected_function_names.clone().unwrap_or_default();
    if let Some(unselected) = unselected_function_names {
        for function_name in unselected {
            // A `static` function's rule is keyed by its executing name,
            // which a retained session's environment carries over from the
            // run that verified it.
            let executing_name = executing_function_name(&termination_kernel_names, &function_name);
            function_environment = function_environment
                .without_verified_function_rule(&function_name)
                .without_verified_function_rule(&executing_name)
                .without_external_function_rule(&function_name);
        }
    }
    let partial_rules = function_environment.verified_function_rules();
    // An unselected function is an assumption here, a `static inline` one
    // too: its loops are ranked by the run that selects it, so its body is
    // not analyzed without the loop rules only that run verifies.
    let unselected_executing_names = assumed_unselected_names
        .iter()
        .map(|name| executing_function_name(&termination_kernel_names, name))
        .collect::<BTreeSet<_>>();
    let inline_bodies = function_environment
        .linked_functions()
        .into_iter()
        .filter(|function| !unselected_executing_names.contains(function.name()))
        .collect::<Vec<_>>();
    // A callee outside the verified set is an assumption, as its postconditions are:
    // an external contract always, and an unselected function because it owes
    // termination evidence to the run that does select it.
    let mut assumed_terminating = external_and_user_function_blocks
        .iter()
        .filter(|function| function.is_external())
        .map(|function| function.signature().name())
        .chain(assumed_unselected_names.iter().map(String::as_str))
        .map(|name| executing_function_name(&termination_kernel_names, name))
        .filter(|name| !declared_diverging.contains(name))
        .collect::<BTreeSet<_>>();
    assumed_terminating.extend(admitted_functions.difference(&declared_diverging).cloned());
    assumed_terminating.extend(closure_instance_names(&parsed_sources));
    assumed_terminating.extend(object_coercion_names(&parsed_sources));
    if selected_thread_runtime
        == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread
    {
        assumed_terminating.extend(modeled_thread_runtime_names());
    }
    let generated_program = program_contracts
        .generate_termination(crate::kernel::ProgramTerminationInputs {
            independent: crate::kernel::IndependentTerminationInputs {
                rules: &partial_rules,
                bodies: &inline_bodies,
            },
            plans: &termination_plans,
            assumed_terminating: &assumed_terminating,
            diverging_contracts: &diverging_contracts,
            has_unselected_functions: !unselected_executing_names.is_empty(),
        })
        .map_err(|failure| program_contract_failure(failure, &declared_diverging, &tactic_names))?;
    let (proved_program, _termination_certificate) = super::proof::program_termination::prove(
        generated_program,
        file.termination_proof.as_deref(),
        SpecDefinitions::new(&predicate_environment, &click_function_environment),
        &theorem_environment,
        &tactic_names,
    )?;
    super::expansion::record_termination_certificate(&_termination_certificate);
    let completed_program = proved_program.complete();
    function_environment = function_environment
        .with_verified_function_termination_rules(completed_program.into_termination_rules());

    if let Some(identity) = c_sources.prepared_project_identity() {
        for theorem in &mut verified {
            theorem.import_identity = Some(identity.to_string());
        }
    }
    let artifact_identity = c_sources.artifact_identity_with_runtime(
        click_source,
        selected_target,
        selected_thread_runtime,
    );
    let selected_proofs = match verification_target.as_ref() {
        Some(VerificationTarget::Theorem(name)) => vec![format!("theorem:{name}")],
        Some(VerificationTarget::Function(name)) => vec![format!("function:{name}")],
        Some(VerificationTarget::Functions(names)) => names
            .iter()
            .map(|name| format!("function:{name}"))
            .collect(),
        None if expansion_capture.is_some() => selected_functions
            .as_ref()
            .into_iter()
            .flatten()
            .map(|name| format!("function:{name}"))
            .collect(),
        None => entry_theorem_names
            .iter()
            .map(|name| format!("theorem:{name}"))
            .chain(
                all_function_names
                    .iter()
                    .filter(|name| {
                        selected_functions
                            .as_ref()
                            .is_none_or(|selected| selected.contains(*name))
                    })
                    .map(|name| format!("function:{name}")),
            )
            .collect(),
    };
    let selected_theorems = selected_proofs
        .iter()
        .filter_map(|proof| proof.strip_prefix("theorem:").map(str::to_string))
        .collect::<BTreeSet<_>>();
    let selected_function_names = selected_proofs
        .iter()
        .filter_map(|proof| proof.strip_prefix("function:").map(str::to_string))
        .collect::<BTreeSet<_>>();
    let selection = ProofSelection {
        entry_module,
        selected_proofs: selected_proofs.clone(),
        assumed_theorems: all_theorem_names
            .iter()
            .filter(|name| !selected_theorems.contains(*name))
            .cloned()
            .collect(),
        assumed_functions: all_function_names
            .iter()
            .filter(|name| !selected_function_names.contains(*name))
            .cloned()
            .collect(),
        runtime_assumptions: selected_thread_runtime
            .assumption()
            .map(|assumption| vec![assumption.to_string()])
            .unwrap_or_default(),
        // `parse_verified_sources_context` has already validated the selected
        // built-in or locked declarations, their types, and every call shape.
        modeled_pthread_binding: (selected_thread_runtime
            == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread)
            .then(crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin),
    };
    for theorem in &mut verified {
        theorem.artifact_identity = Some(artifact_identity);
        theorem.target = selected_target;
        theorem.selection = Some(selection.clone());
    }
    // Recorded work charges tactic budgets without interrupting the tactic,
    // so a budget can be exhausted by a step that then returns; its pending
    // limit fails the run here at the latest.
    check_verification_deadline()?;
    Ok((verified, function_environment))
}

pub(in crate::surface) fn tactic_expansion_required_functions(
    file: &ClickFile,
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
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
            .filter(|function| file.function_is_selected(function.signature().name()))
            .map(|function| function.signature().name().to_string())
            .collect());
    };
    let _tactic_index = tactic_index.ok_or_else(|| {
        ClickError::new(format!(
            "whole-proof capture is not supported for function claim {}",
            claim.describe()
        ))
    })?;
    let function_block = file
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == function_name)
        .ok_or_else(|| ClickError::new(format!("unknown function `{function_name}`")))?;
    let _tactics = match claim {
        ContractProofClaim::Grouped => function_block
            .grouped_proof()
            .and_then(SourceProof::tactics),
        ContractProofClaim::Ensure(index) => function_block
            .ensures()
            .get(index)
            .and_then(|clause| clause.proof().tactics()),
        ContractProofClaim::ExceptionalEnsure(index) => function_block
            .exceptional_ensures()
            .get(index)
            .and_then(|clause| clause.proof().tactics()),
    }
    .ok_or_else(|| {
        ClickError::new(format!(
            "selected {} proof for `{function_name}` is not an explicit tactic script",
            claim.describe()
        ))
    })?;
    let Some((kernel_name, _, parsed)) = parsed_function_for_source_name(
        parsed_sources,
        &function_name,
        Some(function_block.signature()),
    )?
    else {
        return Err(ClickError::new(format!(
            "no C source defines `{function_name}`"
        )));
    };
    let mut required = BTreeSet::new();
    // Expansion checks exactly the selected proof unit. Called-function
    // contracts are interfaces and do not select their implementations.
    required.insert(kernel_name.clone());
    required.insert(function_name);
    if file.selected_thread_runtime()
        == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread
    {
        required.extend(modeled_pthread_create_workers(parsed));
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
    let source_map = ProgramSourceContext::bundle(c_sources);
    let file = parse_click_file_with_c_sources(click_source, c_sources)?;
    let parsed_sources = parse_verified_sources_context(&file, &source_map)?;
    let required = tactic_expansion_required_functions(
        &file,
        &parsed_sources,
        (site.clone(), Some(tactic_index)),
    )?;
    if required.len() <= 1 {
        return Ok(None);
    }

    let root_kernel_name = parsed_function_for_source_name(
        &parsed_sources,
        function_name,
        file.function_blocks()
            .iter()
            .find(|block| block.signature().name() == function_name)
            .map(FunctionBlock::signature),
    )?
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
        for dependency in c_statement_calls(function)
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
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    function_name: &str,
) -> Result<BTreeSet<String>, ClickError> {
    let function_blocks = combined_external_function_blocks(file)?;
    verification_required_functions_with_blocks(
        parsed_sources,
        function_name,
        &function_blocks,
        file.selected_thread_runtime(),
    )
}

fn verification_required_functions_with_blocks(
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    function_name: &str,
    function_blocks: &[FunctionBlock],
    runtime: crate::languages::c::thread_runtime::CThreadRuntime,
) -> Result<BTreeSet<String>, ClickError> {
    required_functions(
        parsed_sources,
        function_name,
        function_blocks,
        runtime,
        None,
    )
}

/// What the assumption report's closure walk records beside the closure.
struct AssumptionWalk<'a> {
    /// The allocator functions the closure calls.
    allocator: &'a mut BTreeSet<&'static str>,
    /// Every `extern` function, by name.
    externals: &'a BTreeMap<String, ModelFamily>,
}

/// The closure [`verification_required_functions_with_blocks`] computes.
/// With `report`, the walk also records the allocator functions the closure
/// calls and follows the calls of a body a typed frontend lowered itself, so
/// that a C++ or Rust function's library interfaces are reported.
fn required_functions(
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    function_name: &str,
    function_blocks: &[FunctionBlock],
    runtime: crate::languages::c::thread_runtime::CThreadRuntime,
    mut report: Option<AssumptionWalk<'_>>,
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
    let mut pending = if let Some((kernel_name, _, _)) = parsed_function_for_source_name(
        parsed_sources,
        function_name,
        function_blocks
            .iter()
            .find(|block| block.signature().name() == function_name)
            .map(FunctionBlock::signature),
    )? {
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
        if runtime == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread
            && (crate::languages::c::thread_runtime::is_modeled_pthread_function(&name)
                || crate::languages::c::thread_runtime::is_publication_operation(&name))
        {
            continue;
        }
        let Some(parsed) = parsed_sources.get(&name).map(|entry| &entry.1) else {
            if function_blocks
                .iter()
                .any(|function| function.is_external() && function.signature().name() == name)
            {
                continue;
            }
            if crate::languages::c::thread_runtime::is_publication_operation(&name) {
                return Err(ClickError::new(format!(
                    "`{name}` is declared by Click's `<stdatomic.h>` projection, but only the modeled-pthread thread runtime models C11 atomic operations"
                )));
            }
            return Err(ClickError::new(format!("no C source defines `{name}`")));
        };
        let Some(report) = report.as_mut() else {
            pending.extend(c_statement_calls(parsed).into_iter().flatten());
            continue;
        };
        pending.extend(
            c_statement_calls_recording(parsed, report.allocator)
                .into_iter()
                .flatten(),
        );
        if let Some(lowered) = parsed.prelowered_kernel_function() {
            pending.extend(
                crate::kernel::program_function_callees(lowered)
                    .into_iter()
                    .filter(|callee| {
                        parsed_sources.contains_key(callee) || report.externals.contains_key(callee)
                    }),
            );
        }
    }
    required.insert(function_name.to_string());
    Ok(required)
}

/// Returns the external C assumptions in each user function's transitive C
/// call closure. This is intentionally derived from the same call graph used
/// by targeted verification, so reporting cannot silently omit a transitive
/// external callee.
pub fn c_external_dependencies(
    click_source: &str,
    c_sources: &[(&str, &str)],
) -> Result<BTreeMap<String, Vec<String>>, ClickError> {
    let sources = ProgramSourceContext::bundle(c_sources);
    external_dependencies_context(click_source, &sources)
}

/// What `click verify` reports about a project beside its verdict, from one
/// resolution of its sources: the external contracts each selected function
/// relies on, and how many proof units are selected.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct ProjectVerificationSummary {
    /// Each function's assumed library interfaces and `extern` contracts.
    pub assumptions: BTreeMap<String, Vec<ModelAssumption>>,
    /// Selected function proofs plus selected theorems.
    pub selected_proof_count: usize,
    /// Every function the sidecar's `verifying` sources define, with the
    /// source that defines it. A sibling sidecar of the same project may not
    /// assume one of these through an `extern` declaration: each sidecar is
    /// verified alone, so nothing would reconcile the assumed contract with
    /// the verified one, and termination ranks only calls whose callee has a
    /// body in the same sidecar.
    pub defined_functions: BTreeMap<String, String>,
    /// The `extern` functions this sidecar itself declares (the standard
    /// library's declarations are not its assumptions to reconcile).
    pub external_declarations: BTreeSet<String>,
}

fn project_verification_summary_file(
    file: &ClickFile,
    sources: &ProgramSourceContext<'_>,
) -> Result<ProjectVerificationSummary, ClickError> {
    // The summary reads function names and call graphs, never `main`'s
    // program-entry storage, so it does not build it.
    let parsed_sources =
        parse_verified_sources_context_with_entry(file, sources, ProgramEntryStorage::Skip)?;
    Ok(ProjectVerificationSummary {
        assumptions: program_assumptions_parsed(file, &parsed_sources, sources.library_models())?,
        selected_proof_count: file
            .function_blocks()
            .iter()
            .filter(|function| file.function_is_selected(function.signature().name()))
            .count()
            + file
                .theorem_definitions()
                .iter()
                .filter(|theorem| file.theorem_is_selected(theorem.name()))
                .count(),
        defined_functions: parsed_sources
            .iter()
            .map(|(name, (source_path, _))| (name.clone(), source_path.clone()))
            .collect(),
        external_declarations: file
            .function_blocks()
            .iter()
            .filter(|function| function.is_external())
            .map(|function| function.signature().name().to_string())
            .collect(),
    })
}

pub fn project_summary(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
) -> Result<ProjectVerificationSummary, ClickError> {
    // The run's budget charges the summary's work, so it gets its own kernel
    // session: what this thread verified before cannot change its units.
    let _session = crate::kernel::VerificationSession::enter();
    let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
    let file = resolve_click_project_context(project, &sources)?;
    project_verification_summary_file(&file, &sources)
}

/// A summary and a verification of one loaded project from a single
/// resolution of its sources. The outer error is the summary's, a failure to
/// resolve or summarize the sources; the inner result is verification's.
pub type SummarizedVerification = Result<
    (
        ProjectVerificationSummary,
        Result<Vec<VerifiedProgramTheorem>, ClickError>,
    ),
    ClickError,
>;

/// [`project_summary`] then [`verify_c_project`], resolving the sources
/// once for both: the resolution validates every declaration, standard
/// library included, so a caller reporting the summary should not pay twice.
pub fn verify_project_with_summary(
    project: &ClickProject,
    inputs: &ProgramInputs<'_>,
) -> SummarizedVerification {
    let sources = ProgramSourceContext::of(inputs)?.with_click_project(project);
    summarize_then_verify(
        project,
        &sources,
        matches!(inputs, ProgramInputs::Bundle(_)),
    )
}

fn summarize_then_verify(
    project: &ClickProject,
    sources: &ProgramSourceContext<'_>,
    emit_timing_failure: bool,
) -> SummarizedVerification {
    // As in the separate summary: the CLI's phase name, which a stop report
    // cites, and its own kernel session, so what this thread verified before
    // cannot change its units. The resolved file holds no session state; the
    // separate verification entry points also resolve before verification
    // enters its session.
    let (file, summary) = {
        let _phase = instrumentation::VerificationPhase::new("external dependency summary");
        let _session = crate::kernel::VerificationSession::enter();
        let file = resolve_click_project_context(project, sources)?;
        let summary = project_verification_summary_file(&file, sources)?;
        (file, summary)
    };
    let verified = instrumentation::with_default_tactic_limits(|| {
        let result = verify_program_with_context(
            project.entry_source().expect("resolved entry source"),
            sources,
            None,
            None,
            None,
            Some(file),
        )
        .map(|(verified, _)| verified);
        if emit_timing_failure && let Err(error) = &result {
            error.emit_timing_failure();
        }
        result
    });
    Ok((summary, verified))
}

/// Reports the same explicit external-contract assumptions for compiler imports.
pub fn c_prepared_external_dependencies(
    click_source: &str,
    imports: &[PreparedCImport],
) -> Result<BTreeMap<String, Vec<String>>, ClickError> {
    let sources = ProgramSourceContext::prepared(imports);
    external_dependencies_context(click_source, &sources)
}

fn external_dependencies_context(
    click_source: &str,
    sources: &ProgramSourceContext<'_>,
) -> Result<BTreeMap<String, Vec<String>>, ClickError> {
    let layouts = parse_c_layouts(click_source, sources)?;
    let file = parser::parse_with_layouts_and_aggregate_objects(
        &sources.with_library_contracts(click_source),
        layouts,
    )?;
    external_dependencies_file(&file, sources)
}

fn external_dependencies_file(
    file: &ClickFile,
    sources: &ProgramSourceContext<'_>,
) -> Result<BTreeMap<String, Vec<String>>, ClickError> {
    // The summary reads function names and call graphs, never `main`'s
    // program-entry storage, so it does not build it.
    let parsed_sources =
        parse_verified_sources_context_with_entry(file, sources, ProgramEntryStorage::Skip)?;
    Ok(
        program_assumptions_parsed(file, &parsed_sources, sources.library_models())?
            .into_iter()
            .filter_map(|(function, assumptions)| {
                let external = assumptions
                    .into_iter()
                    .filter(|assumption| assumption.family != ModelFamily::Allocator)
                    .map(|assumption| assumption.name)
                    .collect::<Vec<_>>();
                (!external.is_empty()).then_some((function, external))
            })
            .collect(),
    )
}

/// Where the contract a verification assumes for code Click does not verify
/// comes from. `docs/concepts/trust.md` lists each family.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ModelFamily {
    /// An `extern` contract a sidecar declares.
    Extern,
    /// A C library contract in `library/c/`.
    CLibrary,
    /// The C allocator the kernel models: `malloc`, `calloc`, `realloc`
    /// and `free`.
    Allocator,
    /// The contract the C front end writes for one `snprintf` format.
    Snprintf,
    /// The contract the C front end writes for a literal `printf` or `fprintf`.
    Printf,
    Fprintf,
    /// A C++ standard-library catalog contract.
    CppStd,
    /// A Rust core-method contract.
    RustCore,
    /// The contract of a verifier primitive in `library/c/builtins.click`:
    /// the value of `__builtin_constant_p`.
    Primitive,
}

impl ModelFamily {
    /// Every family a function's assumptions can belong to; the thread
    /// runtime, which a whole verification assumes, is reported apart.
    pub const ALL: [Self; 9] = [
        Self::Extern,
        Self::CLibrary,
        Self::Allocator,
        Self::Snprintf,
        Self::Printf,
        Self::Fprintf,
        Self::CppStd,
        Self::RustCore,
        Self::Primitive,
    ];

    /// The tag `click verify` prints before the family's names.
    pub fn label(self) -> &'static str {
        match self {
            Self::Extern => "extern",
            Self::CLibrary => "C library",
            Self::Allocator => "allocator",
            Self::Snprintf => "snprintf",
            Self::Printf => "printf",
            Self::Fprintf => "fprintf",
            Self::CppStd => "C++ std",
            Self::RustCore => "Rust core",
            Self::Primitive => "primitive",
        }
    }
}

/// One contract a verified function relies on without Click verifying it.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ModelAssumption {
    pub family: ModelFamily,
    /// The function's name as its contract declares it.
    pub name: String,
}

impl ModelAssumption {
    /// How a report names the model: a formatted-output function by its
    /// format, `"%s"`, and any other by its name.
    pub fn display(&self) -> String {
        match crate::languages::c::formatted_output::function_format(&self.name) {
            Some((_, format)) => {
                format!("\"{}\"", String::from_utf8_lossy(&format).escape_default())
            }
            None => self.name.clone(),
        }
    }
}

/// Each function's assumptions, from the call closure targeted verification
/// already computes: the `extern` contracts it reaches, tagged by where each
/// comes from, and the allocator functions its closure calls.
fn program_assumptions_parsed(
    file: &ClickFile,
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    library_models: Option<&BTreeSet<String>>,
) -> Result<BTreeMap<String, Vec<ModelAssumption>>, ClickError> {
    let function_blocks = combined_external_function_blocks(file)?;
    // The standard library's blocks lead the combined list.
    let library_blocks = super::validation::file_library(file)?
        .function_blocks()
        .len();
    let frontend_family = match file.source_language() {
        crate::languages::SourceLanguage::Rust => ModelFamily::RustCore,
        _ => ModelFamily::CppStd,
    };
    let external_families = function_blocks
        .iter()
        .enumerate()
        .filter(|(_, function)| function.is_external())
        .map(|(index, function)| {
            let name = function.signature().name();
            let family = if index < library_blocks {
                if name == syntax::CONSTANT_P_UNKNOWN {
                    ModelFamily::Primitive
                } else {
                    ModelFamily::CLibrary
                }
            } else if let Some((function, _)) =
                crate::languages::c::formatted_output::function_format(name)
            {
                use crate::languages::c::formatted_output::FormattedOutput;
                match function {
                    FormattedOutput::Snprintf => ModelFamily::Snprintf,
                    FormattedOutput::Printf => ModelFamily::Printf,
                    FormattedOutput::Fprintf => ModelFamily::Fprintf,
                }
            } else if library_models.is_some_and(|models| models.contains(name)) {
                frontend_family
            } else {
                ModelFamily::Extern
            };
            (name.to_string(), family)
        })
        .collect::<BTreeMap<_, _>>();
    let mut assumptions = BTreeMap::new();
    for function in file
        .function_blocks()
        .iter()
        .filter(|function| !function.is_external())
    {
        let mut allocator = BTreeSet::new();
        let required = required_functions(
            parsed_sources,
            function.signature().name(),
            &function_blocks,
            file.selected_thread_runtime(),
            Some(AssumptionWalk {
                allocator: &mut allocator,
                externals: &external_families,
            }),
        )?;
        let mut assumed = required
            .iter()
            .filter_map(|name| {
                external_families.get(name).map(|family| ModelAssumption {
                    family: *family,
                    name: name.clone(),
                })
            })
            .chain(allocator.into_iter().map(|name| ModelAssumption {
                family: ModelFamily::Allocator,
                name: name.to_string(),
            }))
            .collect::<Vec<_>>();
        if !assumed.is_empty() {
            assumed.sort();
            assumptions.insert(function.signature().name().to_string(), assumed);
        }
    }
    Ok(assumptions)
}

/// The allocator function `name` names, which the C front end models as an
/// allocation rather than a call.
fn c_allocator_function(name: &str) -> Option<&'static str> {
    ["malloc", "calloc", "realloc", "free"]
        .into_iter()
        .find(|function| *function == name)
}

/// The functions the modeled-pthread runtime specifies instead of executing:
/// assumed to terminate, since the trusted specification stands in for them.
fn modeled_thread_runtime_names() -> impl Iterator<Item = String> {
    use crate::languages::c::thread_runtime::{MODELED_PTHREAD_FUNCTIONS, PUBLICATION_OPERATIONS};
    MODELED_PTHREAD_FUNCTIONS
        .into_iter()
        .chain(PUBLICATION_OPERATIONS)
        .map(str::to_string)
}

fn modeled_pthread_create_workers(
    function: &crate::languages::interface::ImportedFunction,
) -> BTreeSet<String> {
    use syntax::{CExpression as E, CStatement as S};
    let mut workers = BTreeSet::new();
    let mut pending = vec![function.body()];
    while let Some(statement) = pending.pop() {
        match statement {
            S::Call {
                function_name,
                arguments,
                ..
            }
            | S::CallResult {
                function_name,
                arguments,
                ..
            } if function_name == "pthread_create" => {
                if let Some(E::FunctionAddress(name)) = arguments.get(2) {
                    workers.insert(name.clone());
                }
            }
            S::Label { statement, .. } => pending.push(statement),
            S::Seq(first, second) => {
                pending.push(second);
                pending.push(first);
            }
            S::If {
                then_branch,
                else_branch,
                ..
            } => {
                pending.push(else_branch);
                pending.push(then_branch);
            }
            S::While { test, body, .. } | S::DoWhile { test, body, .. } => {
                pending.push(body);
                if let Some(test) = test {
                    pending.push(test);
                }
            }
            S::For {
                initializer,
                step,
                body,
                ..
            } => {
                pending.push(step);
                pending.push(body);
                pending.push(initializer);
            }
            S::Switch { cases, .. } => {
                pending.extend(cases.iter().map(|case| case.body()));
            }
            _ => {}
        }
    }
    workers
}

fn with_modeled_pthread_workers(
    file: &ClickFile,
    mut selected: BTreeSet<String>,
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    runtime: crate::languages::c::thread_runtime::CThreadRuntime,
) -> Result<BTreeSet<String>, ClickError> {
    if runtime == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread {
        let mut workers = BTreeSet::new();
        for name in &selected {
            if let Some((_, _, parsed)) = parsed_function_for_source_name(
                parsed_sources,
                name,
                file.function_blocks()
                    .iter()
                    .find(|block| block.signature().name() == name)
                    .map(FunctionBlock::signature),
            )? {
                workers.extend(modeled_pthread_create_workers(parsed));
            }
        }
        selected.extend(workers);
    }
    Ok(selected)
}

pub(in crate::surface) fn c_statement_calls(
    function: &crate::languages::interface::ImportedFunction,
) -> Vec<BTreeSet<String>> {
    c_statement_calls_recording(function, &mut BTreeSet::new())
}

/// [`c_statement_calls`], also recording in `allocator` each allocator
/// function the body calls, which is not a call dependency.
fn source_struct_names(
    bindings: &BTreeMap<crate::kernel::BindingName, String>,
) -> BTreeMap<String, String> {
    let mut names: BTreeMap<String, Option<String>> = BTreeMap::new();
    for (binding, ty) in bindings {
        let Some(spelling) = binding
            .reference_referent()
            .unwrap_or(binding)
            .source_spelling()
        else {
            continue;
        };
        names
            .entry(spelling.to_owned())
            .and_modify(|previous| {
                if previous.as_ref() != Some(ty) {
                    *previous = None;
                }
            })
            .or_insert_with(|| Some(ty.clone()));
    }
    names
        .into_iter()
        .filter_map(|(name, ty)| Some((name, ty?)))
        .collect()
}

fn c_statement_calls_recording(
    function: &crate::languages::interface::ImportedFunction,
    allocator: &mut BTreeSet<&'static str>,
) -> Vec<BTreeSet<String>> {
    fn collect_function_pointer_names(
        statement: &syntax::CStatement,
        names: &mut BTreeSet<String>,
    ) {
        match statement {
            syntax::CStatement::Declare {
                interface_type: crate::languages::interface::InterfaceType::FunctionPointer(_),
                name,
                ..
            } => {
                names.insert(name.source_name().to_owned());
            }
            syntax::CStatement::Seq(first, second) => {
                collect_function_pointer_names(first, names);
                collect_function_pointer_names(second, names);
            }
            syntax::CStatement::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_function_pointer_names(then_branch, names);
                collect_function_pointer_names(else_branch, names);
            }
            syntax::CStatement::While { test, body, .. }
            | syntax::CStatement::DoWhile { test, body, .. } => {
                collect_function_pointer_names(body, names);
                if let Some(test) = test {
                    collect_function_pointer_names(test, names);
                }
            }
            syntax::CStatement::For {
                test,
                initializer,
                step,
                body,
                ..
            } => {
                collect_function_pointer_names(initializer, names);
                collect_function_pointer_names(body, names);
                collect_function_pointer_names(step, names);
                if let Some(test) = test {
                    collect_function_pointer_names(test, names);
                }
            }
            syntax::CStatement::Switch { cases, .. } => {
                for case in cases {
                    collect_function_pointer_names(case.body(), names);
                }
            }
            syntax::CStatement::Label { statement, .. } => {
                collect_function_pointer_names(statement, names)
            }
            syntax::CStatement::EndAggregateLifetimes { .. }
            | syntax::CStatement::FillArrayTail { .. }
            | syntax::CStatement::Skip
            | syntax::CStatement::Break
            | syntax::CStatement::Continue
            | syntax::CStatement::Goto { .. }
            | syntax::CStatement::Declare { .. }
            | syntax::CStatement::DeclareStructValue { .. }
            | syntax::CStatement::Assign { .. }
            | syntax::CStatement::Call { .. }
            | syntax::CStatement::CallResult { .. }
            | syntax::CStatement::IndirectCall { .. }
            | syntax::CStatement::HeapAllocate { .. }
            | syntax::CStatement::HeapFree { .. }
            | syntax::CStatement::Return(_, _)
            | syntax::CStatement::Store { .. }
            | syntax::CStatement::SequentialStore { .. }
            | syntax::CStatement::AggregateCopy { .. }
            | syntax::CStatement::Update { .. }
            | syntax::CStatement::Assert { .. }
            | syntax::CStatement::StepValue { .. }
            | syntax::CStatement::LoopTest { .. } => {}
        }
    }

    fn collect_function_addresses(expression: &syntax::CExpression, names: &mut BTreeSet<String>) {
        match expression {
            syntax::CExpression::ScalarUpdate { .. } => {}
            syntax::CExpression::Call { arguments, .. } => {
                for argument in arguments {
                    collect_function_addresses(argument, names);
                }
            }
            syntax::CExpression::IndirectCall {
                function,
                arguments,
                ..
            } => {
                collect_function_addresses(function, names);
                for argument in arguments {
                    collect_function_addresses(argument, names);
                }
            }
            syntax::CExpression::StatementExpression { value, .. } => {
                collect_function_addresses(value, names);
            }
            syntax::CExpression::Assignment { value, .. } => {
                collect_function_addresses(value, names);
            }
            syntax::CExpression::FunctionAddress(name) => {
                names.insert(name.clone());
            }
            syntax::CExpression::Cast { expression, .. }
            | syntax::CExpression::FloatNegate(expression)
            | syntax::CExpression::FloatClassification { expression, .. }
            | syntax::CExpression::AddressOf(expression)
            | syntax::CExpression::AggregateAddress {
                pointer: expression,
                ..
            }
            | syntax::CExpression::UnionAddress {
                pointer: expression,
                ..
            }
            | syntax::CExpression::PointerOffsetBytes {
                pointer: expression,
                ..
            }
            | syntax::CExpression::Subobject {
                pointer: expression,
                ..
            }
            | syntax::CExpression::CheckedArrayIndex {
                index: expression, ..
            }
            | syntax::CExpression::Not(expression)
            | syntax::CExpression::BitwiseNot(expression)
            | syntax::CExpression::Load(expression, _)
            | syntax::CExpression::SequentialRead {
                target: expression, ..
            } => {
                collect_function_addresses(expression, names);
            }
            syntax::CExpression::SequentialWrite { target, value, .. } => {
                collect_function_addresses(target, names);
                collect_function_addresses(value, names);
            }
            syntax::CExpression::Ternary {
                condition,
                then_branch,
                else_branch,
            } => {
                collect_function_addresses(condition, names);
                collect_function_addresses(then_branch, names);
                collect_function_addresses(else_branch, names);
            }
            syntax::CExpression::LessThan(left, right)
            | syntax::CExpression::LessEqual(left, right)
            | syntax::CExpression::GreaterThan(left, right)
            | syntax::CExpression::GreaterEqual(left, right)
            | syntax::CExpression::Equal(left, right)
            | syntax::CExpression::NotEqual(left, right)
            | syntax::CExpression::And(left, right)
            | syntax::CExpression::Or(left, right)
            | syntax::CExpression::Add(left, right)
            | syntax::CExpression::Subtract(left, right)
            | syntax::CExpression::Multiply(left, right)
            | syntax::CExpression::Divide(left, right)
            | syntax::CExpression::Remainder(left, right)
            | syntax::CExpression::ShiftLeft(left, right)
            | syntax::CExpression::ShiftRight(left, right)
            | syntax::CExpression::BitwiseAnd(left, right)
            | syntax::CExpression::BitwiseOr(left, right)
            | syntax::CExpression::BitwiseXor(left, right)
            | syntax::CExpression::Index(left, right, _) => {
                collect_function_addresses(left, names);
                collect_function_addresses(right, names);
            }
            syntax::CExpression::Field { pointer, .. } => {
                collect_function_addresses(pointer, names);
            }
            syntax::CExpression::UnionField { pointer, .. } => {
                collect_function_addresses(pointer, names);
            }
            syntax::CExpression::StringLiteral(_)
            | CExpression::Void
            | syntax::CExpression::Variable(_)
            | syntax::CExpression::StepResult { .. }
            | syntax::CExpression::Int32Literal(_)
            | syntax::CExpression::UInt8Literal(_)
            | syntax::CExpression::UInt32Literal(_)
            | syntax::CExpression::Int64Literal(_)
            | syntax::CExpression::UInt64Literal(_)
            | syntax::CExpression::Float32Literal(_)
            | syntax::CExpression::Float64Literal(_)
            | syntax::CExpression::SizeOfStruct { .. }
            | syntax::CExpression::SizeOfUnion { .. }
            | syntax::CExpression::SizeOfType { .. } => {}
        }
    }

    let mut function_pointer_names = function
        .parameters()
        .iter()
        .filter(|parameter| {
            matches!(
                parameter.interface_type(),
                crate::languages::interface::InterfaceType::FunctionPointer(_)
            )
        })
        .map(|parameter| parameter.name().to_string())
        .collect::<BTreeSet<_>>();
    collect_function_pointer_names(function.body(), &mut function_pointer_names);

    fn visit(
        statement: &syntax::CStatement,
        calls: &mut Vec<BTreeSet<String>>,
        function_pointer_names: &BTreeSet<String>,
        allocator: &mut BTreeSet<&'static str>,
    ) {
        match statement {
            syntax::CStatement::EndAggregateLifetimes { .. }
            | syntax::CStatement::Skip
            | syntax::CStatement::Break
            | syntax::CStatement::Continue => {}
            syntax::CStatement::Goto { .. } | syntax::CStatement::FillArrayTail { .. } => {
                calls.push(BTreeSet::new());
            }
            syntax::CStatement::Label { statement, .. } => {
                visit(statement, calls, function_pointer_names, allocator)
            }
            syntax::CStatement::Seq(first, second) => {
                visit(first, calls, function_pointer_names, allocator);
                visit(second, calls, function_pointer_names, allocator);
            }
            syntax::CStatement::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(condition, &mut dependencies);
                calls.push(dependencies);
                visit(then_branch, calls, function_pointer_names, allocator);
                visit(else_branch, calls, function_pointer_names, allocator);
            }
            syntax::CStatement::While {
                test,
                condition,
                body,
                ..
            }
            | syntax::CStatement::DoWhile {
                test,
                condition,
                body,
                ..
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(condition, &mut dependencies);
                calls.push(dependencies);
                let post_test = matches!(statement, syntax::CStatement::DoWhile { .. });
                if !post_test && let Some(test) = test {
                    visit(test, calls, function_pointer_names, allocator);
                }
                visit(body, calls, function_pointer_names, allocator);
                if post_test && let Some(test) = test {
                    visit(test, calls, function_pointer_names, allocator);
                }
            }
            syntax::CStatement::For {
                test,
                initializer,
                condition,
                step,
                body,
                ..
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(condition, &mut dependencies);
                calls.push(dependencies);
                visit(initializer, calls, function_pointer_names, allocator);
                if let Some(test) = test {
                    visit(test, calls, function_pointer_names, allocator);
                }
                visit(body, calls, function_pointer_names, allocator);
                visit(step, calls, function_pointer_names, allocator);
            }
            syntax::CStatement::Switch {
                expression, cases, ..
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(expression, &mut dependencies);
                calls.push(dependencies);
                for case in cases {
                    visit(case.body(), calls, function_pointer_names, allocator);
                }
            }
            syntax::CStatement::Call {
                function_name,
                arguments,
                callee,
                ..
            }
            | syntax::CStatement::CallResult {
                function_name,
                arguments,
                callee,
                ..
            } => {
                let mut dependencies = BTreeSet::new();
                // A call through a function pointer names no function; the
                // functions it may reach are the addresses it reads.
                if let Some(callee) = callee {
                    collect_function_addresses(&callee.pointer, &mut dependencies);
                } else if !function_pointer_names.contains(function_name) {
                    match c_allocator_function(function_name) {
                        Some(function) => {
                            allocator.insert(function);
                        }
                        None => {
                            dependencies.insert(function_name.clone());
                        }
                    }
                }
                for argument in arguments {
                    collect_function_addresses(argument, &mut dependencies);
                }
                calls.push(dependencies);
            }
            syntax::CStatement::IndirectCall {
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
            syntax::CStatement::DeclareStructValue { .. } => calls.push(BTreeSet::new()),
            syntax::CStatement::Declare {
                initializer,
                zero_fill,
                ..
            } => {
                let mut dependencies = BTreeSet::new();
                for expression in initializer.iter().chain(
                    zero_fill
                        .iter()
                        .flat_map(|fill| fill.written_elements.iter().map(|(_, value)| value)),
                ) {
                    collect_function_addresses(expression, &mut dependencies);
                }
                calls.push(dependencies);
            }
            syntax::CStatement::Assign { expression, .. }
            | syntax::CStatement::HeapAllocate {
                bytes: expression, ..
            }
            | syntax::CStatement::HeapFree {
                pointer: expression,
                ..
            }
            | syntax::CStatement::Return(expression, _) => {
                match statement {
                    syntax::CStatement::HeapAllocate { zeroed, .. } => {
                        allocator.insert(if *zeroed { "calloc" } else { "malloc" });
                    }
                    syntax::CStatement::HeapFree { .. } => {
                        allocator.insert("free");
                    }
                    _ => {}
                }
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(expression, &mut dependencies);
                calls.push(dependencies);
            }
            syntax::CStatement::Store { pointer, value, .. } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(pointer, &mut dependencies);
                collect_function_addresses(value, &mut dependencies);
                calls.push(dependencies);
            }
            syntax::CStatement::SequentialStore { target, value, .. } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(target, &mut dependencies);
                collect_function_addresses(value, &mut dependencies);
                calls.push(dependencies);
            }
            syntax::CStatement::AggregateCopy { target, source, .. } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(target, &mut dependencies);
                collect_function_addresses(source, &mut dependencies);
                calls.push(dependencies);
            }
            syntax::CStatement::Update {
                target, operand, ..
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(target, &mut dependencies);
                collect_function_addresses(operand, &mut dependencies);
                calls.push(dependencies);
            }
            syntax::CStatement::Assert { condition, .. }
            | syntax::CStatement::LoopTest { condition, .. }
            | syntax::CStatement::StepValue {
                expression: condition,
                ..
            } => {
                let mut dependencies = BTreeSet::new();
                collect_function_addresses(condition, &mut dependencies);
                calls.push(dependencies);
            }
        }
    }

    let mut calls = Vec::new();
    visit(
        function.body(),
        &mut calls,
        &function_pointer_names,
        allocator,
    );
    calls
}

/// Words one termination refusal for the function `name`. A refused callee
/// is named by its source spelling and followed to the defect that refused
/// it, so the report ends at something the user can repair, with the repairs
/// the function that owns the defect has.
fn termination_refusal_report(
    name: &str,
    refusal: &TerminationRefusal,
    refusals: &BTreeMap<String, TerminationRefusal>,
    declared_diverging: &BTreeSet<String>,
    unsuitable_callback: Option<&UnsuitableCallback>,
    tactics: &BTreeSet<String>,
) -> String {
    let spelling = |name: &str| {
        name.split_once('#')
            .map_or(name, |(name, _)| name)
            .to_string()
    };
    let mut report = String::new();
    let mut visited = BTreeSet::new();
    let mut owner = name.to_string();
    let mut current = refusal;
    loop {
        let callee = match current {
            TerminationRefusal::Callee { callee } => callee,
            TerminationRefusal::UnmeasuredRecursion { callee } => {
                let shown = TerminationRefusal::UnmeasuredRecursion {
                    callee: spelling(callee),
                };
                if tactics.contains(&owner) {
                    report.push_str(&format!(
                        "{shown}; rank tactic `{owner}` with an expression `decreases` over its \
                         parameters or its binders' models, since a tactic may not diverge"
                    ));
                } else {
                    report.push_str(&format!(
                        "{shown}; rank it with function-level `decreases` clauses, or declare `{owner}` `diverges`"
                    ));
                }
                return report;
            }
            TerminationRefusal::UnrankedLoop { .. } => {
                report.push_str(&format!(
                    "{current}; give it one, or mark it `loop diverges` and declare `{owner}` `diverges`"
                ));
                return report;
            }
            TerminationRefusal::DivergingContract { .. } => {
                report.push_str(&format!(
                    "{current}; declare `{owner}` `diverges` too, or require a contract without the marker"
                ));
                return report;
            }
            TerminationRefusal::IndirectCall { .. } => {
                report.push_str(&current.to_string());
                if let Some(unsuitable) = unsuitable_callback {
                    report.push_str(&format!(
                        "; a call through a function pointer returns only when every function whose address is taken returns without calling through one, and `{}` takes the address of `{}`, which does not",
                        spelling(&unsuitable.taker),
                        spelling(&unsuitable.callback)
                    ));
                }
                return report;
            }
            TerminationRefusal::DeclaredDiverging => {
                report.push_str(&current.to_string());
                return report;
            }
        };
        let shown = TerminationRefusal::Callee {
            callee: spelling(callee),
        };
        report.push_str(&shown.to_string());
        if declared_diverging.contains(callee) {
            report.push_str(&format!(
                ": it is declared `diverges`; declare `{owner}` `diverges` too"
            ));
            return report;
        }
        let Some(next) = refusals.get(callee).filter(|_| visited.insert(callee)) else {
            return report;
        };
        report.push_str(": ");
        owner = spelling(callee);
        current = next;
    }
}

/// The spelling a pure `decreases` component is named by.
///
/// This is a rendering of the declared contract expression, not a lowering:
/// the plan and the loop head render the same clause, so the two agree by
/// construction. It exists so a diagnostic can print what the user wrote,
/// since a lowered specification expression has no source spelling.
pub(in crate::surface) fn termination_measure_source(expression: &ContractExpression) -> String {
    let binary = |left: &ContractExpression, right: &ContractExpression, operator: &str| {
        format!(
            "{} {operator} {}",
            termination_measure_source(left),
            termination_measure_source(right)
        )
    };
    match expression {
        ContractExpression::IntegerLiteral(literal) => literal.clone(),
        ContractExpression::Binding(name)
        | ContractExpression::ProgramBinding(name)
        | ContractExpression::QualifiedC { name, .. } => name.clone(),
        ContractExpression::ProgramExpression(expression) => {
            crate::kernel::ranking_measure_identity(
                &crate::kernel::RankingComponent::ProgramExpression(expression.clone()),
            )
        }
        ContractExpression::Field { base, field, .. } => {
            format!("{}.{field}", termination_measure_source(base))
        }
        ContractExpression::Call { name, arguments } => format!(
            "{name}({})",
            crate::surface::diagnostics::slice_call_arguments(
                name,
                arguments.iter().map(termination_measure_source).collect()
            )
            .join(", ")
        ),
        ContractExpression::ResourceField(access) => {
            format!("{}.{}", access.owner, access.field)
        }
        ContractExpression::Old(inner) => format!("old({})", termination_measure_source(inner)),
        ContractExpression::At {
            selector,
            expression,
        } => format!(
            "at({}, {})",
            crate::surface::diagnostics::describe_program_point_selector(selector),
            termination_measure_source(expression)
        ),
        ContractExpression::Negate(inner) => format!("-{}", termination_measure_source(inner)),
        ContractExpression::Add(left, right) => binary(left, right, "+"),
        ContractExpression::Subtract(left, right) => binary(left, right, "-"),
        ContractExpression::Multiply(left, right) => binary(left, right, "*"),
        ContractExpression::Divide(left, right) => binary(left, right, "/"),
        ContractExpression::Remainder(left, right) => binary(left, right, "%"),
        ContractExpression::Index(base, index) => format!(
            "{}[{}]",
            termination_measure_source(base),
            termination_measure_source(index)
        ),
        // A form without a rendering here still needs a stable identity, and
        // both sides render the same clause. The fully parenthesized source
        // printer is one, and it is also what a diagnostic can show: the
        // structural `Debug` form it replaced read
        // `BitwiseAnd(ProgramExpression(Variable("n")), IntegerLiteral("7"))`.
        expression => crate::surface::diagnostics::describe_contract_expression(expression),
    }
}

/// The loop resource binder a `decreases` clause names, if it is a structural
/// measure. Both the plan and the loop-head lowering classify with this, so
/// they cannot disagree about which kind of measure the clause declares.
pub(in crate::surface) fn loop_structural_measure_binder(
    clause: &StructuralClause,
) -> Option<String> {
    let measure = clause.decreases()?;
    let name = termination_measure_binder_name(measure)?;
    clause
        .resources()
        .iter()
        .any(|resource| {
            matches!(resource, ResourceClause::Named { binding, .. } if binding.name == name)
        })
        .then(|| name.to_string())
}

/// The bare source name a one-component `decreases` clause spells, if any.
fn termination_measure_binder_name(measure: &TerminationMeasure) -> Option<&str> {
    let [component] = measure.components() else {
        return None;
    };
    match component {
        ContractExpression::Binding(name)
        | ContractExpression::ProgramBinding(name)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) => Some(name),
        _ => None,
    }
}

/// Maps each Click-visible C spelling to the name its body executes under.
/// Only a header-provided `static inline` helper has two names; every other
/// function maps to itself and is left out of the map.
pub(in crate::surface) fn executing_function_names(
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    file: &ClickFile,
) -> Result<BTreeMap<String, String>, ClickError> {
    let mut names = BTreeMap::new();
    let mut ambiguous = BTreeSet::new();
    let mut qualified = BTreeMap::new();
    for (kernel_name, (source_path, function)) in parsed_sources {
        qualified.insert((source_path.as_str(), function.source_name()), kernel_name);
        if function.source_name() == kernel_name.as_str() {
            continue;
        }
        if names
            .insert(function.source_name().to_string(), kernel_name.clone())
            .is_some()
        {
            ambiguous.insert(function.source_name().to_string());
        }
    }
    // Keep ambiguous bare spellings unmapped: later contract lookup reports
    // the ambiguity, rather than guessing one translation unit's body.
    for name in ambiguous {
        names.remove(&name);
    }
    let mut selected_definitions = BTreeMap::new();
    for block in file
        .function_blocks()
        .iter()
        .filter(|block| !block.is_external())
    {
        let signature = block.signature();
        let kernel_name = if let Some(source) = &signature.c_source {
            let (_, name) = signature
                .name()
                .rsplit_once("::")
                .expect("qualified C head");
            qualified
                .get(&(source.as_str(), name))
                .map(|name| (*name).clone())
        } else {
            names.get(signature.name()).cloned().or_else(|| {
                parsed_sources
                    .get_key_value(signature.name())
                    .map(|(name, _)| name.clone())
            })
        };
        if let Some(kernel_name) = kernel_name {
            if let Some(previous) =
                selected_definitions.insert(kernel_name.clone(), signature.name())
            {
                return Err(ClickError::new(format!(
                    "contracts `{previous}` and `{}` select the same C definition; use one ordinary contract per definition",
                    signature.name()
                )));
            }
            if signature.c_source.is_some() {
                names.insert(signature.name().to_string(), kernel_name);
            }
        }
    }
    Ok(names)
}

/// The name `source_name`'s body executes under, which is its own spelling
/// unless it is a header-provided `static inline` helper.
fn executing_function_name(names: &BTreeMap<String, String>, source_name: &str) -> String {
    names
        .get(source_name)
        .cloned()
        .unwrap_or_else(|| source_name.to_string())
}

pub(in crate::surface) fn function_recursion_resource_requirement(
    function: &FunctionBlock,
) -> Result<Option<usize>, ClickError> {
    let Some(FunctionDecrease::Resource(measure)) = function.decreases() else {
        return Ok(None);
    };
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
        let Requirement::Resource(required) = requirement else {
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
    Ok(Some(index))
}

pub(in crate::surface) fn program_function_termination_plans(
    file: &ClickFile,
    selected_functions: Option<&BTreeSet<String>>,
    executing_names: &BTreeMap<String, String>,
) -> Result<
    (
        Vec<crate::kernel::FunctionTerminationPlan>,
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
                FunctionDecrease::Unresolved(_) => Err(ClickError::new(format!(
                    "function-level `decreases` in `{}` was never classified; declared-resource expansion did not run",
                    function.signature().name()
                ))),
                // Every numeric or named structural measure is ranked by
                // ordinary obligations at calls, using the entry authority
                // captured on the function interface.
                FunctionDecrease::Binder(binder) => {
                    Ok(crate::kernel::FunctionTerminationMeasure::Expression(binder.clone()))
                }
                FunctionDecrease::Numeric(measure) => {
                    Ok(crate::kernel::FunctionTerminationMeasure::Expression(
                        termination_measure_source(measure),
                    ))
                }
                // A tuple is ranked by obligations at the self-calls, like
                // any expression measure.
                FunctionDecrease::Lexicographic(components) => {
                    Ok(crate::kernel::FunctionTerminationMeasure::Expression(format!(
                        "({})",
                        components
                            .iter()
                            .map(termination_measure_source)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )))
                }
                FunctionDecrease::Resource(measure) => {
                    function_recursion_resource_requirement(function)?;
                    Ok(crate::kernel::FunctionTerminationMeasure::Expression(
                        describe_resource_clause(measure),
                    ))
                }
            })
            .transpose()?;
        // Frontier-local loops are bound to C loop identities during proof
        // execution. Proof order is not C loop order: distinct proof branches
        // may annotate the same C loop. Their verified rules supply the exact
        // checked ranking measures after execution, including nested loops.
        // A plan is a demand for certified termination, and only a function
        // this run verifies can answer it. A location-scoped run (`verify_at`,
        // which every audit site uses) verifies one proof unit and the C it
        // calls, so planning an unselected function's loops would fail
        // certification for a loop rule this run was never going to build.
        // A whole-file run selects everything, so nothing is dropped there.
        // A `diverges` function declares that it may not return, so it never
        // asks for whole-function termination evidence. It still plans its
        // ranked loops, which lets the check say whether the marker was
        // needed.
        let requests = selected && !function.signature().diverges();
        if requests {
            requested.insert(function.signature().name().to_string());
        }
        if selected && recursive_measure.is_some() {
            plans.push(program_function_termination_plan(
                executing_function_name(executing_names, function.signature().name()),
                recursive_measure,
                BTreeMap::new(),
            ));
        }
    }
    Ok((plans, requested))
}

/// Refuses a pure function or predicate whose body reads a C object by name:
/// a file-scope object by its bare name, or any object by its qualified
/// `unit::name` spelling.
///
/// An application is keyed on its argument values and the states its
/// array-ref arguments carry, and a predicate fact on its arguments; nothing
/// in either records the ambient memory. A body that read `counter` would make
/// `read_counter(0)` one term before and after a store to `counter`, and a
/// `requires` fact about it would discharge a false `ensures` verbatim. The
/// message carries the remedy: pass the object's value as an argument, and the
/// application then names the value it was applied to.
///
/// The check is syntactic over the declared bodies and runs once per
/// verification. A name a parameter shadows is the parameter; a name bound by
/// a `let`, a fold or a quantifier is removed by the collection itself.
fn reject_pure_bodies_reading_c_objects(
    spec_definitions: SpecDefinitions<'_>,
    file_scope_objects: &BTreeSet<String>,
) -> Result<(), ClickError> {
    fn read_object(
        parameters: &[FunctionParameter],
        referenced: BTreeSet<String>,
        file_scope_objects: &BTreeSet<String>,
    ) -> Option<String> {
        referenced.into_iter().find(|name| {
            parameters
                .iter()
                .all(|parameter| parameter.name() != name.as_str())
                && (name.contains("::") || file_scope_objects.contains(name))
        })
    }
    fn refusal(kind: &str, name: &str, object: &str) -> ClickError {
        ClickError::new(format!(
            "{kind} `{name}` reads the C object `{object}` by name; a {kind} body may read only its parameters, so pass the object's value as an argument"
        ))
        .with_kind(ClickErrorKind::Type)
    }
    for definition in spec_definitions.functions.definitions.values() {
        let Some(body) = definition.body() else {
            continue;
        };
        let mut referenced = BTreeSet::new();
        super::lowering::collect_contract_expression_referenced_names(body, &mut referenced);
        if let Some(object) = read_object(definition.parameters(), referenced, file_scope_objects) {
            return Err(refusal(
                "pure function",
                generic_instance_source_name(definition.name()),
                &object,
            ));
        }
    }
    for definition in spec_definitions.predicates.definitions.values() {
        let mut referenced = BTreeSet::new();
        super::lowering::collect_click_proposition_referenced_names(
            definition.body(),
            &mut referenced,
        );
        if let Some(object) = read_object(definition.parameters(), referenced, file_scope_objects) {
            return Err(refusal("predicate", definition.name(), &object));
        }
    }
    Ok(())
}

/// Looks up a C definition using the spelling visible to Click. Header-local
/// inline bodies have a translation-unit-qualified kernel name, so sidecar
/// contracts must match `ImportedFunction::source_name()` rather than the execution
/// identity returned by `ImportedFunction::name()`.
fn parsed_function_for_source_name<'a>(
    parsed_sources: &'a BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    source_name: &str,
    signature: Option<&FunctionSignature>,
) -> Result<
    Option<(
        &'a String,
        &'a String,
        &'a crate::languages::interface::ImportedFunction,
    )>,
    ClickError,
> {
    let mut matches = parsed_sources
        .iter()
        .filter(|(_, (path, function))| {
            signature.map_or_else(
                || function.source_name() == source_name,
                |signature| signature.matches_c_definition(path, function),
            )
        })
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

/// Parses the C layouts one sidecar's contracts need, selecting the C
/// implementation target from the sidecar itself. Include expansion runs
/// before the sidecar is parsed, so the target comes from the pre-parse scan
/// the parser later confirms.
pub(in crate::surface) fn parse_c_layouts(
    click_source: &str,
    c_sources: &ProgramSourceContext<'_>,
) -> Result<parser::ProgramLayouts, ClickError> {
    parse_c_layouts_for_target(
        click_source,
        c_sources,
        super::selected_c_target(click_source)?,
    )
}

/// Parses C layouts under an already selected target. A project selects one
/// target for every module, so its resolved target is passed in rather than
/// rescanned from the entry module alone.
pub(in crate::surface) fn parse_c_layouts_for_target(
    click_source: &str,
    c_sources: &ProgramSourceContext<'_>,
    target: CTarget,
) -> Result<parser::ProgramLayouts, ClickError> {
    let verifying_paths = super::verifying_source_paths(click_source)?;
    if let ProgramSource::Program { import, execution } = &c_sources.source {
        let mut verifying = verifying_paths
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let mut prepared = import.logical_sources();
        verifying.sort_unstable();
        prepared.sort_unstable();
        if verifying != prepared {
            return Err(ClickError::new(format!(
                "prepared {} import logical source must exactly match the verifying clause",
                import.language()
            )));
        }
        let mut layouts = parser::ProgramLayouts::of_execution(execution);
        layouts.language = Some(import.language());
        return Ok(layouts);
    }
    c_frontend::c_layouts(verifying_paths, c_sources, target)
}

/// A C++ method's receiver, its first parameter `this`.
fn receiver(
    function: &crate::languages::interface::ImportedFunction,
) -> Option<&crate::languages::interface::ImportedParameter> {
    function
        .parameters()
        .first()
        .filter(|parameter| parameter.name() == "this")
}

/// Whether a C++ method's receiver is `const`.
fn receiver_constant(function: &crate::languages::interface::ImportedFunction) -> bool {
    receiver(function)
        .is_some_and(crate::languages::interface::ImportedParameter::pointee_is_constant)
}

impl parser::ProgramLayouts {
    /// The layouts and per-function locals of a prepared program's
    /// execution. A prepared program exposes no globals or unions.
    fn of_execution(execution: &crate::languages::PreparedExecution) -> Self {
        let mut tables = parser::ProgramLayouts {
            struct_layouts: execution.layouts.clone(),
            record_spellings: execution.record_spellings.clone(),
            ..Default::default()
        };
        let source_names = execution
            .functions
            .iter()
            .map(|function| (function.name(), function.source_name()))
            .collect::<BTreeMap<_, _>>();
        for function in &execution.functions {
            tables.register_local_bindings(function);
            tables.register_string_literals(function);
            let captures = function.closure_captures();
            if !captures.is_empty() {
                tables.closure_captures.insert(
                    function.source_name().to_string(),
                    captures
                        .iter()
                        .map(|capture| FunctionParameter {
                            click_type: ClickType::Program(capture.interface_type()),
                            name: capture.name().to_string(),
                            struct_name: None,
                            function_pointer_signature: None,
                            constant: false,
                            pointee_constant: false,
                            reference: false,
                        })
                        .collect(),
                );
            }
            tables.aggregate_objects.insert(
                function.source_name().to_string(),
                source_struct_names(function.local_struct_values()),
            );
            if let Some(interface) = function.trait_interface()
                && let Some(interface) = source_names.get(interface)
            {
                tables
                    .virtual_overrides
                    .push((function.source_name().to_string(), interface.to_string()));
            }
            if !function.receiver_calls().is_empty() {
                tables.receiver_calls.insert(
                    function.source_name().to_string(),
                    function
                        .receiver_calls()
                        .iter()
                        .map(|(callee, holder)| {
                            (
                                source_names
                                    .get(callee.as_str())
                                    .map_or(callee.as_str(), |name| name)
                                    .to_string(),
                                holder.clone(),
                            )
                        })
                        .collect(),
                );
            }
            for interface_type in function
                .parameters()
                .iter()
                .map(|parameter| parameter.interface_type())
                .chain([function.return_type()])
            {
                // An enum or a `Vec` a parameter or result holds or refers to.
                if let InterfaceType::Parameter(enum_type)
                | InterfaceType::ParameterPointer(enum_type) = interface_type
                    && (enum_type.is_enum()
                        || generics::primitive_instance_of(enum_type.name()).is_some())
                {
                    tables
                        .rust_enum_types
                        .insert(rust_enum_type_name(enum_type), enum_type);
                }
            }
            if let Some(generic) = function.generic_instance() {
                tables.rust_generic_instances.push((
                    function.source_name().to_string(),
                    source_names
                        .get(generic)
                        .map_or(generic, |name| name)
                        .to_string(),
                    function
                        .parameters()
                        .iter()
                        .map(|parameter| parameter.interface_type())
                        .collect(),
                    function.return_type(),
                    function
                        .parameters()
                        .iter()
                        .map(|parameter| {
                            written_parameter_name(parameter.name(), parameter.is_reference())
                                .to_string()
                        })
                        .collect(),
                    receiver_constant(function),
                ));
            }
            if let Some(path) = execution.overload_paths.get(function.name()) {
                tables
                    .cpp_overloads
                    .entry(path.clone())
                    .or_default()
                    .push(parser::CppOverload {
                        name: function.source_name().to_string(),
                        constant: receiver_constant(function),
                        parameters: function
                            .parameters()
                            .iter()
                            .skip(usize::from(receiver(function).is_some()))
                            .map(|parameter| parameter.interface_type())
                            .collect(),
                    });
            }
            if let Some((trait_name, arguments)) =
                crate::languages::rust::names::interface_instance(function.name())
            {
                tables
                    .rust_trait_instances
                    .entry(trait_name)
                    .or_default()
                    .insert(arguments);
            }
            if let Some(method) = function.dispatched_method()
                && let Some(method) = source_names.get(method)
            {
                tables
                    .virtual_dispatches
                    .push((function.source_name().to_string(), method.to_string()));
            }
            tables.local_struct_pointers.insert(
                function.source_name().to_string(),
                parser::FunctionLocals {
                    execution_name: Some(function.name().to_string()),
                    struct_pointers: source_struct_names(function.local_struct_pointers()),
                    references: function
                        .local_references()
                        .iter()
                        .filter_map(|name| name.source_spelling().map(str::to_owned))
                        .collect(),
                    pointers: function
                        .local_pointers()
                        .iter()
                        .filter_map(|name| name.source_spelling().map(str::to_owned))
                        .collect(),
                    loop_iterators: function.loop_iterators().to_vec(),
                },
            );
        }
        tables
    }
}

#[cfg(test)]
pub(in crate::surface) fn parse_verified_sources(
    file: &ClickFile,
    c_sources: &BTreeMap<&str, &str>,
) -> Result<BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>, ClickError> {
    let sources = c_sources
        .iter()
        .map(|(path, source)| (*path, *source))
        .collect::<Vec<_>>();
    let context = ProgramSourceContext::bundle(&sources);
    parse_verified_sources_context(file, &context)
}

/// Publishes the program-wide never-address-taken names to the kernel, from
/// every function body this verification parsed.
///
/// Completeness of the source set is what makes the answer usable: a `local:`
/// block exists only because some function *body* executed a declaration, and
/// the only bodies a verification can execute are the ones in `parsed_sources`
/// — every function of every `verifying "...";` source the session loaded.
/// An external declaration has no body and no automatic objects of this
/// program; a callee reached through its contract contributes no block at all.
/// So a name that survives the pass cannot be addressed by anything that runs
/// here.
///
/// A verification that joins an enclosing session (it continues from an
/// earlier one's environment) must not raise the answer, because the memo
/// tables may already hold one. It can only lower it, by withdrawing a name
/// its own sources address; doing so drops those tables, since an answer they
/// cached was computed while the name was still in the registry. No caller
/// joins a session today, so this is a lock rather than a code path in use.
fn record_never_address_taken_locals(
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    session_is_fresh: bool,
) {
    let summary = crate::languages::c::address_taken::summarize_address_taken(
        parsed_sources.values().map(|(_, function)| function),
    );
    if session_is_fresh {
        crate::kernel::set_never_address_taken_locals(summary.never_taken());
        return;
    }
    if crate::kernel::withdraw_never_address_taken_locals(summary.taken()) {
        crate::kernel::clear_memory_resolution_memos_and_caches();
    }
}

/// A prepared declaration whose parameters the import knows only by
/// position, a Rust `extern` block item, named by its sidecar `extern fn`
/// head. Its types stay the declaration's, which the head is checked against.
fn named_by_extern_head(
    file: &ClickFile,
    function: &crate::languages::interface::ImportedFunction,
) -> Result<crate::languages::interface::ImportedFunction, ClickError> {
    if !function.has_positional_parameters() {
        return Ok(function.clone());
    }
    let Some(block) = file
        .function_blocks()
        .iter()
        .find(|block| block.signature().name() == function.source_name())
    else {
        return Ok(function.clone());
    };
    if !block.is_external() {
        return Err(ClickError::new(format!(
            "`{}` is declared in an `extern` block and has no body to verify; state its contract with `extern fn`",
            block.signature().name()
        ))
        .with_kind(ClickErrorKind::Type)
        .at_declaration(block.signature().name()));
    }
    // A head of another arity keeps the declaration's positions, and the
    // signature check reports the difference.
    Ok(function
        .named_by_head(
            block
                .signature()
                .parameters()
                .iter()
                .map(|parameter| parameter.name()),
        )
        .unwrap_or_else(|| function.clone()))
}

pub(in crate::surface) fn parse_verified_sources_context(
    file: &ClickFile,
    c_sources: &ProgramSourceContext<'_>,
) -> Result<BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>, ClickError> {
    parse_verified_sources_context_with_entry(file, c_sources, ProgramEntryStorage::Build)
}

/// Whether parsing the verifying sources also builds `main`'s program-entry
/// storage. Storage is as large as the program's static objects; a caller
/// that reads only function names, signatures, and call graphs (the
/// external-dependency summary) skips it. Static initializers are validated
/// either way, so both report the same source errors.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::surface) enum ProgramEntryStorage {
    Build,
    Skip,
}

pub(in crate::surface) fn parse_verified_sources_context_with_entry(
    file: &ClickFile,
    c_sources: &ProgramSourceContext<'_>,
    entry_storage: ProgramEntryStorage,
) -> Result<BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>, ClickError> {
    let build_storage = entry_storage == ProgramEntryStorage::Build;
    if file.selected_thread_runtime()
        == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread
    {
        if file.selected_c_target() != CTarget::X86_64LinuxUserspace {
            return Err(ClickError::new(
                "modeled-pthread runtime requires mode `userspace`",
            ));
        }
        // The runtime's declarations are Click's interface, never a
        // platform header, so a compiler import cannot supply them.
        if !matches!(c_sources.source, ProgramSource::Bundle(_)) {
            return Err(ClickError::new(
                "modeled-pthread runtime requires Click's built-in `<pthread.h>`; a compiler import cannot supply its declarations",
            ));
        }
        if file.verifying_sources.is_empty() {
            return Err(ClickError::new(
                "modeled-pthread runtime requires a verifying C source with selected `<pthread.h>` declarations",
            ));
        }
    }
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

    if let ProgramSource::Program { import, execution } = &c_sources.source {
        let mut verifying = file
            .verifying_sources
            .iter()
            .map(String::as_str)
            .collect::<Vec<_>>();
        let mut prepared = import.logical_sources();
        verifying.sort_unstable();
        prepared.sort_unstable();
        if verifying != prepared {
            return Err(ClickError::new(format!(
                "prepared {} import logical source must exactly match the verifying clause",
                import.language()
            )));
        }
        return execution
            .functions
            .iter()
            .map(|function| {
                Ok((
                    function.name().to_string(),
                    (
                        import.source_of(function.name()).to_string(),
                        named_by_extern_head(file, function)?,
                    ),
                ))
            })
            .collect();
    }

    let external_functions = file
        .function_blocks()
        .iter()
        .filter(|function| function.is_external())
        .map(|function| function.signature().name())
        .collect::<Vec<_>>();
    c_frontend::link_c_units(
        &file.verifying_sources,
        file.selected_c_target(),
        file.selected_thread_runtime(),
        &external_functions,
        c_sources,
        build_storage,
    )
}

fn validate_modeled_pthread_calls(
    statement: &syntax::CStatement,
    source_path: &str,
) -> Result<(), ClickError> {
    use syntax::{CExpression as E, CStatement as S};
    fn is_null(expression: &E) -> bool {
        match expression {
            E::Int32Literal(0) => true,
            E::Cast { expression, .. } => is_null(expression),
            _ => false,
        }
    }
    match statement {
        S::Call {
            function_name,
            arguments,
            ..
        }
        | S::CallResult {
            function_name,
            arguments,
            ..
        } => match function_name.as_str() {
            "pthread_create" => {
                if arguments.len() != 4
                    || !is_null(&arguments[1])
                    || !matches!(&arguments[2], E::FunctionAddress(_))
                {
                    return Err(ClickError::new(format!(
                        "modeled-pthread `pthread_create` in `{source_path}` requires null attributes and a direct worker"
                    )));
                }
            }
            "pthread_join" if arguments.len() != 2 || !is_null(&arguments[1]) => {
                return Err(ClickError::new(format!(
                    "modeled-pthread `pthread_join` in `{source_path}` requires a null result slot"
                )));
            }
            "pthread_mutex_init" if arguments.len() != 2 || !is_null(&arguments[1]) => {
                return Err(ClickError::new(format!(
                    "modeled-pthread `pthread_mutex_init` in `{source_path}` requires null attributes"
                )));
            }
            "pthread_mutex_lock" | "pthread_mutex_unlock" | "pthread_mutex_destroy"
                if arguments.len() != 1 =>
            {
                return Err(ClickError::new(format!(
                    "modeled-pthread `{function_name}` in `{source_path}` requires one mutex argument"
                )));
            }
            _ => {}
        },
        S::Label { statement, .. } => validate_modeled_pthread_calls(statement, source_path)?,
        S::Seq(first, second) => {
            validate_modeled_pthread_calls(first, source_path)?;
            validate_modeled_pthread_calls(second, source_path)?;
        }
        S::If {
            then_branch,
            else_branch,
            ..
        } => {
            validate_modeled_pthread_calls(then_branch, source_path)?;
            validate_modeled_pthread_calls(else_branch, source_path)?;
        }
        S::While { test, body, .. } | S::DoWhile { test, body, .. } => {
            if let Some(test) = test {
                validate_modeled_pthread_calls(test, source_path)?;
            }
            validate_modeled_pthread_calls(body, source_path)?;
        }
        S::For {
            test,
            initializer,
            step,
            body,
            ..
        } => {
            validate_modeled_pthread_calls(initializer, source_path)?;
            if let Some(test) = test {
                validate_modeled_pthread_calls(test, source_path)?;
            }
            validate_modeled_pthread_calls(step, source_path)?;
            validate_modeled_pthread_calls(body, source_path)?;
        }
        S::Switch { cases, .. } => {
            for case in cases {
                validate_modeled_pthread_calls(case.body(), source_path)?;
            }
        }
        _ => {}
    }
    Ok(())
}

pub(in crate::surface) fn external_c_function(
    function_block: &FunctionBlock,
) -> crate::languages::interface::ImportedFunction {
    external_c_function_with_layouts(function_block, &BTreeMap::new())
}

/// The C interface of a bodiless function block. A struct passed by value
/// carries its layout, as a parsed C declaration's parameter does: the
/// call copies the argument into an object of that layout.
pub(in crate::surface) fn external_c_function_with_layouts(
    function_block: &FunctionBlock,
    struct_layouts: &BTreeMap<String, crate::languages::interface::RecordLayout>,
) -> crate::languages::interface::ImportedFunction {
    crate::languages::interface::ImportedFunction::external(
        function_block.signature().return_type(),
        function_block.signature().name().to_string(),
        function_block
            .signature()
            .parameters()
            .iter()
            .map(|parameter| {
                let program_parameter =
                    crate::languages::interface::ImportedParameter::from_binding(
                        parameter.interface_type(),
                        parameter.binding_name(),
                        parameter.struct_name().map(str::to_string),
                    );
                let program_parameter = match parameter
                    .struct_name()
                    .filter(|_| program_parameter.is_struct_value())
                    .and_then(|name| Some((name, struct_layouts.get(name)?)))
                {
                    Some((name, layout)) => {
                        program_parameter.with_struct_value(name.to_string(), layout.clone())
                    }
                    None => program_parameter,
                };
                program_parameter
                    .with_constant(parameter.is_constant())
                    .with_pointee_constant(parameter.pointee_is_constant())
                    .with_reference(parameter.is_reference())
            })
            .collect(),
    )
    .with_return_pointee_constant(function_block.signature().return_pointee_is_constant())
    .with_return_reference(function_block.signature().returns_reference())
}

/// An instance block's head for the generic interface `name`'s trait, at
/// `i32`: `crate_name::Scale<i32>`.
fn generic_instance_example(name: &str) -> String {
    let display =
        crate::languages::rust::names::rust_display_name(name).unwrap_or_else(|| name.to_string());
    let trait_path = display
        .rsplit_once("::")
        .map_or(display.as_str(), |(path, _)| path);
    match trait_path.split_once('<') {
        Some((path, arguments)) => {
            let count = arguments.trim_end_matches('>').split(',').count();
            format!("{path}<{}>", vec!["i32"; count].join(", "))
        }
        None => trait_path.to_string(),
    }
}

pub(in crate::surface) fn build_function_environment(
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    function_blocks: &[FunctionBlock],
    contract_definitions: &[ContractDefinition],
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
) -> Result<ExecutionEnvironment, ClickError> {
    let mut environment = ExecutionEnvironment::new();
    for definition in contract_definitions {
        let function_block = definition.function_block();
        let parsed_function =
            external_c_function_with_layouts(function_block, resource_environment.struct_layouts());
        let InitialClaimContext {
            state, arguments, ..
        } = initial_claim_context_with_caller_owner(
            function_block,
            &parsed_function,
            resource_environment,
            spec_definitions,
            &format!("{}.named contract", definition.name()),
            None,
        )
        .map_err(|error| {
            error
                .with_context(format!(
                    "could not prepare named contract `{}`",
                    definition.name()
                ))
                .at_declaration(definition.name())
        })?;
        let function = annotated_function(
            function_block,
            &parsed_function,
            &state,
            &arguments,
            spec_definitions,
            resource_environment,
        )
        .map_err(|error| {
            error
                .with_context(format!(
                    "could not lower named contract `{}`",
                    definition.name()
                ))
                .at_declaration(definition.name())
        })?;
        let contract = FunctionContract::new(definition.name(), function)
            .and_then(|contract| {
                contract.with_value_parameters(definition.value_parameters().len())
            })
            .ok_or_else(|| {
                ClickError::new(format!(
                    "named contract `{}` cannot be applied opaquely{}",
                    definition.name(),
                    crate::surface::lowering::opaque_contract_refusal_suffix(definition.name())
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
    // A generic trait's interface, `trait p::Scale<T>`, holds for every
    // type: it is lowered once with its type parameters abstract, so a
    // clause that does not mean something at every type is refused here,
    // whether or not the import uses an instance.
    for function_block in function_blocks
        .iter()
        .filter(|block| block.is_external() && block.signature().has_abstract_types())
    {
        let name = function_block.signature().name();
        let parsed_function =
            external_c_function_with_layouts(function_block, resource_environment.struct_layouts());
        let InitialClaimContext {
            state, arguments, ..
        } = initial_claim_context_with_caller_owner(
            function_block,
            &parsed_function,
            resource_environment,
            spec_definitions,
            &format!("{name}.generic interface"),
            None,
        )
        .map_err(|error| {
            error
                .with_context(format!("could not prepare the generic interface `{name}`"))
                .at_declaration(name)
        })?;
        let function = annotated_function(
            function_block,
            &parsed_function,
            &state,
            &arguments,
            spec_definitions,
            resource_environment,
        )
        .map_err(|error| {
            error
                .with_context(format!("could not lower the generic interface `{name}`"))
                .at_declaration(name)
        })?;
        let argument_values = arguments
            .iter()
            .map(|argument| match argument {
                ProgramExpression::Value(value) => Some(value.clone()),
                _ => None,
            })
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                ClickError::new(format!(
                    "the generic interface `{name}` has an argument that is not a value"
                ))
                .at_declaration(name)
            })?;
        crate::kernel::program_check_contract_clauses_lower(
            &function,
            &state,
            &argument_values,
            &crate::kernel::PureFactContext::new(),
        )
        .map_err(|reason| {
            ClickError::new(reason).with_context(format!(
                "the generic interface `{}` does not mean something at every type: a value of an abstract type has `==` and `!=` only, so a clause that needs more belongs in an instance's block, such as `trait {}`",
                crate::languages::rust::names::rust_display_name(name).unwrap_or_else(|| name.to_string()),
                generic_instance_example(name),
            ))
            .at_declaration(name)
        })?;
    }
    for (source_path, function) in parsed_sources.values() {
        let closure_captures = function.closure_captures().len();
        let mut function_block = function_blocks.iter().find(|block| {
            block
                .signature()
                .matches_c_definition(source_path, function)
        });
        // A program's internal-linkage function is never the C library's
        // function of the same name, whose contract the standard library
        // declares. The C parser refuses an external-linkage definition of
        // a library function Click specifies.
        if let Some(block) = function_block
            && block.is_external()
            && function.name() != function.source_name()
            && standard_library_function_block(block.signature().name())?.as_ref() == Some(block)
        {
            function_block = None;
        }
        let function = match function_block {
            Some(function_block) => {
                check_signature(
                    function_block.signature(),
                    function_block.witness_count(),
                    function,
                    source_path,
                )?;
                let function = &*witnessed_function(function, function_block);
                let (resource_requires, resource_ensures) = function_resource_summary(
                    function_block,
                    function,
                    spec_definitions,
                    resource_environment,
                )?;
                let resource_constructors = function_resource_constructors(function_block)?;
                let (
                    contract_requires,
                    contract_requirement_sources,
                    contract_ensures,
                    exceptional_ensures,
                    contract_mutable,
                    contract_claims,
                    opaque_supported,
                    predicate_unfoldings,
                    recursion_measure,
                ) = function_contract_summary(
                    function_block,
                    function,
                    spec_definitions,
                    resource_environment,
                )?;
                let resource_derived_mutable_frame = !function_block.is_tactic_procedure()
                    && (crate::surface::lowering::construction_result_layout(function).is_some()
                        || function_block
                            .requires()
                            .iter()
                            .any(|requirement| matches!(requirement, Requirement::Resource(_))));
                let mut function = function
                    .to_kernel_function()
                    .with_resource_summary(resource_requires, resource_ensures)
                    .with_resource_constructors(resource_constructors)
                    .with_composite_resource_definitions(composite_resource_definitions(
                        resource_environment,
                        spec_definitions,
                    )?)
                    .with_ordinary_abstract_families(ordinary_abstract_families(
                        resource_environment,
                    ))
                    .with_predicate_unfoldings(predicate_unfoldings)
                    .with_contract(
                        contract_requires,
                        contract_ensures,
                        contract_mutable,
                        contract_claims,
                        opaque_supported,
                    )
                    .with_contract_requirement_sources(contract_requirement_sources);
                // The peers travel with the measure: they are what the anchor
                // ranks calls to, and a function without an expression measure ranks
                // none.
                let recursion_binder = match function_block.decreases() {
                    Some(FunctionDecrease::Binder(binder)) => Some(binder.clone()),
                    _ => None,
                };
                let recursion_resource = function_recursion_resource_requirement(function_block)?;
                if !recursion_measure.is_empty()
                    || recursion_binder.is_some()
                    || recursion_resource.is_some()
                {
                    function =
                        function.with_recursion_peers(function_block.recursion_peers().to_vec());
                }
                function = function
                    .with_recursion_binder(recursion_binder)
                    .with_recursion_resource(recursion_resource);
                function = function.with_recursion_measure(recursion_measure);
                function = function
                    .with_trailing_value_parameters(function_block.witness_count())
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "`{}` has more contract value parameters than parameters",
                            function_block.signature().name()
                        ))
                    })?;
                if let Some(exceptional_type) = function_block.signature().exceptional_type() {
                    function = function
                        .with_exceptional_outcome(exceptional_type.to_kernel_type())
                        .with_exceptional_ensures(exceptional_ensures);
                }
                if resource_derived_mutable_frame {
                    function.with_resource_derived_mutable_frame()
                } else {
                    function
                }
            }
            None => function.to_kernel_function(),
        };
        let unwritten_coercion = function_block.is_none() && is_object_coercion(function.name());
        if closure_captures > 0 {
            environment = with_closure_instance(environment, &function, closure_captures)?;
        }
        // A trait's or class's object carries no state when its sidecar
        // declares no functions: making one from a reference to the struct
        // or derived class, or the reference back, moves nothing.
        if unwritten_coercion {
            let no_op = function.clone().with_contract(
                vec![],
                vec![],
                vec![],
                vec![FunctionContractClaim::body_safety()],
                true,
            );
            let rule =
                crate::kernel::program_external_function_rule(no_op.clone()).ok_or_else(|| {
                    ClickError::new(format!(
                        "object coercion `{}` cannot be applied opaquely",
                        function.name()
                    ))
                })?;
            environment = environment
                .with_function(no_op)
                .with_external_function_rule(rule);
            continue;
        }
        environment = environment.with_function(function);
    }
    // A standard-library declaration is built only for a program that
    // refers to it, by the same call graph targeted verification follows.
    // The library's declarations are in every program's block list, and
    // building one costs an entry construction.
    let mut referenced = BTreeSet::new();
    for (_, parsed) in parsed_sources.values() {
        referenced.extend(c_statement_calls(parsed).into_iter().flatten());
    }
    // A prepared frontend's bodiless library function keeps its prepared
    // interface, which can return a constructed record by value; the
    // block's own signature only names the types a C declaration can.
    let prepared_interfaces = parsed_sources
        .values()
        .map(|(_, function)| (function.source_name(), function))
        .collect::<BTreeMap<_, _>>();
    let interfaces = parsed_sources
        .values()
        .filter_map(|(_, function)| function.trait_interface())
        .collect::<BTreeSet<_>>();
    for function_block in function_blocks
        .iter()
        .filter(|function| function.is_external())
    {
        let name = function_block.signature().name();
        if !referenced.contains(name)
            && standard_library_function_block(name)?.as_ref() == Some(function_block)
        {
            continue;
        }
        let parsed_function = match prepared_interfaces.get(name) {
            Some(prepared) => (*prepared).clone(),
            None => external_c_function_with_layouts(
                function_block,
                resource_environment.struct_layouts(),
            ),
        };
        let InitialClaimContext {
            state, arguments, ..
        } = initial_claim_context_with_caller_owner(
            function_block,
            &parsed_function,
            resource_environment,
            spec_definitions,
            &format!("{}.external contract", function_block.signature().name()),
            None,
        )?;
        let function = annotated_function(
            function_block,
            &parsed_function,
            &state,
            &arguments,
            spec_definitions,
            resource_environment,
        )?;
        let mut rule =
            crate::kernel::program_external_function_rule(function.clone()).ok_or_else(|| {
                ClickError::new(format!(
                    "external function `{}` has a contract that cannot be applied opaquely{}",
                    function_block.signature().name(),
                    crate::surface::lowering::opaque_contract_refusal_suffix(
                        function_block.signature().name()
                    )
                ))
            })?;
        // A crate trait method's interface is also the named contract its
        // implementations refine.
        if interfaces.contains(name) {
            let contract = FunctionContract::new(name, function.clone()).ok_or_else(|| {
                ClickError::new(format!(
                    "trait method interface `{name}` has a contract that cannot be applied opaquely{}",
                    crate::surface::lowering::opaque_contract_refusal_suffix(
                        function_block.signature().name()
                    )
                ))
            })?;
            environment = environment.with_function_contract(contract);
        }
        // Bind the representation-copy effect to the exact standard-library
        // declaration, never to the spelling. A user function that shadows the
        // name with a different declaration keeps the plain external contract.
        if is_recognized_representation_copy_block(function_block)? {
            rule = rule.with_representation_copy(crate::kernel::RepresentationCopyEffect {
                destination_argument: 0,
                source_argument: 1,
                bytes_argument: 2,
            });
        }
        environment = environment
            .with_function(function)
            .with_external_function_rule(rule);
    }
    check_trait_method_implementations(&environment, parsed_sources, function_blocks)?;
    Ok(environment)
}

/// Checks that each crate trait method implementation's contract refines the
/// trait's interface for that method, which a call through the trait
/// assumes of whichever implementation it reaches. An interface the sidecar
/// does not declare has no contract, so no call through it verifies.
fn check_trait_method_implementations(
    environment: &ExecutionEnvironment,
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
    function_blocks: &[FunctionBlock],
) -> Result<(), ClickError> {
    for (_, function) in parsed_sources.values() {
        let Some(interface) = function.trait_interface() else {
            continue;
        };
        // A C++ class template's override at other type arguments is its
        // generic method's instance, whose refinement of the generic
        // interface is checked once for every type.
        if function.generic_instance().is_some()
            && !crate::languages::rust::names::is_rust_name(function.name())
        {
            continue;
        }
        let rust = crate::languages::rust::names::is_rust_name(function.name());
        // A C++ virtual method with a body, or a Rust trait's default method,
        // is verified against its own contract, which is its interface. A
        // Rust interface is a verified function only where the sidecar
        // states its default body.
        let interface_source = parsed_sources
            .get(interface)
            .map_or(interface, |(_, function)| function.source_name());
        let verified_interface = if environment.get_function_contract(interface).is_some()
            || (rust
                && !function_blocks.iter().any(|block| {
                    !block.is_external() && block.signature().name() == interface_source
                })) {
            None
        } else {
            environment.get_function(interface)
        };
        if environment.get_function_contract(interface).is_none() && verified_interface.is_none() {
            continue;
        }
        let interface_name = interface_source;
        // A trait or class whose object carries state states each
        // implementation's interface on that implementation's own memory. A
        // C++ override of a defining class's method refines only that: a call
        // through a reference to a class another derives from is checked
        // against the object class's interface, never the method's own
        // contract.
        let iface = crate::surface::parser::implementation_interface_contract(function.name());
        let on_memory = environment.get_function_contract(&iface).is_some();
        let mut contracts = Vec::new();
        if on_memory {
            contracts.push(Some(iface.as_str()));
        } else {
            contracts.push(verified_interface.is_none().then_some(interface));
        }
        // An implementation without its own contract is never verified, so
        // no interface may stand for it.
        if !function_blocks
            .iter()
            .any(|block| !block.is_external() && block.signature().name() == function.source_name())
        {
            return Err(ClickError::new(if rust {
                format!(
                    "`{}` implements the trait method interface `{interface}` but has no \
                     contract; write it in the `impl` block, with its proof",
                    function.name()
                )
            } else {
                format!(
                    "`{}` overrides the virtual method `{interface_name}` but has no contract; \
                     write it in the sidecar, with its proof",
                    function.source_name()
                )
            })
            .at_declaration(function.name()));
        }
        let Some(implementation) = environment.get_function(function.name()) else {
            continue;
        };
        let mut refines = true;
        for contract in contracts {
            refines &= match (contract, verified_interface) {
                (None, Some(interface)) => {
                    crate::kernel::program_function_refines_function_contract(
                        environment,
                        interface,
                        implementation,
                    )
                }
                (contract, _) => crate::kernel::program_function_refines_named_contract(
                    environment,
                    contract.unwrap_or(interface),
                    implementation,
                ),
            }
            .map_err(ClickError::new)?;
        }
        if !refines {
            let (name, interface) = if rust {
                (
                    function.name(),
                    format!("the trait method interface `{interface}`"),
                )
            } else {
                (
                    function.source_name(),
                    format!("the virtual method `{interface_name}` it overrides"),
                )
            };
            return Err(ClickError::new(format!(
                "`{name}` does not refine {interface}: its contract must accept every call the \
                 interface allows; it inherits the interface's guarantees, and its `requires` \
                 must follow from the interface's, each clause read exactly or decided as a \
                 bare comparison"
            ))
            .at_declaration(function.name()));
        }
    }
    Ok(())
}

/// The functions that turn a crate struct reference into a crate trait's
/// object, or a C++ class reference into its base's, and back. Each returns
/// at once: it only moves resources.
fn object_coercion_names(
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
) -> impl Iterator<Item = String> + '_ {
    parsed_sources
        .values()
        .map(|(_, function)| function.name())
        .filter(|name| is_object_coercion(name))
        .map(str::to_string)
}

/// Whether `name` is a function an importer places where a reference
/// becomes a Rust trait's or a C++ base class's object, or back.
fn is_object_coercion(name: &str) -> bool {
    crate::languages::rust::names::is_object_coercion(name)
        || crate::languages::cpp::names::is_object_coercion(name)
}

/// The functions that make instances of the program's capturing closures.
/// Each returns at once: it only forms a function value.
fn closure_instance_names(
    parsed_sources: &BTreeMap<String, (String, crate::languages::interface::ImportedFunction)>,
) -> impl Iterator<Item = String> + '_ {
    parsed_sources
        .values()
        .filter(|(_, function)| !function.closure_captures().is_empty())
        .map(|(_, function)| crate::languages::rust::names::closure_instance_name(function.name()))
}

/// Registers a capturing closure's contract and the function that makes an
/// instance of it.
///
/// The closure's contract is a named contract under the closure's own name
/// whose value parameters are its captures. The instance function takes the
/// captured values and returns a fresh function value whose fact attaches
/// that contract fixed to them, so a callee requiring another contract of
/// the value is answered by contract-to-contract refinement.
fn with_closure_instance(
    environment: ExecutionEnvironment,
    closure: &ProgramFunction,
    captures: usize,
) -> Result<ExecutionEnvironment, ClickError> {
    let contract = FunctionContract::new(closure.name(), closure.clone())
        .and_then(|contract| contract.with_leading_value_parameters(captures))
        .ok_or_else(|| {
            ClickError::new(format!(
                "closure `{}` has a contract that cannot be applied opaquely",
                closure.name()
            ))
        })?;
    let parameters = contract.interface().value_parameters().to_vec();
    let mut arguments = vec![SpecPredicateArgument::Value(
        SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
            crate::kernel::CONTRACT_RESULT,
        )),
    )];
    arguments.extend(parameters.iter().map(|parameter| {
        SpecPredicateArgument::Value(SpecExpression::ProgramExpression(
            crate::kernel::program_expression::variable(parameter.name()),
        ))
    }));
    let instance = crate::kernel::program_function(
        contract.function_pointer_type(),
        crate::languages::rust::names::closure_instance_name(closure.name()),
        parameters,
        ProgramStatement::Skip,
    )
    .with_contract(
        vec![],
        vec![SpecProposition::Predicate {
            resource_state_dependent: false,
            name: contract.predicate_name(),
            arguments,
        }],
        vec![],
        vec![
            FunctionContractClaim::body_safety(),
            FunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    );
    let rule =
        crate::kernel::program_external_function_rule(instance.clone()).ok_or_else(|| {
            ClickError::new(format!(
                "closure `{}` cannot be made into a function value",
                closure.name()
            ))
        })?;
    Ok(environment
        .with_function_contract(contract)
        .with_function(instance)
        .with_external_function_rule(rule))
}

/// Whether `function_block` is the standard-library declaration that carries
/// the checked byte-copy effect. Its argument positions are fixed by that
/// declaration's parameter order.
fn is_recognized_representation_copy_block(
    function_block: &FunctionBlock,
) -> Result<bool, ClickError> {
    let name = function_block.signature().name();
    if name != "memcpy" {
        return Ok(false);
    }
    Ok(standard_library_function_block(name)?.as_ref() == Some(function_block))
}

pub(in crate::surface) fn function_resource_summary(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
    spec_definitions: SpecDefinitions<'_>,
    resource_environment: &ResourceEnvironment,
) -> Result<(Vec<ResourceSpec>, Vec<ResourceSpec>), ClickError> {
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
        .filter(|requirement| matches!(requirement, Requirement::Resource(_)))
        .count();
    let resource_positions = function_block.resource_requirement_positions();
    let mut resource_clause_index = 0;
    for requirement in function_block.requires() {
        let Requirement::Resource(resource) = requirement else {
            continue;
        };
        let (clause_index, clause_count) = resource_positions
            .get(resource_clause_index)
            .copied()
            .unwrap_or((resource_clause_index, resource_clause_count));
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
        let role = if requires[first_spec..].iter().any(ResourceSpec::is_view)
            || borrowed_index.is_some()
        {
            if let Some(index) = borrowed_index {
                borrowed_requirements[index] = true;
            }
            ResourceTransferRole::Borrow
        } else {
            ResourceTransferRole::Consume
        };
        for spec in &mut requires[first_spec..] {
            *spec = spec
                .clone()
                .with_role(role)
                .with_state_source(ResourceStateSource::Entry)
                .with_clause_position(clause_index, clause_count);
        }
        resource_clause_index += 1;
    }
    let mut ensures = Vec::new();
    let ensure_clause_count = function_block
        .ensures()
        .iter()
        .filter(|ensure| matches!(ensure.ensure(), Ensure::Resource(_)))
        .count();
    let ensure_positions = function_block.resource_ensure_positions();
    // A guard elaborates over the function's file-scope bindings, as the
    // contract summary's clauses do; built only when some guard needs it.
    let guard_entry_state = std::cell::OnceCell::new();
    let mut ensure_clause_index = 0;
    for ensure in function_block.ensures() {
        let Ensure::Resource(resource) = ensure.ensure() else {
            continue;
        };
        let (clause_index, clause_count) = ensure_positions
            .get(ensure_clause_index)
            .copied()
            .unwrap_or((ensure_clause_index, ensure_clause_count));
        let role = if ensure.borrowed() {
            ResourceTransferRole::Borrow
        } else {
            ResourceTransferRole::Produce
        };
        let retained_state = if ensure.borrowed() {
            ResourceStateSource::Entry
        } else {
            ResourceStateSource::Post
        };
        let result_binding = BTreeMap::from([(
            "result".to_string(),
            ContractExpression::ProgramExpression(ProgramExpression::Variable(
                crate::kernel::CONTRACT_RESULT,
            )),
        )]);
        let result_substitutions = ContractSubstitutions::for_contract_result(&result_binding);
        let lowered_resource = if ensure.borrowed() {
            // Borrowed clauses were written at entry; `result` there can be
            // a C parameter, and the return value has no entry binding.
            std::borrow::Cow::Borrowed(resource)
        } else {
            std::borrow::Cow::Owned(
                substitute_resource_clause_for_summary_in(resource, &result_substitutions)
                    .map_err(ClickError::new)?,
            )
        };
        let specs = resource_clause_to_resource_specs_with_metadata(
            &lowered_resource,
            parsed_function.parameters(),
            (!ensure.borrowed()).then(|| parsed_function.return_type().to_kernel_type()),
            role,
            retained_state,
            None,
        )?;
        let guard = ensure
            .condition()
            .map(|condition| {
                let condition = crate::surface::lowering::substitute_click_proposition_in(
                    condition,
                    &result_substitutions,
                )
                .map_err(ClickError::new)?;
                crate::surface::lowering::elaborate_requirement_proposition(
                    ParameterBinding::new(parsed_function.parameters(), &[]),
                    guard_entry_state.get_or_init(|| {
                        crate::kernel::initialize_program_function_globals(
                            &ExecutionState::new(),
                            &parsed_function.to_kernel_function(),
                        )
                    }),
                    &condition,
                    spec_definitions,
                )
                .map_err(ClickError::new)
            })
            .transpose()?;
        for mut spec in specs {
            // Instance ownership is identity-borrowed but field-produced: its
            // selected identity comes from entry while its declared fields are
            // checked against the post-call instance.  Keep that exceptional
            // state explicit in the normalized descriptor.
            if ensure.borrowed() && spec.is_instance() {
                spec = spec.with_state_source(ResourceStateSource::Post);
            }
            if let Some(guard) = &guard {
                spec = spec.with_guard(guard.clone());
            }
            ensures.push(spec.with_clause_position(clause_index, clause_count));
        }
        ensure_clause_index += 1;
    }
    if let Some(storage) = crate::surface::lowering::construction_result_resource(parsed_function)?
    {
        requires.push(
            storage
                .clone()
                .with_state_source(ResourceStateSource::Entry),
        );
        ensures.push(
            storage
                .with_role(ResourceTransferRole::Produce)
                .with_state_source(ResourceStateSource::Post),
        );
    }
    if parsed_function.requires_read_only_contract()
        && (!function_block.constructs().is_empty()
            || requires
                .iter()
                .chain(&ensures)
                .any(|resource| !resource.is_view()))
    {
        return Err(ClickError::new(format!(
            "expression observer `{}` requires a read-only contract: use views, without ownership transfer or resource construction",
            parsed_function.name()
        )));
    }
    Ok((requires, ensures))
}

pub(in crate::surface) fn function_resource_constructors(
    function_block: &FunctionBlock,
) -> Result<Vec<ResourceSpec>, ClickError> {
    function_block
        .constructs()
        .iter()
        .map(|resource| {
            let result_binding = BTreeMap::from([(
                "result".to_string(),
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    crate::kernel::CONTRACT_RESULT,
                )),
            )]);
            let resource = substitute_resource_clause_for_summary_in(
                resource,
                &ContractSubstitutions::for_contract_result(&result_binding),
            )
            .map_err(ClickError::new)?;

            resource_clause_to_resource_spec_with_metadata(
                &resource,
                &[],
                None,
                ResourceTransferRole::Produce,
                ResourceStateSource::Current,
                None,
            )
        })
        .collect()
}

/// The abstract families declared without `authorized`; the kernel treats
/// every other abstract family as a possible population member.
pub(in crate::surface) fn ordinary_abstract_families(
    resource_environment: &ResourceEnvironment,
) -> Vec<String> {
    resource_environment
        .definitions
        .values()
        .filter(|definition| {
            definition.composite_body().is_none()
                && !definition.is_authorized()
                // The built-in resources have their own kernel forms.
                && !matches!(
                    definition.name(),
                    "authority"
                        | "mutex_guard"
                        | "mutex_live"
                        | "mutex_use"
                        | "publisher"
                        | "subscriber"
                )
                && definition.name() != crate::kernel::ResourceFact::ALLOCATION_RESOURCE_NAME
        })
        .map(|definition| definition.name().to_string())
        .collect()
}

pub(in crate::surface) fn composite_resource_definitions(
    resource_environment: &ResourceEnvironment,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<CompositeResourceDefinition>, ClickError> {
    let mut definitions = Vec::new();
    let mut fold_sources = resource_environment
        .fold_sources
        .get()
        .is_none()
        .then(BTreeMap::new);
    // Resource-match Integer binders are logical atoms in the lowered arm
    // facts. Allocate them once for the complete function environment so
    // unrelated resources cannot accidentally share a carrier identity.
    let mut next_integer_binding_variable = 9_100_000_000u64;
    for definition in resource_environment.definitions.values() {
        // An unmatched body's named children are split out of its clauses
        // and facts, as each matched arm's are.
        let unmatched_scope = validation::resource_unmatched_body_scope(definition, |name| {
            resource_environment.get(name)
        })?;
        let definition = unmatched_scope.as_ref().unwrap_or(definition);
        // Field-bearing definitions retain their schema; only checked
        // instance exchanges may expose their bodies without erasing identity.
        let Some(body) = definition.composite_body() else {
            continue;
        };
        let mut fold_source = fold_sources.as_ref().map(|_| ResourceFoldSource {
            body: body.clone(),
            arms: BTreeMap::new(),
        });
        // The body's memory clauses take their element widths from the
        // definition's own parameters and field types, as contract clauses
        // do, so a `uint64` field is one 8-byte element on both sides of
        // an unfold.
        let definition_parameters = definition
            .parameters()
            .iter()
            .map(|parameter| {
                crate::languages::interface::ImportedParameter::new(
                    parameter.interface_type(),
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
                crate::kernel::ProgramParameter::new(
                    parameter.name(),
                    parameter.interface_type().to_kernel_type(),
                )
            })
            .collect();
        let condition = lower_composite_resource_condition(
            definition,
            spec_definitions,
            resource_environment.struct_layouts(),
        )?;
        let LoweredResourceBody {
            facts,
            fact_source_indices,
            children,
        } = lower_composite_resource_body(
            definition,
            spec_definitions,
            resource_environment.struct_layouts(),
        )?;
        let witnesses = body
            .witnesses()
            .iter()
            .map(|witness| {
                crate::kernel::ProgramParameter::new(
                    witness.name(),
                    witness.interface_type().to_kernel_type(),
                )
            })
            .collect();
        let facts_read_counts = body.facts().iter().any(proposition_contains_resource_count);
        let owned_bases = body
            .contains()
            .iter()
            .filter_map(|resource| match resource {
                ResourceClause::OwnMemory(segment) => Some(&segment.base),
                _ => None,
            })
            .collect::<Vec<_>>();
        let facts_claim_liveness = body.facts().iter().any(|fact| {
            proposition_contains_liveness_claim(
                fact,
                &owned_bases,
                spec_definitions.predicates,
                &mut BTreeSet::new(),
            )
        });
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
                    spec_definitions
                        .functions
                        .algebraic_type_definitions
                        .get(name)
                },
                |name| resource_environment.get(name),
            )?;
            let mut arms = Vec::new();
            for (variant, bindings, arm) in scopes {
                if let Some(source) = &mut fold_source {
                    source.arms.insert(
                        variant.clone(),
                        (
                            bindings.clone(),
                            arm.composite_body()
                                .expect("normalized resource arm has a body")
                                .clone(),
                        ),
                    );
                }
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
                        crate::languages::interface::ImportedParameter::new(
                            parameter.interface_type(),
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
                let LoweredResourceBody {
                    facts, children, ..
                } = lower_composite_resource_body_with_bindings(
                    &arm,
                    spec_definitions,
                    &bindings,
                    &integer_binding_variables,
                    resource_environment.struct_layouts(),
                )?;
                let binding_types = algebraic_type
                    .variants
                    .iter()
                    .find(|entry| entry.name == variant)
                    .ok_or_else(|| ClickError::new("unknown resource match constructor"))?
                    .fields
                    .clone();
                arms.push(crate::kernel::ResourceMatchArm {
                    children,
                    variant,
                    bindings: bindings.into_iter().map(|(name, _)| name).collect(),
                    binding_types,
                    binding_variables,
                    contains,
                    facts,
                });
            }
            Some(crate::kernel::ResourceMatchBody {
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
            CompositeResourceDefinition::new(
                definition.name(),
                parameters,
                condition,
                recursive,
                contains,
                facts,
            )
            .with_facts_read_counts(facts_read_counts)
            .with_authorized(definition.is_authorized())
            // A field-bearing abstract resource's body is empty, and no proof
            // folds or unfolds it: only trusted contracts move its instances.
            .with_sealed(definition.is_sealed())
            .with_resource_parameters(
                definition
                    .resource_parameters()
                    .iter()
                    .map(|parameter| {
                        resource_clause_to_resource_specs_with_metadata(
                            parameter,
                            &definition_parameters,
                            None,
                            ResourceTransferRole::Borrow,
                            ResourceStateSource::Current,
                            None,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect(),
            )
            .with_witnesses(witnesses)
            .with_fact_source_indices(fact_source_indices)
            .with_fact_source_spellings(
                body.facts()
                    .iter()
                    .map(crate::surface::printing::authored_click_proposition)
                    .collect(),
            )
            .with_liveness_facts(facts_claim_liveness)
            .with_resource_match_body(matched)
            .with_children(children)
            .with_matched_recursion(matched_recursive)
            .with_instance_schema(definition.field_schema().cloned()),
        );
        if let (Some(sources), Some(source)) = (&mut fold_sources, fold_source) {
            sources.insert(definition.name().to_owned(), source);
        }
    }
    crate::kernel::propagate_population_reach(&mut definitions);
    if let Some(sources) = fold_sources {
        let _ = resource_environment.fold_sources.set(sources);
    }
    Ok(definitions)
}

pub(in crate::surface) fn append_entry_resource_specs(
    resource: &ResourceClause,
    parameters: &[crate::languages::interface::ImportedParameter],
    _resource_environment: &ResourceEnvironment,
    specs: &mut Vec<ResourceSpec>,
) -> Result<(), ClickError> {
    specs.extend(resource_clause_to_resource_specs_with_metadata(
        resource,
        parameters,
        None,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
        None,
    )?);
    Ok(())
}

pub(in crate::surface) fn append_entry_resource_specs_with_pointer_types(
    resource: &ResourceClause,
    parameters: &[crate::languages::interface::ImportedParameter],
    pointer_element_types: &BTreeMap<String, crate::kernel::ProgramType>,
    specs: &mut Vec<ResourceSpec>,
) -> Result<(), ClickError> {
    specs.extend(resource_clause_to_resource_specs_with_metadata(
        resource,
        parameters,
        None,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
        Some(pointer_element_types),
    )?);
    Ok(())
}

fn resource_clause_to_resource_specs_with_metadata(
    resource: &ResourceClause,
    parameters: &[crate::languages::interface::ImportedParameter],
    result_type: Option<crate::kernel::ProgramType>,
    role: crate::kernel::ResourceTransferRole,
    retained_state: crate::kernel::ResourceStateSource,
    pointer_element_types: Option<&BTreeMap<String, crate::kernel::ProgramType>>,
) -> Result<Vec<ResourceSpec>, ClickError> {
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
                    retained_state,
                    pointer_element_types,
                )
            })
            .collect();
    }
    let mut spec = resource_clause_to_resource_spec_with_metadata(
        resource,
        parameters,
        result_type,
        role,
        retained_state,
        pointer_element_types,
    )?;
    fn declared_arguments(resource: &ResourceClause) -> Option<&[ContractExpression]> {
        match resource {
            ResourceClause::Named { resource, .. }
            | ResourceClause::Quantified { resource, .. } => declared_arguments(resource),
            ResourceClause::Declared { arguments, .. } => Some(arguments),
            _ => None,
        }
    }
    if let Some(arguments) = declared_arguments(resource) {
        spec = spec.with_source_arguments(
            arguments
                .iter()
                .map(crate::surface::diagnostics::describe_contract_expression)
                .collect(),
        );
    }
    Ok(vec![spec])
}

fn resource_clause_to_resource_spec_with_parameters(
    resource: &ResourceClause,
    parameters: &[crate::languages::interface::ImportedParameter],
    result_type: Option<crate::kernel::ProgramType>,
) -> Result<ResourceSpec, ClickError> {
    resource_clause_to_resource_spec_with_metadata(
        resource,
        parameters,
        result_type,
        crate::kernel::ResourceTransferRole::Borrow,
        crate::kernel::ResourceStateSource::Entry,
        None,
    )
}

fn resource_clause_to_resource_spec_for_body(
    resource: &ResourceClause,
    parameters: &[crate::languages::interface::ImportedParameter],
    result_type: Option<crate::kernel::ProgramType>,
) -> Result<ResourceSpec, ClickError> {
    // Scalar model fields are bound by the instance-body evaluator, just as
    // they are for memory endpoints and child arguments. Keep this spelling
    // local to bodies: a field read in an ordinary contract still requires
    // the named instance's authority.
    let lowered_quantity;
    let resource = if let ResourceClause::Quantified { quantity, resource } = resource {
        let no_values = BTreeMap::new();
        let substitutions =
            crate::surface::lowering::ContractSubstitutions::with_body_fields_as_program_names(
                &no_values,
            );
        lowered_quantity = ResourceClause::Quantified {
            quantity: crate::surface::lowering::substitute_contract_expression_in(
                quantity,
                &substitutions,
            )
            .map_err(ClickError::new)?,
            resource: resource.clone(),
        };
        &lowered_quantity
    } else {
        resource
    };
    let role = match resource {
        ResourceClause::Conditional { .. } => {
            return Err(ClickError::new(
                "conditional resource assertions are supported only in loop contracts",
            ));
        }
        ResourceClause::Named { .. } | ResourceClause::Quantified { .. } => {
            ResourceTransferRole::Consume
        }
        ResourceClause::ViewMemory(_) => ResourceTransferRole::Borrow,
        ResourceClause::OwnMemory(_) | ResourceClause::Iterated(_) => ResourceTransferRole::Consume,
        ResourceClause::MemoryAggregate { access, .. }
        | ResourceClause::Declared { access, .. } => match access {
            ResourceAccessMode::Own => ResourceTransferRole::Consume,
            ResourceAccessMode::View => ResourceTransferRole::Borrow,
        },
    };
    resource_clause_to_resource_spec_with_metadata(
        resource,
        parameters,
        result_type,
        role,
        ResourceStateSource::Current,
        None,
    )
}

fn resource_clause_to_resource_spec_with_metadata(
    resource: &ResourceClause,
    parameters: &[crate::languages::interface::ImportedParameter],
    result_type: Option<crate::kernel::ProgramType>,
    role: crate::kernel::ResourceTransferRole,
    retained_state: crate::kernel::ResourceStateSource,
    pointer_element_types: Option<&BTreeMap<String, crate::kernel::ProgramType>>,
) -> Result<ResourceSpec, ClickError> {
    match resource {
        ResourceClause::Conditional { .. } => Err(ClickError::new(
            "conditional resource assertions require loop-contract lowering",
        )),
        ResourceClause::Named { binding, resource } => {
            let inner = resource_clause_to_resource_spec_with_metadata(
                resource,
                parameters,
                result_type,
                role,
                retained_state,
                pointer_element_types,
            )?;
            if matches!(
                inner.term(),
                crate::kernel::ResourceTerm::MutexGuard { .. }
                    | crate::kernel::ResourceTerm::MutexLive { .. }
                    | crate::kernel::ResourceTerm::MutexUse { .. }
            ) {
                return inner
                    .with_mutex_authority_binding(binding.identity, binding.name.clone())
                    .map_err(|error| ClickError::new(error.to_string()));
            }
            ResourceSpec::instance(
                binding.identity,
                binding.name.clone(),
                binding.schema.clone().ok_or_else(|| {
                    ClickError::new("resource binding has no checked field schema")
                })?,
                inner,
                role,
                retained_state,
            )
            .map_err(|error| ClickError::new(error.to_string()))
        }
        ResourceClause::Quantified { quantity, resource } => {
            let inner = resource_clause_to_resource_spec_with_metadata(
                resource,
                parameters,
                result_type,
                role,
                retained_state,
                pointer_element_types,
            )?;
            let (quantity, quantity_state_source) =
                crate::surface::lowering::resource_argument_to_typed_program_expression_with_state(
                    quantity,
                    crate::languages::interface::InterfaceType::Int32,
                )?;
            ResourceSpec::quantified_with_quantity_state(
                quantity,
                inner,
                role,
                retained_state,
                quantity_state_source,
            )
            .map_err(|error| ClickError::new(error.to_string()))
        }
        ResourceClause::ViewMemory(segment) => Ok(ResourceSpec::memory(
            MemorySegment::new(
                segment.base.clone(),
                segment.start.clone(),
                segment.end.clone(),
            )
            .with_element_width(
                crate::surface::lowering::contract_segment_element_width_with_pointer_types(
                    parameters,
                    segment,
                    result_type,
                    pointer_element_types,
                ),
            )
            .with_value_runs(crate::surface::lowering::contract_segment_value_runs(
                parameters, segment,
            )),
            KernelResourceAccessMode::View,
            role,
            retained_state,
        )),
        ResourceClause::OwnMemory(segment) => Ok(ResourceSpec::memory(
            MemorySegment::new(
                segment.base.clone(),
                segment.start.clone(),
                segment.end.clone(),
            )
            .with_element_width(
                crate::surface::lowering::contract_segment_element_width_with_pointer_types(
                    parameters,
                    segment,
                    result_type,
                    pointer_element_types,
                ),
            )
            .with_uninitialized(segment.is_uninitialized())
            .with_value_runs(crate::surface::lowering::contract_segment_value_runs(
                parameters, segment,
            )),
            KernelResourceAccessMode::Own,
            role,
            retained_state,
        )),
        ResourceClause::MemoryAggregate { .. } => Err(ClickError::new(
            "aggregate resource clauses must be expanded before one resource spec is required",
        )),
        ResourceClause::Iterated(clause) => ResourceSpec::new(
            crate::kernel::ResourceTerm::Iterated(Box::new(
                crate::surface::lowering::iterated_clause_to_spec(clause, parameters)?,
            )),
            KernelResourceAccessMode::Own,
            crate::kernel::ResourceQuantity::One,
            role,
            retained_state,
        )
        .map_err(|error| ClickError::new(error.to_string())),
        ResourceClause::Declared {
            type_schema: _,
            resource_type_arguments,
            resource_arguments,
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => {
            if !resource_type_arguments.is_empty()
                && (!matches!(
                    name.as_str(),
                    "mutex_use" | "authority" | "publisher" | "subscriber"
                ) || resource_type_arguments.len() != 1)
            {
                return Err(ClickError::new("unsupported resource type arguments"));
            }
            let access = resource_access_to_kernel(*access);
            let lowered_arguments = arguments
                .iter()
                .zip(parameter_types)
                .map(|(argument, parameter_type)| {
                    crate::surface::lowering::resource_argument_to_typed_program_expression_with_state(
                        argument,
                        *parameter_type,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let (arguments, argument_state_sources): (Vec<_>, Vec<_>) =
                lowered_arguments.into_iter().unzip();
            let parameter_types = parameter_types
                .iter()
                .map(|interface_type| interface_type.to_kernel_type())
                .collect();
            if name == "authority" {
                let [protected] = resource_type_arguments.as_slice() else {
                    return Err(ClickError::new(
                        "authority expects one checked resource type",
                    ));
                };
                let ResourceClause::Declared {
                    type_schema: Some(schema),
                    arguments: protected_arguments,
                    ..
                } = protected
                else {
                    return Err(ClickError::new(
                        "authority requires a checked resource type",
                    ));
                };
                let mut anchor_clause = protected.clone();
                let population_arity = if let ResourceClause::Declared {
                    arguments,
                    parameter_types,
                    ..
                } = &mut anchor_clause
                {
                    if arguments.len() > 1 {
                        let arity = arguments.len();
                        arguments.truncate(1);
                        parameter_types.truncate(1);
                        Some(arity)
                    } else {
                        None
                    }
                } else {
                    None
                };
                let protected_spec = resource_clause_to_resource_spec_with_metadata(
                    &anchor_clause,
                    parameters,
                    result_type,
                    role,
                    retained_state,
                    pointer_element_types,
                )?
                .with_source_arguments(
                    protected_arguments
                        .iter()
                        .take(1)
                        .map(crate::surface::diagnostics::describe_contract_expression)
                        .collect(),
                );
                return ResourceSpec::new(
                    crate::kernel::ResourceTerm::PopulationAuthority {
                        population_arity,
                        protected: Box::new(crate::kernel::ResourceTypeSpec {
                            resource: Box::new(protected_spec),
                            schema: schema.clone(),
                        }),
                        state_source: retained_state,
                    },
                    access,
                    crate::kernel::ResourceQuantity::One,
                    role,
                    retained_state,
                )
                .map_err(|error| ClickError::new(error.to_string()));
            }
            if name == "mutex_guard" {
                let [mutex] = arguments.as_slice() else {
                    return Err(ClickError::new("mutex_guard expects one mutex pointer"));
                };
                return ResourceSpec::new(
                    crate::kernel::ResourceTerm::MutexGuard {
                        mutex: Box::new(mutex.clone()),
                        state_source: argument_state_sources[0],
                    },
                    access,
                    crate::kernel::ResourceQuantity::One,
                    role,
                    retained_state,
                )
                .map_err(|error| ClickError::new(error.to_string()));
            }
            if name == "mutex_live" {
                let [mutex] = arguments.as_slice() else {
                    return Err(ClickError::new("mutex_live expects one mutex pointer"));
                };
                return ResourceSpec::new(
                    crate::kernel::ResourceTerm::MutexLive {
                        mutex: Box::new(mutex.clone()),
                        state_source: argument_state_sources[0],
                    },
                    access,
                    crate::kernel::ResourceQuantity::One,
                    role,
                    retained_state,
                )
                .map_err(|error| ClickError::new(error.to_string()));
            }
            if let Some(side) = crate::kernel::PublicationSide::for_keyword(name) {
                let [flag] = arguments.as_slice() else {
                    return Err(ClickError::new(format!(
                        "{name} expects one atomic flag pointer"
                    )));
                };
                let Some(
                    payload @ ResourceClause::Declared {
                        type_schema: Some(schema),
                        arguments: payload_arguments,
                        ..
                    },
                ) = resource_type_arguments.first()
                else {
                    return Err(ClickError::new(format!(
                        "{name} requires the published resource type"
                    )));
                };
                let payload = crate::kernel::ResourceTypeSpec {
                    resource: Box::new(
                        resource_clause_to_resource_spec_with_metadata(
                            payload,
                            parameters,
                            result_type,
                            role,
                            retained_state,
                            pointer_element_types,
                        )?
                        .with_source_arguments(
                            payload_arguments
                                .iter()
                                .map(crate::surface::diagnostics::describe_contract_expression)
                                .collect(),
                        ),
                    ),
                    schema: schema.clone(),
                };
                return ResourceSpec::new(
                    crate::kernel::ResourceTerm::Publication {
                        side,
                        payload: Box::new(payload),
                        flag: Box::new(flag.clone()),
                        state_source: argument_state_sources[0],
                    },
                    access,
                    crate::kernel::ResourceQuantity::One,
                    role,
                    retained_state,
                )
                .map_err(|error| ClickError::new(error.to_string()));
            }
            if name == "mutex_use" {
                let [mutex] = arguments.as_slice() else {
                    return Err(ClickError::new("mutex_use expects one mutex pointer"));
                };
                return ResourceSpec::new(
                    crate::kernel::ResourceTerm::MutexUse {
                        protected: resource_type_arguments.first().map(|resource| {
                            let ResourceClause::Declared { type_schema: Some(schema), .. } = resource else { return Err(ClickError::new("protected resource type has no checked schema")); };
                            Ok(Box::new(crate::kernel::ResourceTypeSpec {
                                resource: Box::new(resource_clause_to_resource_spec_with_metadata(resource, parameters, result_type, role, retained_state, pointer_element_types,
)?.with_source_arguments(match resource {
                                    ResourceClause::Declared { arguments, .. } => arguments.iter().map(crate::surface::diagnostics::describe_contract_expression).collect(),
                                    _ => unreachable!(),
                                })),
                                schema: schema.clone(),
                            }))
                        }).transpose()?,
                        mutex: Box::new(mutex.clone()),
                        state_source: argument_state_sources[0],
                    },
                    access,
                    crate::kernel::ResourceQuantity::One,
                    role,
                    retained_state,
                )
                .map_err(|error| ClickError::new(error.to_string()));
            }
            ResourceSpec::declared_with_argument_states(
                match kind {
                    ResourceKind::Composite => ResourceFamily::Composite,
                    ResourceKind::Token => ResourceFamily::Token,
                },
                access,
                name.clone(),
                arguments,
                argument_state_sources,
                parameter_types,
                role,
                retained_state,
            )
            .map(|spec| {
                spec.with_resource_arguments(
                    resource_arguments
                        .iter()
                        .map(|reference| reference.identity)
                        .collect(),
                )
            })
            .map_err(|error| ClickError::new(error.to_string()))
        }
    }
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
        ResourceClause::Conditional {
            condition,
            resource,
        } => Ok(ResourceClause::Conditional {
            condition: crate::surface::lowering::substitute_click_proposition_in(
                condition,
                substitutions,
            )?,
            resource: Box::new(substitute_resource_clause_for_summary_in(
                resource,
                substitutions,
            )?),
        }),
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
        ResourceClause::Iterated(clause) => Ok(ResourceClause::Iterated(Box::new(
            crate::surface::lowering::substitute_iterated_clause(clause, substitutions)?,
        ))),
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
            type_schema,
            resource_type_arguments,
            resource_arguments,
            access,
            kind,
            name,
            arguments,
            parameter_types,
        } => Ok(ResourceClause::Declared {
            type_schema: type_schema.clone(),
            resource_type_arguments: resource_type_arguments
                .iter()
                .map(|resource| substitute_resource_clause_for_summary_in(resource, substitutions))
                .collect::<Result<_, _>>()?,
            resource_arguments: resource_arguments
                .iter()
                .map(|binding| {
                    match substitutions.instance_rename(&binding.name, binding.identity) {
                        Some(name) => ResourceInstanceBinding {
                            name,
                            ..binding.clone()
                        },
                        None => binding.clone(),
                    }
                })
                .collect(),
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
    if substitutions.is_contract_result_binding() && segment.state == ContractSegmentState::Old {
        return Ok(segment.clone());
    }
    let surface = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end } => ContractSegmentSurface::Range {
            base: substitute_contract_expression_in(base, substitutions)?,
            start: substitute_contract_expression_in(start, substitutions)?,
            end: substitute_contract_expression_in(end, substitutions)?,
        },
        ContractSegmentSurface::StructRange {
            base,
            start,
            end,
            layout,
        } => ContractSegmentSurface::StructRange {
            base: substitute_contract_expression_in(base, substitutions)?,
            start: substitute_contract_expression_in(start, substitutions)?,
            end: substitute_contract_expression_in(end, substitutions)?,
            layout: layout.clone(),
        },
        surface => surface.clone(),
    };
    // Preserve resolved C spellings unless a component actually refers to
    // the return name. Its surface form then distinguishes `program::result`.
    if substitutions.is_contract_result_binding()
        && let ContractSegmentSurface::Range { base, start, end }
        | ContractSegmentSurface::StructRange {
            base, start, end, ..
        } = &surface
    {
        let lower = |original: &ProgramExpression, source: &ContractExpression| {
            let rewritten = substitute_program_expression_in(original, substitutions)?;
            if rewritten == *original {
                return Ok(original.clone());
            }
            crate::surface::lowering::resource_argument_to_program_expression(source)
                .map_err(|error| error.message().to_string())
        };
        return Ok(ContractSegment {
            uninitialized: segment.uninitialized,
            state: segment.state,
            base: lower(&segment.base, base)?,
            start: lower(&segment.start, start)?,
            end: lower(&segment.end, end)?,
            surface,
        });
    }
    Ok(ContractSegment {
        uninitialized: segment.uninitialized,
        state: segment.state,
        base: substitute_program_expression_in(&segment.base, substitutions)?,
        start: substitute_program_expression_in(&segment.start, substitutions)?,
        end: substitute_program_expression_in(&segment.end, substitutions)?,
        surface,
    })
}

pub(in crate::surface) fn resource_clause_to_resource_spec(
    resource: &ResourceClause,
) -> Result<ResourceSpec, ClickError> {
    resource_clause_to_resource_spec_with_metadata(
        resource,
        &[],
        None,
        crate::kernel::ResourceTransferRole::Borrow,
        crate::kernel::ResourceStateSource::Current,
        None,
    )
}

pub(in crate::surface) fn resource_access_to_kernel(
    access: ResourceAccessMode,
) -> KernelResourceAccessMode {
    match access {
        ResourceAccessMode::Own => KernelResourceAccessMode::Own,
        ResourceAccessMode::View => KernelResourceAccessMode::View,
    }
}

/// The label of `claim`, one of `function_block`'s claims or the implicit
/// body-safety claim of a block without any
/// ([`FunctionBlock::ensure_claim_label`]).
pub(in crate::surface) fn function_claim_label(
    function_block: &FunctionBlock,
    claim: &FunctionClaimRef<'_>,
) -> String {
    match claim {
        FunctionClaimRef::Ensure(index, _) => function_block.ensure_claim_label(*index),
        FunctionClaimRef::ExceptionalEnsure(index, _) => {
            function_block.exceptional_ensure_claim_label(*index)
        }
    }
}

pub(in crate::surface) fn implication_body(proposition: &Proposition) -> &Proposition {
    match proposition {
        Proposition::Implies(_, body) => implication_body(body),
        _ => proposition,
    }
}
pub(in crate::surface) fn assumptions_from_propositions(
    propositions: &(impl PropositionSource + ?Sized),
) -> PureFactContext {
    propositions.pure_context()
}

/// `parsed_function` with the block's contract value parameters after its C
/// parameters, as the block's signature has them. Lowering the contract
/// reads them as it reads the C parameters; the lowered function moves them
/// back out ([`crate::kernel::ProgramFunction::with_trailing_value_parameters`]).
pub(in crate::surface) fn witnessed_function<'a>(
    parsed_function: &'a crate::languages::interface::ImportedFunction,
    function_block: &FunctionBlock,
) -> std::borrow::Cow<'a, crate::languages::interface::ImportedFunction> {
    if function_block.witness_count() == 0
        || parsed_function.parameters().len() == function_block.signature().parameters().len()
    {
        return std::borrow::Cow::Borrowed(parsed_function);
    }
    std::borrow::Cow::Owned(
        parsed_function.with_trailing_value_parameters(
            function_block.signature().parameters()
                [function_block.signature().parameters().len() - function_block.witness_count()..]
                .iter()
                .map(|parameter| {
                    crate::languages::interface::ImportedParameter::new(
                        parameter.interface_type(),
                        parameter.name().to_string(),
                        None,
                    )
                }),
        ),
    )
}

/// Checks a block's signature against its C declaration. The block's last
/// `witness_count` signature parameters are contract value parameters, which
/// C does not declare.
pub(in crate::surface) fn check_signature(
    signature: &FunctionSignature,
    witness_count: usize,
    parsed_function: &crate::languages::interface::ImportedFunction,
    source_path: &str,
) -> Result<(), ClickError> {
    if parsed_function.requires_nonthrowing_contract() && signature.exceptional_type().is_some() {
        return Err(ClickError::new(format!(
            "noexcept C++ function `{}` requires a nonthrowing contract; omit `throws` and prove no exception escapes",
            signature.name()
        )).with_kind(ClickErrorKind::Type));
    }
    let c_parameters = &signature.parameters()[..signature.parameters().len() - witness_count];
    // A head restates the C declaration, so its types are the declaration's
    // exact C types: `long` and `long long` are distinct, as in C.
    if signature.return_type() != parsed_function.return_type() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click return type is `{}`, C return type is `{}`",
            signature.name(),
            signature.return_type().ranked_diagnostic_name(),
            parsed_function.return_type().ranked_diagnostic_name()
        ))
        .with_kind(ClickErrorKind::Type));
    }

    if signature.returns_reference() != parsed_function.returns_reference() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: reference and pointer results are distinct",
            signature.name()
        )).with_kind(ClickErrorKind::Type));
    }

    if signature.returns_reference()
        && signature.return_struct_name.as_deref() != parsed_function.return_pointer_struct_name()
    {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: reference result must retain its nominal record type",
            signature.name()
        )).with_kind(ClickErrorKind::Type));
    }

    if signature.return_pointee_is_constant() != parsed_function.return_pointee_is_constant() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click return pointee const is {}, C return pointee const is {}",
            signature.name(),
            signature.return_pointee_is_constant(),
            parsed_function.return_pointee_is_constant()
        ))
        .with_kind(ClickErrorKind::Type));
    }

    if c_parameters.len() != parsed_function.parameters().len() {
        return Err(ClickError::new(format!(
            "signature mismatch for `{}` in `{source_path}`: .click has {} parameters, C has {}",
            signature.name(),
            c_parameters.len(),
            parsed_function.parameters().len()
        ))
        .with_kind(ClickErrorKind::Type));
    }

    for (index, (expected, actual)) in c_parameters
        .iter()
        .zip(parsed_function.parameters())
        .enumerate()
    {
        if expected.interface_type() != actual.interface_type()
            || expected.pointee_is_constant() != actual.pointee_is_constant()
            || expected.is_reference() != actual.is_reference()
            || expected.name() != actual.name()
            || expected.struct_name() != actual.struct_name()
            || expected.function_pointer_signature() != actual.function_pointer_signature()
        {
            return Err(ClickError::new(format!(
                "signature mismatch for `{}` parameter {} in `{source_path}`: .click has {} {}, C has {} {}",
                signature.name(),
                index + 1,
                describe_parameter_type(
                    expected.interface_type(),
                    expected.struct_name(),
                    expected.pointee_is_constant(),
                    expected.is_reference(),
                ),
                written_parameter_name(expected.name(), expected.is_reference()),
                describe_parameter_type(
                    actual.interface_type(),
                    actual.struct_name(),
                    actual.pointee_is_constant(),
                    actual.is_reference(),
                ),
                written_parameter_name(actual.name(), actual.is_reference())
            ))
            .with_kind(ClickErrorKind::Type));
        }
    }

    Ok(())
}

/// A parameter's name as a signature writes it: a reference is written by
/// its referent, not by the pointer that carries it.
fn written_parameter_name(name: &str, reference: bool) -> &str {
    let _ = reference;
    name
}

pub(in crate::surface) fn describe_parameter_type(
    interface_type: InterfaceType,
    struct_name: Option<&str>,
    pointee_constant: bool,
    reference: bool,
) -> String {
    let parameter_type = match struct_name {
        Some(name) if matches!(interface_type, InterfaceType::UInt8Array(_)) => {
            format!("struct {name}")
        }
        Some(name) if reference => format!("struct {name}&"),
        Some(name) => format!("struct {name}*"),
        None if matches!(interface_type, InterfaceType::FunctionPointer(_)) => {
            describe_interface_type(interface_type)
        }
        None => match interface_type.pointee_type().filter(|_| reference) {
            Some(referent) => format!("{}&", referent.ranked_diagnostic_name()),
            None => interface_type.ranked_diagnostic_name(),
        },
    };
    if pointee_constant {
        format!("const {parameter_type}")
    } else {
        parameter_type
    }
}

pub(in crate::surface) fn validate_region_proof_clauses(
    function_block: &FunctionBlock,
    parsed_function: &crate::languages::interface::ImportedFunction,
) -> Result<(), ClickError> {
    let loop_count = count_loop_regions(parsed_function);
    for region_proof_clause in function_block.structural_clauses() {
        validate_region_proof_clause(
            function_block.signature().name(),
            region_proof_clause,
            loop_count,
        )?;
    }
    Ok(())
}

/// One structural clause's check for [`validate_region_proof_clauses`]: it
/// depends only on the clause and the function's loop count.
pub(in crate::surface) fn validate_region_proof_clause(
    function_name: &str,
    region_proof_clause: &StructuralClause,
    loop_count: usize,
) -> Result<(), ClickError> {
    match region_proof_clause.region() {
        CodeRegion::Function => {
            return Err(ClickError::new(
                "`for function` region proof blocks are not supported",
            ));
        }
        CodeRegion::Loop(index) if *index >= loop_count => {
            return Err(ClickError::new(format!(
                "`{function_name}` has no `loop({index})` code region; it contains {loop_count} loop(s)"
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
    validate_loop_phase_proof("preserve", region_proof_clause.preserve_proof())
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
            ProofTactic::UnfoldProposition(_)
            | ProofTactic::UnfoldFunction(_)
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::Have(_)
            | ProofTactic::Known
            | ProofTactic::Normalize
            | ProofTactic::NormalizeUsing(_)
            | ProofTactic::Rewrite(_)
            | ProofTactic::Solve => {}
            ProofTactic::If(proof_if) => {
                validate_loop_initialization_tactics(&proof_if.then_tactics)?;
                validate_loop_initialization_tactics(&proof_if.else_tactics)?;
            }
            ProofTactic::Cases(proof_cases) => {
                for arm in proof_cases.arms() {
                    validate_loop_initialization_tactics(arm.tactics())?;
                }
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
            let sources = ProgramSourceContext::prepared(&imports);
            let click = "verifying \"shared.c\";\n";
            let file = parse_click_file_with_program_sources(click, &sources).unwrap();
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
            let sources = ProgramSourceContext::prepared(&imports);
            parse_c_layouts(&click(size), &sources).expect("prepared layouts parse");
            assert_eq!(sources.prepared_parse_count.get(), size);
            let file = parse_click_file_with_program_sources(&click(size), &sources)
                .expect("prepared click file parse");
            parse_verified_sources_context(&file, &sources)
                .expect("prepared verified sources parse");
            assert_eq!(sources.prepared_parse_count.get(), size);
        }
    }
}

#[cfg(test)]
mod modeled_pthread_binding_tests {
    use super::*;

    const CLICK: &str = "target \"x86_64-unknown-linux-gnu\";\nruntime \"modeled-pthread\";\nverifying \"fork_join.c\";\n";
    const FROZEN: &str = include_str!("../../examples/concurrency-fork-join/fork_join.c");

    fn parse_binding(click: &str, source: &str) -> Result<(), ClickError> {
        let sources = [("fork_join.c", source)];
        let context = ProgramSourceContext::bundle(&sources);
        let file = parse_click_file_with_program_sources(click, &context)?;
        parse_verified_sources_context(&file, &context).map(|_| ())
    }

    #[test]
    fn frozen_calls_select_the_builtin_binding_on_mac() {
        parse_binding(CLICK, FROZEN).expect("frozen call shapes bind to the built-in projection");
        let context = ProgramSourceContext::bundle(&[("fork_join.c", FROZEN)]);
        assert_ne!(
            context.environment_identity(CTarget::X86_64LinuxUserspace),
            context.environment_identity_with_runtime(
                CTarget::X86_64LinuxUserspace,
                crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread,
            )
        );
    }

    #[test]
    #[ignore = "nightly: 3s in the parallel gate"]
    fn frozen_worker_proof_retains_the_runtime_assumption() {
        let fixture = include_str!("../../mdtests/fork_join_worker_direct_contract.md");
        let click = fixture
            .split_once("```click\n")
            .unwrap()
            .1
            .split_once("\n```")
            .unwrap()
            .0
            .replace(
                "verifying \"fill_range.c\";",
                "runtime \"modeled-pthread\";\nverifying \"fork_join.c\";",
            );
        let verified = verify_c_sources(&click, &[("fork_join.c", FROZEN)])
            .expect("the original worker proof verifies against the unchanged C source");
        assert!(!verified.is_empty());
        assert_eq!(verified[0].function_block.signature().name(), "fill_range");
        assert_eq!(
            verified[0]
                .selection
                .as_ref()
                .unwrap()
                .runtime_assumptions
                .len(),
            1
        );
        let binding = verified[0]
            .selection
            .as_ref()
            .unwrap()
            .modeled_pthread_binding
            .as_ref()
            .unwrap();
        assert_eq!(
            binding,
            &crate::languages::c::thread_runtime::ModeledPthreadBinding::builtin()
        );
        assert_eq!(binding.mutex_storage_alignment, 8);
        assert_eq!(binding.mutex_storage_bytes, 40);
        assert_eq!(binding.target, CTarget::X86_64LinuxUserspace);
    }

    #[test]
    fn targeted_mutex_proof_uses_the_modeled_calls_without_c_definitions() {
        let fixture = include_str!("../../mdtests/guarded_resource_mutex_flow.md");
        let c = fixture
            .split_once("```c filename=guarded_resource_mutex_flow.c\n")
            .unwrap()
            .1
            .split_once("\n```")
            .unwrap()
            .0;
        let click = fixture
            .split_once("```click\n")
            .unwrap()
            .1
            .split_once("\n```")
            .unwrap()
            .0;
        verify_c_sources_functions(
            click,
            &[("guarded_resource_mutex_flow.c", c)],
            ["read_counter".to_string()],
        )
        .expect("a targeted proof should link modeled mutex calls");
    }

    #[test]
    fn source_create_status_can_be_copied_and_tested_later() {
        let c = "#include <pthread.h>\n#include <stddef.h>\nstruct cell { int value; };\nvoid *worker(void *p) { struct cell *q = p; q->value = 77; return NULL; }\nint run(struct cell *p) { pthread_t h; int rc = pthread_create(&h, NULL, worker, p); int saved = rc; int unrelated = 7; if (saved != 0) return 0; pthread_join(h, NULL); return unrelated; }\n";
        let click = "target \"x86_64-unknown-linux-gnu\";\nruntime \"modeled-pthread\";\nverifying \"fork_join.c\";\nvoid *worker(void *p) { owns (p as (struct cell *))->value; }\nint32 run(struct cell *p) { owns p->value; ensures result == 0 or result == 7; } by { step(); step(); step(); step(); step(); step(); step(); step(); branch { true => { step(); solve(); } false => {} } step(); step(); solve(); }\n";
        verify_c_sources(click, &[("fork_join.c", c)])
            .expect("a saved status should choose the checked create outcome");
        let expanded = expand_c_claim_source(
            click,
            &[("fork_join.c", c)],
            "run",
            ContractProofClaim::Grouped,
        )
        .expect("delayed create status proof should expand");
        verify_c_sources(&expanded, &[("fork_join.c", c)])
            .expect("expanded delayed status proof should certify");
    }

    #[test]
    fn source_cannot_read_transferred_memory_before_status_and_join() {
        let c = "#include <pthread.h>\n#include <stddef.h>\nstruct cell { int value; };\nvoid *worker(void *p) { struct cell *q = p; q->value = 77; return NULL; }\nint run(struct cell *p) { pthread_t h; int rc = pthread_create(&h, NULL, worker, p); int early = p->value; if (rc != 0) return 0; pthread_join(h, NULL); return early; }\n";
        let click = "target \"x86_64-unknown-linux-gnu\";\nruntime \"modeled-pthread\";\nverifying \"fork_join.c\";\nvoid *worker(void *p) { owns (p as (struct cell *))->value; }\nint32 run(struct cell *p) { owns p->value; } by { step(); step(); step(); step(); step(); }\n";
        let error = verify_c_sources(click, &[("fork_join.c", c)])
            .expect_err("the task memory cannot be read while creation is pending");
        assert!(
            error
                .message()
                .contains("resolve the pending pthread create status"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn a_session_cannot_drop_the_modeled_runtime() {
        let c = "#include <pthread.h>\nint answer(void) { return 1; }\n";
        let click = "target \"x86_64-unknown-linux-gnu\";\nruntime \"modeled-pthread\";\nverifying \"fork_join.c\";\nint32 answer() { ensures result == 1; }\n";
        let (session, _) = ProgramVerificationSession::new(click, &[("fork_join.c", c)])
            .expect("baseline modeled proof");
        let changed = click.replace("runtime \"modeled-pthread\";\n", "");
        let error = session.verify_at(&changed, 3, 47).unwrap_err();
        assert!(error.message().contains("identity mismatch"));
    }

    #[test]
    fn same_named_declaration_without_builtin_header_is_refused() {
        let source = "typedef unsigned long pthread_t;\nint pthread_join(pthread_t thread, void **result);\nint f(void) { return 0; }\n";
        assert!(
            parse_binding(CLICK, source)
                .unwrap_err()
                .message()
                .contains("from Click's built-in `<pthread.h>`")
        );
    }

    #[test]
    fn compiler_imported_pthread_declarations_are_refused() {
        // Even glibc's own `<pthread.h>`, locked through a compiler import,
        // does not supply the modeled declarations: they are Click's.
        let import = crate::languages::c::compiler_import::PreparedCImport::for_test_on(
            CTarget::X86_64LinuxUserspace,
            "fork_join.c",
            "# 1 \"/usr/include/pthread.h\" 1 3 4\ntypedef unsigned long pthread_t;\nint pthread_join(pthread_t thread, void **result);\n",
        );
        let imports = [import];
        let context = ProgramSourceContext::prepared(&imports);
        let error = parse_click_file_with_program_sources(CLICK, &context)
            .and_then(|file| parse_verified_sources_context(&file, &context).map(|_| ()))
            .unwrap_err();
        assert!(
            error.message().contains(
                "requires Click's built-in `<pthread.h>`; a compiler import cannot supply"
            ),
            "{}",
            error.message()
        );
    }

    #[test]
    fn local_definition_and_shadowing_are_refused() {
        let defined = format!(
            "{FROZEN}\nint pthread_join(pthread_t handle, void **result) {{ return 0; }}\n"
        );
        assert!(
            parse_binding(CLICK, &defined)
                .unwrap_err()
                .message()
                .contains("local definition")
        );
        let shadowed =
            "#include <pthread.h>\nint f(void) { int pthread_join = 0; return pthread_join; }\n";
        assert!(
            parse_binding(CLICK, shadowed)
                .unwrap_err()
                .message()
                .contains("shadowing")
        );
    }

    #[test]
    fn changed_declaration_and_wrong_target_are_refused() {
        let source = "#include <pthread.h>\nint pthread_join(int handle, void **result);\n";
        assert!(parse_binding(CLICK, source).is_err());
        let kernel = CLICK.replace("verifying", "mode \"kernel\";\nverifying");
        assert!(
            parse_binding(&kernel, FROZEN)
                .unwrap_err()
                .message()
                .contains("requires mode")
        );
    }

    #[test]
    fn nonnull_result_slot_is_refused() {
        let source = FROZEN
            .replace("pthread_join(first, NULL)", "pthread_join(first, &result)")
            .replace(
                "    pthread_t first;",
                "    void *result;\n    pthread_t first;",
            );
        assert!(
            parse_binding(CLICK, &source)
                .unwrap_err()
                .message()
                .contains("null result slot")
        );
    }

    #[test]
    fn nonnull_attributes_are_refused() {
        let source = FROZEN
            .replace(
                "pthread_create(&first, NULL,",
                "pthread_create(&first, attr,",
            )
            .replace(
                "    pthread_t first;",
                "    const pthread_attr_t *attr = NULL;\n    pthread_t first;",
            );
        assert!(
            parse_binding(CLICK, &source)
                .unwrap_err()
                .message()
                .contains("null attributes")
        );
    }
}

#[cfg(test)]
mod artifact_identity_tests {
    use super::*;

    const CLICK: &str = r#"
verifying "answer.c";
int32 answer() {
    ensures result == 1;
} by {
    step_until(function.exit);
    solve();
}


"#;

    const C_SOURCE: &str = "int answer(void) { return 1; }";

    fn position(source: &str, needle: &str) -> (usize, usize) {
        let offset = source.find(needle).expect("source needle");
        let line = source[..offset]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1;
        let column = offset - source[..offset].rfind('\n').unwrap_or(0);
        (line, column)
    }

    #[test]
    fn direct_and_targeted_routes_attach_the_same_fixed_identity() {
        let sources = [("answer.c", C_SOURCE)];
        let direct = verify_c_sources(CLICK, &sources).expect("direct verification");
        let (line, column) = position(CLICK, "step_until(function.exit);");
        let targeted =
            verify_c_sources_at(CLICK, &sources, line, column).expect("targeted verification");
        assert_eq!(direct.len(), targeted.len());
        assert_eq!(direct[0].artifact_identity, targeted[0].artifact_identity);
        assert_eq!(
            direct[0]
                .artifact_identity
                .unwrap()
                .resource_semantics_version,
            crate::kernel::RESOURCE_SEMANTICS_VERSION
        );
        assert!(
            std::mem::size_of::<ProofArtifactIdentity>() <= 64,
            "artifact identity must remain a fixed-size comparison token"
        );
    }

    #[test]
    fn prepared_identity_is_order_independent_and_binds_logical_sources() {
        let first = PreparedCImport::for_test("answer.c", C_SOURCE);
        let helper = PreparedCImport::for_test("helper.c", "int helper(void) { return 1; }");
        let forward_imports = [first.clone(), helper.clone()];
        let reverse_imports = [helper, first];
        let forward = ProgramSourceContext::prepared(&forward_imports);
        let reverse = ProgramSourceContext::prepared(&reverse_imports);
        assert_eq!(
            forward.environment_identity(CTarget::SUPPORTED),
            reverse.environment_identity(CTarget::SUPPORTED)
        );
    }

    /// The pre-pass must see what verification parses, not what a standalone
    /// parse produces: a name whose address the C takes has to be refused on
    /// the exact `ImportedFunction` values the registry is built from.
    #[test]
    fn the_address_taken_pass_reads_the_bodies_verification_parses() {
        const C: &str = "int32* echo(int32* p) { return p; }\nvoid v4(void) { int32 x; int32* q; x = 5; q = echo(&x); x = 1; }\n";
        const SIDECAR: &str = "verifying \"a2.c\";\nint32* echo(int32* p) { ensures result == p; }\nvoid v4() { ensures 1 == 1; }\n";
        let sources = [("a2.c", C)];
        let context = ProgramSourceContext::bundle(&sources);
        let file = super::selected_c_target(SIDECAR)
            .and_then(|target| {
                let layouts = parse_c_layouts_for_target(SIDECAR, &context, target)?;
                parser::parse_with_layouts_and_aggregate_objects(SIDECAR, layouts)
            })
            .expect("the fixture parses");
        let parsed = parse_verified_sources_context(&file, &context).expect("sources parse");
        let summary = crate::languages::c::address_taken::summarize_address_taken(
            parsed.values().map(|(_, function)| function),
        );
        assert!(
            !summary.never_taken().contains(&("x").into()),
            "`&x` is written in v4, so `x` must not be reported: {:?}",
            summary.never_taken()
        );
    }

    #[test]
    fn session_rejects_a_stale_identity_before_reverification() {
        let sources = [("answer.c", C_SOURCE)];
        let (mut session, _) =
            ProgramVerificationSession::new(CLICK, &sources).expect("baseline verification");
        let (line, column) = position(CLICK, "step_until(function.exit);");
        session.environment_identity =
            ProgramSourceContext::bundle(&[("answer.c", "int answer(void) { return 2; }")])
                .environment_identity(CTarget::SUPPORTED);
        let error = session
            .verify_at(CLICK, line, column)
            .expect_err("a session identity from other inputs must be refused");
        assert!(error.message().contains("identity mismatch"), "{error}");
    }

    #[test]
    fn session_identity_survives_a_proof_only_rewrite() {
        let sources = [("answer.c", C_SOURCE)];
        let (session, baseline) =
            ProgramVerificationSession::new(CLICK, &sources).expect("baseline verification");
        let rewritten = CLICK.replace("solve();", "solve();\n    ");
        let (line, column) = position(&rewritten, "step_until(function.exit);");
        let verified = session
            .verify_at(&rewritten, line, column)
            .expect("proof-only rewrite remains within the session identity");
        assert_ne!(baseline[0].artifact_identity, verified[0].artifact_identity);
    }

    #[test]
    fn artifact_identity_binds_click_source_and_target_profile() {
        let context = ProgramSourceContext::bundle(&[("answer.c", C_SOURCE)]);
        let changed_click = context.artifact_identity("proof A", CTarget::SUPPORTED);
        let other_click = context.artifact_identity("proof B", CTarget::SUPPORTED);
        assert_ne!(changed_click, other_click);

        let c_digest = [1; 32];
        let click_digest = [2; 32];
        let first_target = ProofArtifactIdentity::for_components(
            c_digest,
            click_digest,
            CTarget::X86_64LinuxKernel.name(),
        );
        let second_target =
            ProofArtifactIdentity::for_components(c_digest, click_digest, "other-target-profile");
        assert_ne!(first_target, second_target);
    }

    #[test]
    fn artifact_identity_separates_the_selected_c_targets() {
        let context = ProgramSourceContext::bundle(&[("answer.c", C_SOURCE)]);
        assert_ne!(
            context.artifact_identity(CLICK, CTarget::X86_64LinuxKernel),
            context.artifact_identity(CLICK, CTarget::X86_64LinuxUserspace)
        );
        assert_ne!(
            context.environment_identity(CTarget::X86_64LinuxKernel),
            context.environment_identity(CTarget::X86_64LinuxUserspace)
        );
    }

    /// End to end: one C source, one Click proof, and only the directive
    /// differing gives two different verified artifacts, each reporting its
    /// own target.
    #[test]
    fn a_target_directive_changes_the_verified_artifact_identity() {
        const KERNEL_CLICK: &str = r#"
target "x86_64-unknown-linux-gnu";
mode "kernel";
verifying "answer.c";
int32 answer() {
    ensures result == 1;
}
"#;
        let sources = [("answer.c", C_SOURCE)];
        let userspace = verify_c_sources(CLICK, &sources).expect("default target verification");
        let kernel = verify_c_sources(KERNEL_CLICK, &sources).expect("kernel target verification");
        assert_eq!(kernel.len(), userspace.len());
        assert_ne!(kernel[0].artifact_identity, userspace[0].artifact_identity);
        assert_eq!(kernel[0].target(), CTarget::X86_64LinuxKernel);
        assert_eq!(userspace[0].target(), CTarget::X86_64LinuxUserspace);
    }

    fn verify_sources(click: &str, source: &str) -> Result<(), ClickError> {
        let sources = ProgramSourceContext::bundle(&[("reader.c", source)]);
        verify_program_with_context(click, &sources, None, None, None, None).map(|_| ())
    }

    /// A contract input view is caller-supplied shared authority: the body
    /// may write memory it owns beside it, and reads through the view stay
    /// stable across that write.
    #[test]
    fn root_view_permits_an_owned_write_beside_it() {
        let click = r#"
verifying "reader.c";

int32 reader(int32 p[], int32 q[]) {
    views p[0..1];
    owns q[0..1];
    ensures result == p[0];
    ensures q[0] == 1;
}
"#;
        let source = "int reader(int *p, int *q) { q[0] = 1; return p[0]; }";
        verify_sources(click, source).expect("an owned write beside a rooted view");
    }

    /// The viewed pointer itself carries no write authority. A pure view
    /// holds no owner for the store, so the ordinary owned-authority check
    /// refuses it first and the missing-ownership diagnostic is what the
    /// verifier reports. The loan barrier is reserved for an
    /// owner-authorized write.
    #[test]
    fn root_view_reports_missing_ownership_for_an_unowned_write() {
        let click = r#"
verifying "reader.c";

int32 reader(int32 p[]) {
    views p[0..1];
    ensures result == p[0];
}
"#;
        let source = "int reader(int *p) { p[0] = 1; return p[0]; }";
        let error = verify_sources(click, source)
            .expect_err("a store through a contract input view must be refused");
        assert!(
            error.message().contains("missing resource fact `owns p"),
            "{}",
            error.message()
        );
    }

    /// An owned range assumed equal to the viewed range is not a partition
    /// any caller can supply: the view would be a projection of the owner,
    /// so no external root is installed and the proof stops at entry.
    #[test]
    fn root_view_refuses_an_owned_alias_of_the_viewed_range() {
        let click = r#"
verifying "reader.c";

int32 reader(int32 p[], int32 q[]) {
    requires q == p;
    views p[0..1];
    owns q[0..1];
    ensures result == p[0];
}
"#;
        let source = "int reader(int *p, int *q) { q[0] = 1; return p[0]; }";
        let error = verify_sources(click, source)
            .expect_err("an owned alias of a contract input view must be refused at entry");
        assert!(
            error
                .message()
                .contains("could not establish stable authority for a contract input view"),
            "{}",
            error.message()
        );
        // The refusal names the invariant and both clauses, so the contract
        // can be repaired without reading the ledger.
        assert!(
            error
                .message()
                .contains("the contract's `views` clause overlaps its own `owns` clause"),
            "{}",
            error.message()
        );
        assert!(
            error.message().contains("`views p[0]`")
                && error.message().contains("is already supported by `owns "),
            "{}",
            error.message()
        );
    }

    #[test]
    fn root_view_checks_pointer_offset_aliases() {
        for equality in ["q == p + 1", "p == q - 1", "q == p - 1"] {
            let click = format!(
                r#"
verifying "reader.c";
int32 reader(int32 p[], int32 q[]) {{
    requires {equality};
    requires p[1] == 3;
    views p[0..3];
    consumes q[0..3];
    ensures result == 3;
}}
"#
            );
            let error = verify_sources(
                &click,
                "int reader(int *p, int *q) { q[0] = 7; return p[1]; }",
            )
            .err()
            .unwrap_or_else(|| panic!("offset aliases must be checked for {equality}"));
            assert!(
                error.message().contains("overlaps"),
                "{equality}: {}",
                error.message()
            );
        }
    }

    #[test]
    fn root_view_accepts_adjacent_pointer_offset_aliases() {
        let click = r#"
verifying "reader.c";
int32 reader(int32 p[], int32 q[]) {
    requires q == p + 3;
    requires p[1] == 3;
    views p[0..3];
    consumes q[0..1];
    ensures result == 3;
}
"#;
        verify_sources(
            click,
            "int reader(int *p, int *q) { q[0] = 7; return p[1]; }",
        )
        .expect("adjacent owned and viewed ranges form a valid partition");
    }

    const RETARGET_SOURCE: &str = "struct buffer { int *data; };\n\
int read_entry(struct buffer *owner, int *other) { return owner->data[0]; }\n\
int read_retargeted(struct buffer *owner, int *other) {\n\
    owner->data = other;\n\
    return owner->data[0];\n\
}\n";

    /// R11's positive half: a contract input view over a pointer field's
    /// pointee is authority for reading that pointee.
    #[test]
    fn field_derived_view_reads_the_entry_footprint() {
        let click = r#"
verifying "reader.c";

int32 read_entry(struct buffer* owner, int32* other) {
    owns owner->data;
    views owner->data[0..1];
    ensures result == owner->data[0];
}
"#;
        verify_sources(click, RETARGET_SOURCE)
            .expect("a field-derived contract input view reads its own footprint");
    }

    /// R11's retargeting half: `views owner->data[0..1]` selects its
    /// footprint from the value `owner->data` holds at entry. Writing the
    /// pointer field does not move that authority to the new pointee, so the
    /// load after the write has nothing behind it: `other` carries no clause
    /// of its own, and the entry view does not follow the field
    /// (docs/internals/stable-views.md).
    #[test]
    fn field_derived_view_does_not_retarget_after_a_pointer_write() {
        let click = r#"
verifying "reader.c";

int32 read_retargeted(struct buffer* owner, int32* other) {
    owns owner->data;
    views owner->data[0..1];
    ensures result == owner->data[0];
}
"#;
        let error = verify_sources(click, RETARGET_SOURCE)
            .expect_err("the entry view must not follow a rewritten pointer field");
        assert!(
            error.message().contains("missing resource fact `views "),
            "{}",
            error.message()
        );
        // The view the state still holds is anchored at the pointer field's
        // entry load, not at whatever `owner->data` points at now.
        assert!(
            error.message().contains("views owner->data[")
                && !error.message().contains("arg-memory"),
            "{}",
            error.message()
        );
    }

    /// A view of read-only storage is intrinsic read authority, so it needs
    /// no borrowed root at entry and no loan at a call. A call that lends an
    /// ordinary view therefore has to carry the caller's file-static const
    /// view across its return without a binding for it, and the caller can
    /// still read the table afterwards.
    #[test]
    fn carries_a_file_static_const_view_across_a_call() {
        let click = r#"
verifying "reader.c";

int32 peek(const int32 values[], int32 q[]) {
    views values[0..2];
    views q[0..1];
    ensures result == q[0];
}

int32 run(int32 q[]) {
    views table[0..2];
    views q[0..1];
    ensures result == table[1];
}
"#;
        let source = "static const int32 table[2] = {5, 7};\n\
int32 peek(const int32 *values, int32 *q) { return q[0]; }\n\
int32 run(int32 *q) { int32 seen = peek(table, q); return table[1]; }\n";
        verify_sources(click, source)
            .expect("a const table view survives a call that lends an ordinary view");
    }

    fn verify_sources_with_header(
        click: &str,
        header: &str,
        source: &str,
    ) -> Result<(), ClickError> {
        let sources = ProgramSourceContext::bundle(&[("include/h.h", header), ("t.c", source)]);
        verify_program_with_context(click, &sources, None, None, None, None).map(|_| ())
    }

    const INLINE_HELPERS: &str = "#ifndef H_H\n#define H_H\n\
static inline int get0(int *p) { return p[0]; }\n\
static inline int set0(int *p) { p[0] = 9; return 0; }\n\
#endif\n";

    /// An inline helper is call-site code: it reads through the caller's
    /// contract input view without lending, and the view stays bound.
    #[test]
    fn inline_helper_reads_through_the_callers_rooted_view() {
        let click = r#"
verifying "t.c";

int32 run(int32 p[]) {
    views p[0..1];
    ensures result == p[0];
}
"#;
        let source = "#include \"include/h.h\"\nint run(int *p) { return get0(p); }";
        verify_sources_with_header(click, INLINE_HELPERS, source)
            .expect("an inline reader beside a rooted view");
    }

    /// The same helper writing through the caller's rooted view runs on the
    /// caller's resources, which hold no owner for the store, so the store is
    /// refused inside the body with the ordinary missing-ownership message.
    #[test]
    fn inline_helper_cannot_write_through_the_callers_rooted_view() {
        let click = r#"
verifying "t.c";

int32 run(int32 p[]) {
    views p[0..1];
    ensures result == 0;
}
"#;
        let source = "#include \"include/h.h\"\nint run(int *p) { return set0(p); }";
        let error = verify_sources_with_header(click, INLINE_HELPERS, source)
            .expect_err("an inline store through a rooted view must be refused");
        assert!(
            error.message().contains("missing resource fact `owns p"),
            "{}",
            error.message()
        );
    }

    /// Two per-claim proofs of one contract must share one borrowed-input
    /// root; with a fresh root per claim the second claim's completion is
    /// at a different authority than the certified entry and is refused.
    #[test]
    fn per_claim_proofs_share_one_borrowed_input_root() {
        let click = r#"
verifying "reader.c";

int32 reader(int32 p[]) {
    views p[0..1];
    ensures exact_value: result == p[0];
    ensures lower_bound: result >= p[0];
}
"#;
        let source = "int reader(int *p) { return p[0]; }";
        verify_sources(click, source).expect("both claims certify at one shared root");
    }

    /// A whole-struct assignment through a rooted view has no owner behind
    /// it (the entry root refuses an owner beside a viewed input), so the
    /// write-authority check that precedes the ledger names the missing
    /// owner exactly. The ledger-level aggregate witness, an owner-authorized
    /// copy over a lent field, is
    /// `owner_authorized_aggregate_copy_into_a_lent_range_requires_separation`.
    #[test]
    fn root_view_refuses_an_aggregate_copy_into_it() {
        let click = r#"
verifying "reader.c";

int32 copy_pair(struct pair* s, struct pair* t) {
    views *s;
    owns *t;
    ensures result == 0;
}
"#;
        let source = "struct pair { int a; int b; };\nint copy_pair(struct pair *s, struct pair *t) { *s = *t; return 0; }";
        let error = verify_sources(click, source)
            .expect_err("an aggregate copy into a contract input view must be refused");
        assert!(
            error
                .message()
                .contains("missing resource fact `owns s->a`"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn private_aggregate_parameters_can_lend_ownership_to_helpers() {
        let source = "struct packet { uint32 n; }; void change(uint32* n) { *n = 9; } uint32 consume(struct packet p) { uint32 before = p.n; change(&p.n); return before; } uint32 entry(uint32 x) { struct packet p = {x}; uint32 ignored = consume(p); return p.n; }";
        let proof = r#"verifying "reader.c";
            void change(uint32* n) { owns n[0..1]; ensures *n == 9u32; }
            uint32 consume(struct packet p) { ensures result == old(p.n); }
            uint32 entry(uint32 x) { ensures result == x; }
        "#;
        verify_sources(proof, source).unwrap();
        assert!(verify_sources(&proof.replace("result == x", "result != x"), source).is_err());
        assert!(
            verify_sources(proof, &source.replace("change(&p.n)", "change(&p.n + 1)")).is_err()
        );
        assert!(
            verify_sources(
                &proof.replace(
                    "ensures result == old(p.n)",
                    "owns p.n; ensures result == old(p.n)"
                ),
                source
            )
            .is_err()
        );
    }

    #[test]
    fn unsigned_array_field_returns_preserve_values_in_c_callers() {
        let source = "struct packet { uint32 words[4]; }; struct packet make(uint32 x) { struct packet p = {{x, x, x, x}}; return p; } uint32 read(uint32 x) { struct packet p = make(x); return p.words[3]; }";
        let proof = r#"verifying "reader.c";
            struct packet make(uint32 x) { ensures result.words[3] == x; }
            uint32 read(uint32 x) { ensures result == x; }
        "#;
        verify_sources(proof, source).unwrap();
        assert!(verify_sources(&proof.replace("result == x", "result != x"), source).is_err());
    }

    const BORROWING_BOX_PRELUDE: &str = r#"
verifying "reader.c";

resource box(p: struct s*) {
    owns p->a;
    owns p->b;
    owns p->d;
    views p->d[0..p->b];
    fact 0 <= p->b;
}

extern int32 setup(struct s* p, int32 d[], int32 n) {
    requires 0 <= n;
    consumes *p;
    views d[0..n];
    produces box(p);
    ensures p->b == n;
    ensures p->d == d;
}

extern void drop_box(struct s* p) {
    consumes box(p);
    produces *p;
}
"#;

    const BORROWING_BOX_HEADER: &str = "struct s { int32 a; int32 b; int32* d; };\nint32 setup(struct s* p, int32 d[], int32 n);\nvoid drop_box(struct s* p);\n";

    /// Step 7: a produced composite that packages a view of a lent input
    /// keeps that input lent: the owner stays escrowed, so the caller has no
    /// write authority over the array while the box describes it (the
    /// write-authority check runs before the ledger, as in step 3).
    #[test]
    fn escaping_borrow_refuses_a_write_while_the_composite_lives() {
        let click = format!(
            "{BORROWING_BOX_PRELUDE}
int32 f(struct s* p, int32 d[], int32 n) {{
    requires 0 < n;
    owns *p;
    owns d[0..n];
    ensures result == 0;
}}
"
        );
        let source = format!(
            "{BORROWING_BOX_HEADER}int32 f(struct s* p, int32 d[], int32 n) {{ setup(p, d, n); d[0] = 1; drop_box(p); return 0; }}"
        );
        let error = verify_sources(&click, &source)
            .expect_err("a write into memory a live borrowing composite views must be refused");
        assert!(
            error.message().contains("missing resource fact `owns "),
            "{}",
            error.message()
        );
    }

    /// Consuming the composite releases its hold: the loan ends, the owner
    /// is recovered, and the same write is accepted afterwards.
    #[test]
    #[ignore = "nightly: 0.6s in the parallel gate"]
    fn consuming_the_composite_recovers_the_owner() {
        let click = format!(
            "{BORROWING_BOX_PRELUDE}
int32 f(struct s* p, int32 d[], int32 n) {{
    requires 0 < n;
    owns *p;
    owns d[0..n];
    ensures result == 0;
}}
"
        );
        let source = format!(
            "{BORROWING_BOX_HEADER}int32 f(struct s* p, int32 d[], int32 n) {{ setup(p, d, n); drop_box(p); d[0] = 1; return 0; }}"
        );
        verify_sources(&click, &source).expect("after the composite is consumed the owner is back");
    }

    /// Unfolding a held composite hands the hold to the restored piece, and
    /// folding it back reuses that hold: the write stays refused while the
    /// piece is out, and one consumption still releases everything.
    #[test]
    #[ignore = "nightly: 1.3s in the parallel gate"]
    fn unfold_keeps_the_escaped_borrow_held() {
        let refused = format!(
            "{BORROWING_BOX_PRELUDE}
int32 f(struct s* p, int32 d[], int32 n) {{
    requires 0 < n;
    owns *p;
    owns d[0..n];
    ensures result == 0;
}} by {{
    step();
    unfold(box(p));
    step();
    step();
    step();
    solve();
}}
"
        );
        let source = format!(
            "{BORROWING_BOX_HEADER}int32 f(struct s* p, int32 d[], int32 n) {{ setup(p, d, n); d[0] = 1; drop_box(p); return 0; }}"
        );
        let error =
            verify_sources(&refused, &source).expect_err("the unfolded piece still holds the loan");
        assert!(
            error.message().contains("missing resource fact `owns "),
            "{}",
            error.message()
        );

        let accepted = format!(
            "{BORROWING_BOX_PRELUDE}
int32 f(struct s* p, int32 d[], int32 n) {{
    requires 0 < n;
    owns *p;
    owns d[0..n];
    ensures result == 0;
}} by {{
    step();
    unfold(box(p));
    fold(box(p));
    step();
    step();
    step();
    solve();
}}
"
        );
        let source = format!(
            "{BORROWING_BOX_HEADER}int32 f(struct s* p, int32 d[], int32 n) {{ setup(p, d, n); drop_box(p); d[0] = 1; return 0; }}"
        );
        verify_sources(&accepted, &source)
            .expect("a refold reuses the hold, so one consumption releases it");
    }

    /// A produced composite whose viewed piece no viewed input of the call
    /// backs describes memory nothing stabilizes; the call is refused.
    #[test]
    fn produced_borrowing_composite_without_a_backing_input_is_refused() {
        let click = r#"
verifying "reader.c";

resource box(p: struct s*) {
    owns p->a;
    owns p->b;
    owns p->d;
    views p->d[0..p->b];
    fact 0 <= p->b;
}

extern int32 conjure(struct s* p, int32 n) {
    requires 0 <= n;
    consumes *p;
    produces box(p);
    ensures p->b == n;
}

int32 f(struct s* p, int32 n) {
    requires 0 < n;
    consumes *p;
    produces box(p);
    ensures result == 0;
}
"#;
        let source = "struct s { int32 a; int32 b; int32* d; };\nint32 conjure(struct s* p, int32 n);\nint32 f(struct s* p, int32 n) { conjure(p, n); return 0; }";
        let error =
            verify_sources(click, source).expect_err("a borrow with no source cannot be produced");
        assert!(
            error
                .message()
                .contains("no viewed input of this call backs"),
            "{}",
            error.message()
        );
    }

    /// A callee whose contract leaves allocation continuity undecided may
    /// deallocate; retiring the allocation must consult the ledger that
    /// carries this call's own loans, because lending has removed the owner
    /// from the preserved residual (docs/internals/stable-views.md).
    #[test]
    fn call_retirement_requires_separation_from_its_own_loan() {
        let click = r#"
verifying "reader.c";

extern uint8* external_alloc(int32 bytes) {
    requires 0 < bytes;
    ensures result != 0;
    produces allocation(result, bytes);
    produces result[0..bytes];
}

extern void realloc_like(uint8* p, int32 n) {
    views p[0..4];
    consumes allocation(p, 4);
    produces allocation(p, n);
}

extern void drop_alloc(uint8* p, int32 n) {
    consumes allocation(p, n);
    consumes p[0..4];
}

int32 f(int32 n) {
    ensures result == 7;
}
"#;
        let source = "uint8* external_alloc(int32 bytes);\nvoid realloc_like(uint8* p, int32 n);\nvoid drop_alloc(uint8* p, int32 n);\nint32 f(int32 n) { uint8* data; int32 value; data = external_alloc(4); data[0] = 7; realloc_like(data, n); value = data[0]; drop_alloc(data, n); return value; }";
        let definite_free = click.replace("    produces allocation(p, n);\n", "");
        for contract in [click, &definite_free] {
            let error = verify_sources(contract, source)
                .expect_err("a call that may deallocate a lent allocation must be refused");
            assert!(
                error
                    .message()
                    .contains("verified call allocation retirement separation"),
                "{}",
                error.message()
            );
        }
    }

    #[test]
    fn a_surface_proof_carries_the_current_resource_semantics_version() {
        let click = r#"
verifying "reader.c";

int32 reader(int32 p[]) {
    owns p[0..1];
    ensures result == p[0];
}
"#;
        let source = "int reader(int *p) { return p[0]; }";
        let sources = ProgramSourceContext::bundle(&[("reader.c", source)]);
        let verified = verify_program_with_context(click, &sources, None, None, None, None)
            .expect("the surface route should use the kernel's stable view semantics");
        assert!(!verified.0.is_empty());
        assert_eq!(
            verified.0[0]
                .artifact_identity
                .unwrap()
                .resource_semantics_version,
            crate::kernel::RESOURCE_SEMANTICS_VERSION
        );
    }

    /// A one-call execution theorem whose conclusion is `goal`, proved from
    /// `Exact` by one step.  Only the target contract varies between the
    /// positive and negative cases.
    fn one_call_execution_theorem_source(goal: &str) -> String {
        format!(
            r#"
contract const int *Exact(const int *p) {{
    views p[0..1];
    ensures result == p;
}}
contract const int *{goal}(const int *p) {{
    views p[0..1];
    ensures result == p;
}}
theorem lift(callback: const int* (*)(const int*)) executes callback(const int* p) {{
    requires Exact(callback);
    ensures {goal}(callback) by {{ step(Exact); solve(); }}
}}
verifying "main.c";
int read_view(const int *(*f)(const int *), const int *p) {{
    requires Exact(f);
    views p[0..1];
    ensures result == p[0];
}} by {{ apply(lift(f)); step({goal}); step_until(function.exit); solve(); }}
"#
        )
    }

    const ONE_CALL_THEOREM_C_SOURCE: &str =
        "int read_view(const int *(*f)(const int *), const int *p) { return f(p)[0]; }";

    #[test]
    fn one_call_execution_theorem_still_needs_its_target_obligation() {
        // Reusing the proof's entry state must not discharge an obligation the
        // one-call proof never established: this target promises a value the
        // `Exact` step does not prove.
        let click = one_call_execution_theorem_source("Readable").replace(
            "ensures result == p;\n}\ntheorem",
            "ensures result == p + 1;\n}\ntheorem",
        );
        let sources = ProgramSourceContext::bundle(&[("main.c", ONE_CALL_THEOREM_C_SOURCE)]);
        let error = verify_program_with_context(&click, &sources, None, None, None, None)
            .expect_err("an unproved target obligation must still be refused");
        assert!(
            error
                .message()
                .contains("did not retain a complete proof for `lift.ensures_0`"),
            "unexpected diagnostic: {}",
            error.message()
        );
    }
}

#[cfg(test)]
mod retained_caller_tests {
    use super::*;

    #[test]
    #[ignore = "nightly: 3s in the parallel gate"]
    fn retained_session_reverifies_unchanged_static_array_caller() {
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/static_local_arrays.md");
        let fixture =
            crate::cli::parse_mdtest(&path, &std::fs::read_to_string(&path).unwrap()).unwrap();
        let click = fixture.click_source.unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let (session, _) = ProgramVerificationSession::new(&click, &sources).unwrap();
        let position =
            expansion::position_at_offset(&click, click.find("ensures result == 16").unwrap());
        for _ in 0..2 {
            session
                .verify_at(&click, position.line, position.column)
                .expect("an unchanged caller must keep the baseline verdict");
        }
        let changed = click.replace("ensures result == 16", "ensures result == 17");
        assert!(
            session
                .verify_at(&changed, position.line, position.column)
                .is_err(),
            "retained facts must not prove a changed, false postcondition"
        );
    }

    #[test]
    #[ignore = "nightly: 3s in the parallel gate"]
    fn resumed_kernel_reverifies_static_array_caller_without_a_cached_environment() {
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/static_local_arrays.md");
        let fixture =
            crate::cli::parse_mdtest(&path, &std::fs::read_to_string(&path).unwrap()).unwrap();
        let click = fixture.click_source.unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let position =
            expansion::position_at_offset(&click, click.find("ensures result == 16").unwrap());
        verify_c_sources(&click, &sources).unwrap();
        let _tables = crate::kernel::VerificationSession::resume();
        for _ in 0..2 {
            verify_c_sources_at(&click, &sources, position.line, position.column)
                .expect("a fresh target in retained tables must keep the baseline verdict");
        }
    }
}

#[cfg(test)]
mod construction_return_tests;

/// The name a sidecar's Rust type resolves to for enum type `enum_type`: a
/// crate enum's own name, or an `Option` or `Result` instance's importer
/// name.
fn rust_enum_type_name(enum_type: crate::kernel::TypeParameterName) -> String {
    let algebraic_type = enum_type.algebraic_type();
    let spelling = |argument: &crate::kernel::AlgebraicValueType| -> String {
        match argument {
            // A value of a Rust type parameter is a C value of that type.
            crate::kernel::AlgebraicValueType::Program(crate::kernel::ProgramType::Parameter(
                name,
            )) => name.name().to_string(),
            // The library's `Slice<T>` is Rust's shared slice: the chunk of
            // `Option<&[u8]>`.
            crate::kernel::AlgebraicValueType::Algebraic { name, arguments }
                if name == "Slice"
                    && let [crate::kernel::AlgebraicValueType::Program(element)] =
                        arguments.as_slice() =>
            {
                let element = match element {
                    crate::kernel::ProgramType::Int8 => "i8",
                    crate::kernel::ProgramType::Int16 => "i16",
                    crate::kernel::ProgramType::Int32 => "i32",
                    crate::kernel::ProgramType::Int64 => "i64",
                    crate::kernel::ProgramType::UInt8 => "u8",
                    crate::kernel::ProgramType::UInt16 => "u16",
                    crate::kernel::ProgramType::UInt32 => "u32",
                    crate::kernel::ProgramType::UInt64 => "usize",
                    _ => "?",
                };
                format!("&[{element}]")
            }
            // A crate enum payload is spelled by its name.
            crate::kernel::AlgebraicValueType::Algebraic { name, .. } => name.clone(),
            crate::kernel::AlgebraicValueType::Program(interface_type) => match interface_type {
                crate::kernel::ProgramType::Int8 => "i8",
                crate::kernel::ProgramType::Int16 => "i16",
                crate::kernel::ProgramType::Int32 => "i32",
                crate::kernel::ProgramType::Int64 => "i64",
                crate::kernel::ProgramType::UInt8 => "u8",
                crate::kernel::ProgramType::UInt16 => "u16",
                crate::kernel::ProgramType::UInt32 => "u32",
                crate::kernel::ProgramType::UInt64 => "usize",
                crate::kernel::ProgramType::Bool => "bool",
                // A shared reference to a scalar, the item of a slice
                // iterator: `Option<&u8>`.
                crate::kernel::ProgramType::Int8Pointer => "&i8",
                crate::kernel::ProgramType::Int16Pointer => "&i16",
                crate::kernel::ProgramType::Int32Pointer => "&i32",
                crate::kernel::ProgramType::Int64Pointer => "&i64",
                crate::kernel::ProgramType::UInt8Pointer => "&u8",
                crate::kernel::ProgramType::UInt16Pointer => "&u16",
                crate::kernel::ProgramType::UInt32Pointer => "&u32",
                crate::kernel::ProgramType::UInt64Pointer => "&usize",
                _ => "?",
            }
            .into(),
            _ => "?".into(),
        }
    };
    if let Some((primitive, arguments)) = generics::primitive_instance_of(&algebraic_type.name)
        && primitive == "Vec"
        && let [element] = arguments.as_slice()
    {
        return crate::languages::rust::names::vec_type_name(&spelling(element));
    }
    match algebraic_type.arguments.as_slice() {
        // The library's `Slice<T>` is named `Slice<u8>`.
        [element] if algebraic_type.name == "Slice" => {
            let mut name = "Slice".to_string();
            crate::languages::rust::names::push_type_argument(&mut name, &spelling(element));
            name
        }
        [argument] if algebraic_type.name == "Option" => {
            crate::languages::rust::names::option_type_name(&spelling(argument))
        }
        [ok, err] if algebraic_type.name == "Result" => {
            crate::languages::rust::names::result_type_name(&spelling(ok), &spelling(err))
        }
        _ => algebraic_type.name.clone(),
    }
}

pub(in crate::surface) fn program_contract_failure(
    failure: crate::kernel::ProgramContractFailure,
    declared_diverging: &BTreeSet<String>,
    tactic_names: &BTreeSet<String>,
) -> ClickError {
    use crate::kernel::{ProgramContractFailure, ProgramContractGoal};
    match failure {
        ProgramContractFailure::UnfinishedBody(name) => {
            let name = name.split_once('#').map_or(name.as_str(), |(name, _)| name);
            ClickError::new(format!(
                "contract proof for `{name}` still owes its body obligations"
            ))
            .at_declaration(name)
        }
        ProgramContractFailure::Analysis(error) => {
            let located = ClickError::new(format!("could not certify C termination: {error}"));
            match error.function() {
                Some(function) => located
                    .at_declaration(function.split_once('#').map_or(function, |(name, _)| name)),
                None => located,
            }
        }
        ProgramContractFailure::Obligation { goal, verdicts } => {
            let spelling = |name: &str| {
                name.split_once('#')
                    .map_or(name, |(name, _)| name)
                    .to_string()
            };
            match goal {
                ProgramContractGoal::DivergencePolicy(name) => {
                    let name = spelling(&name);
                    ClickError::new(format!("`{name}` is declared `diverges`, but every loop it runs is ranked and every call it makes descends; remove the marker")).at_declaration(&name)
                }
                ProgramContractGoal::CallbackSafety => {
                    let unsuitable = &verdicts.unsuitable_callbacks[0];
                    let taker = spelling(&unsuitable.taker);
                    let callback = spelling(&unsuitable.callback);
                    let lacks = match verdicts.refusals.get(&unsuitable.callback) {
                        Some(refusal) => termination_refusal_report(
                            &callback,
                            refusal,
                            &verdicts.refusals,
                            declared_diverging,
                            None,
                            tactic_names,
                        ),
                        None => "it has no termination evidence".to_string(),
                    };
                    ClickError::new(format!("could not certify termination for `{taker}`: it takes the address of `{callback}`, and a function reached through a function pointer must return without calling through one: {lacks}")).at_declaration(&taker)
                }
                ProgramContractGoal::Returns(name) => {
                    let refusal = &verdicts.refusals[&name];
                    let name = spelling(&name);
                    ClickError::new(format!(
                        "could not certify termination for `{name}`: {}",
                        termination_refusal_report(
                            &name,
                            refusal,
                            &verdicts.refusals,
                            declared_diverging,
                            verdicts.unsuitable_callbacks.first(),
                            tactic_names
                        )
                    ))
                    .at_declaration(&name)
                }
                ProgramContractGoal::Program
                | ProgramContractGoal::Body { .. }
                | ProgramContractGoal::BodyOpening
                | ProgramContractGoal::DeclaredBody(_) => {
                    unreachable!("the program root was opened into its declared goals")
                }
            }
        }
    }
}

#[cfg(test)]
mod induction_dependency_tests {
    use super::*;

    #[test]
    fn induction_hypothesis_is_local_only_after_its_declaration() {
        let source = r#"
            spec enum Chain { Nil, Link(Chain), }
            theorem reflexive(xs: Chain) {
                ensures xs == xs by {
                    apply(ih());
                    let ih = induct(xs);
                    match xs {
                        Chain::Nil => { apply(helper()); }
                        Chain::Link(tail) => { apply(ih(tail)); }
                    }
                }
            }
        "#;
        for (text, expected) in [
            (source.to_string(), vec!["helper", "ih"]),
            (source.replace("apply(ih());", ""), vec!["helper"]),
        ] {
            let file = crate::surface::parse(&text).unwrap();
            let mut names = BTreeSet::new();
            collect_applied_theorems_from_proof(
                file.theorem_definitions()[0].ensures()[0].proof(),
                &mut names,
            );
            assert_eq!(names, expected.into_iter().map(String::from).collect());
        }
    }
}
