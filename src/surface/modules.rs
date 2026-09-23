use super::*;

const MAX_IMPORT_CHAIN: usize = 256;

/// Resolves and validates a graph of already-loaded canonical modules.
///
/// Filesystem policy belongs to the CLI loader. This layer consumes immutable
/// module identities and sources, parses every reachable module once, checks
/// each module against only its own import closure, and returns the entry's
/// declaration environment with imported proof bodies left unselected.
pub fn resolve_click_project(
    project: &ClickProject,
    c_sources: &[(&str, &str)],
) -> Result<ClickFile, ClickError> {
    let entry_source = project
        .entry_source()
        .ok_or_else(|| ClickError::new(format!("missing entry module `{}`", project.entry())))?;
    let source_context = verification::CSourceContext::bundle(c_sources);
    let (
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
        local_struct_pointers,
    ) = verification::parse_c_layouts_for_target(
        entry_source,
        &source_context,
        super::selected_project_c_target(project)?,
    )?;
    resolve_click_project_with_layouts(
        project,
        struct_layouts,
        union_layouts,
        aggregate_objects,
        aggregate_array_objects,
        global_array_shapes,
        qualified_objects,
        local_struct_pointers,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::surface) fn resolve_click_project_with_layouts(
    project: &ClickProject,
    struct_layouts: BTreeMap<String, syntax::C0StructLayout>,
    union_layouts: BTreeMap<String, syntax::C0UnionLayout>,
    aggregate_objects: BTreeMap<String, BTreeMap<String, String>>,
    aggregate_array_objects: BTreeMap<String, BTreeSet<String>>,
    global_array_shapes: BTreeMap<String, BTreeMap<String, parser::GlobalArrayShape>>,
    qualified_objects: BTreeMap<String, BTreeMap<String, parser::QualifiedCObject>>,
    local_struct_pointers: BTreeMap<String, BTreeMap<String, String>>,
) -> Result<ClickFile, ClickError> {
    let modules = project
        .modules()
        .iter()
        .map(|module| (module.identity().to_string(), module))
        .collect::<BTreeMap<_, _>>();
    if modules.len() != project.modules().len() {
        return Err(ClickError::new("duplicate canonical Click module identity"));
    }
    let mut states = BTreeMap::<String, VisitState>::new();
    let mut stack = Vec::new();
    let mut order = Vec::new();
    visit_module(
        project.entry(),
        &modules,
        &mut states,
        &mut stack,
        &mut order,
    )?;

    let reachable = order.iter().cloned().collect::<BTreeSet<_>>();
    if reachable.len() != modules.len() {
        let unrelated = modules
            .keys()
            .filter(|identity| !reachable.contains(*identity))
            .take(8)
            .cloned()
            .collect::<Vec<_>>();
        return Err(ClickError::new(format!(
            "module input contains unreachable file(s): {}",
            unrelated.join(", ")
        )));
    }

    let mut locals = BTreeMap::<String, ClickFile>::new();
    for identity in &order {
        let module = modules[identity];
        let imported_ids = transitive_imports(identity, &modules)?;
        let imported_algebraic_types = imported_ids
            .iter()
            .filter_map(|imported| locals.get(imported))
            .flat_map(|file| file.algebraic_type_definitions().iter().cloned())
            .collect::<Vec<_>>();
        let mut local = parser::parse_file_items_for_module(
            module.source(),
            identity,
            &imported_algebraic_types,
            struct_layouts.clone(),
            union_layouts.clone(),
            aggregate_objects.clone(),
            aggregate_array_objects.clone(),
            global_array_shapes.clone(),
            qualified_objects.clone(),
            local_struct_pointers.clone(),
        )?;
        if local.imports().len() != module.imports().len() {
            return Err(ClickError::new(format!(
                "module `{identity}` resolved {} imports but its source declares {}",
                module.imports().len(),
                local.imports().len()
            )));
        }
        assign_local_owners(&mut local, identity)?;
        locals.insert(identity.clone(), local);

        // Validate now, before an importer can contribute names. This is the
        // capture boundary: a module can use its own declarations, its import
        // closure, and the standard library, but never an importer-only name.
        let closure_ids = transitive_imports(identity, &modules)?;
        let mut combined = merge_modules(&closure_ids, identity, &locals)?;
        combined = validation::expand_declared_resource_clauses(combined)?;
        validation::validate_click_definitions(&combined).map_err(|error| {
            ClickError::new(format!(
                "while checking module `{identity}`: {}",
                error.message()
            ))
        })?;
        lowering::check_resource_field_schemas(&mut combined)?;
    }

    for identity in order
        .iter()
        .filter(|identity| identity.as_str() != project.entry())
    {
        let local = &locals[identity];
        let importing_site = first_importing_site(identity, &modules, &locals);
        if !local.verifying_sources().is_empty() {
            return Err(ClickError::new(format!(
                "{importing_site}: imported module `{identity}` contains `verifying`; only the entry module may select C translation units"
            )));
        }
        if !local.contract_definitions().is_empty() || !local.function_blocks().is_empty() {
            return Err(ClickError::new(format!(
                "{importing_site}: imported module `{identity}` contains a named contract or C function specification; the first import delivery supports only algebraic types, predicates, pure functions, resources, and theorems"
            )));
        }
    }

    let imported = order
        .iter()
        .filter(|identity| identity.as_str() != project.entry())
        .cloned()
        .collect::<Vec<_>>();
    let mut combined = merge_modules(&imported, project.entry(), &locals)?;
    combined = validation::expand_declared_resource_clauses(combined)?;
    validation::validate_click_definitions(&combined)?;
    lowering::check_resource_field_schemas(&mut combined)?;
    reject_theorem_justification_cycles(&combined)?;
    Ok(combined)
}

fn first_importing_site(
    imported: &str,
    modules: &BTreeMap<String, &ClickModuleSource>,
    locals: &BTreeMap<String, ClickFile>,
) -> String {
    for (importer, module) in modules {
        for (index, target) in module.imports().iter().enumerate() {
            if target == imported {
                if let Some(position) = locals
                    .get(importer)
                    .and_then(|file| file.imports().get(index))
                    .map(ImportDeclaration::position)
                {
                    return format!("{importer}:{position}");
                }
                return format!("module `{importer}` import");
            }
        }
    }
    "import graph".to_string()
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum VisitState {
    Visiting,
    Complete,
}

fn visit_module(
    identity: &str,
    modules: &BTreeMap<String, &ClickModuleSource>,
    states: &mut BTreeMap<String, VisitState>,
    stack: &mut Vec<String>,
    order: &mut Vec<String>,
) -> Result<(), ClickError> {
    match states.get(identity) {
        Some(VisitState::Complete) => return Ok(()),
        Some(VisitState::Visiting) => {
            let start = stack.iter().position(|item| item == identity).unwrap_or(0);
            let mut cycle = stack[start..].to_vec();
            cycle.push(identity.to_string());
            return Err(ClickError::new(format!(
                "Click import cycle: {}",
                bounded_chain(&cycle)
            )));
        }
        None => {}
    }
    if stack.len() >= MAX_IMPORT_CHAIN {
        return Err(ClickError::new(format!(
            "Click import chain exceeds {MAX_IMPORT_CHAIN} modules: {}",
            bounded_chain(stack)
        )));
    }
    let module = modules
        .get(identity)
        .ok_or_else(|| ClickError::new(format!("missing loaded Click module `{identity}`")))?;
    states.insert(identity.to_string(), VisitState::Visiting);
    stack.push(identity.to_string());
    let mut imports = module.imports().to_vec();
    imports.sort();
    imports.dedup();
    for imported in imports {
        visit_module(&imported, modules, states, stack, order)?;
    }
    stack.pop();
    states.insert(identity.to_string(), VisitState::Complete);
    order.push(identity.to_string());
    Ok(())
}

fn bounded_chain(chain: &[String]) -> String {
    const SHOWN: usize = 12;
    if chain.len() <= SHOWN {
        return chain.join(" -> ");
    }
    format!(
        "{} -> ... {} more",
        chain[..SHOWN].join(" -> "),
        chain.len() - SHOWN
    )
}

fn transitive_imports(
    identity: &str,
    modules: &BTreeMap<String, &ClickModuleSource>,
) -> Result<Vec<String>, ClickError> {
    let mut seen = BTreeSet::new();
    let mut pending = modules
        .get(identity)
        .ok_or_else(|| ClickError::new(format!("missing loaded Click module `{identity}`")))?
        .imports()
        .to_vec();
    while let Some(next) = pending.pop() {
        if !seen.insert(next.clone()) {
            continue;
        }
        let module = modules
            .get(&next)
            .ok_or_else(|| ClickError::new(format!("missing loaded Click module `{next}`")))?;
        pending.extend(module.imports().iter().cloned());
    }
    Ok(seen.into_iter().collect())
}

fn local_identities(file: &ClickFile) -> Vec<DeclarationIdentity> {
    file.algebraic_type_definitions()
        .iter()
        .map(|definition| DeclarationIdentity::AlgebraicType(definition.name().to_string()))
        .chain(
            file.predicate_definitions()
                .iter()
                .map(|definition| DeclarationIdentity::Predicate(definition.name().to_string())),
        )
        .chain(
            file.click_function_definitions()
                .iter()
                .map(|definition| DeclarationIdentity::Function(definition.name().to_string())),
        )
        .chain(
            file.resource_definitions()
                .iter()
                .map(|definition| DeclarationIdentity::Resource(definition.name().to_string())),
        )
        .chain(
            file.theorem_definitions()
                .iter()
                .map(|definition| DeclarationIdentity::Theorem(definition.name().to_string())),
        )
        .chain(
            file.contract_definitions()
                .iter()
                .map(|definition| DeclarationIdentity::Contract(definition.name().to_string())),
        )
        .chain(file.function_blocks().iter().map(|definition| {
            DeclarationIdentity::CFunction(definition.signature().name().to_string())
        }))
        .collect()
}

fn assign_local_owners(file: &mut ClickFile, identity: &str) -> Result<(), ClickError> {
    for declaration in local_identities(file) {
        if file
            .declaration_owners
            .insert(declaration.clone(), identity.to_string())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate declaration {declaration:?} in module `{identity}`"
            )));
        }
    }
    file.entry_module = Some(identity.to_string());
    Ok(())
}

fn merge_modules(
    imported: &[String],
    entry: &str,
    locals: &BTreeMap<String, ClickFile>,
) -> Result<ClickFile, ClickError> {
    let mut identities = imported.to_vec();
    identities.sort();
    identities.dedup();
    identities.retain(|identity| identity != entry);
    identities.push(entry.to_string());
    let mut merged = ClickFile {
        imports: Vec::new(),
        verifying_sources: Vec::new(),
        c_target: None,
        thread_runtime: Default::default(),
        algebraic_type_definitions: Vec::new(),
        predicate_definitions: Vec::new(),
        click_function_definitions: Vec::new(),
        resource_definitions: Vec::new(),
        theorem_definitions: Vec::new(),
        contract_definitions: Vec::new(),
        function_blocks: Vec::new(),
        declaration_owners: BTreeMap::new(),
        entry_module: Some(entry.to_string()),
    };
    for identity in identities {
        let local = locals
            .get(&identity)
            .ok_or_else(|| ClickError::new(format!("module `{identity}` was not parsed")))?;
        for (declaration, owner) in &local.declaration_owners {
            if let Some(previous) = merged
                .declaration_owners
                .insert(declaration.clone(), owner.clone())
                && previous != *owner
            {
                return Err(ClickError::new(format!(
                    "conflicting declaration {declaration:?} in modules `{previous}` and `{owner}`"
                )));
            }
        }
        // One project selects exactly one C implementation target: its
        // sources are preprocessed once, and its proofs carry one target in
        // their artifact identity. A module may restate the project's target
        // but never contradict it.
        if let Some(declared) = local.c_target {
            if let Some(previous) = merged.c_target
                && previous != declared
            {
                return Err(ClickError::new(format!(
                    "module `{identity}` selects C target `{}`, but another module of this project selects `{}`",
                    declared.name(),
                    previous.name()
                )));
            }
            merged.c_target = Some(declared);
        }
        if local.thread_runtime != Default::default() {
            if merged.thread_runtime != Default::default()
                && merged.thread_runtime != local.thread_runtime
            {
                return Err(ClickError::new(format!(
                    "module `{identity}` selects a conflicting C thread runtime"
                )));
            }
            merged.thread_runtime = local.thread_runtime;
        }
        if identity == entry {
            merged.imports = local.imports.clone();
            merged.verifying_sources = local.verifying_sources.clone();
            merged.contract_definitions = local.contract_definitions.clone();
            merged.function_blocks = local.function_blocks.clone();
        }
        merged
            .algebraic_type_definitions
            .extend(local.algebraic_type_definitions.iter().cloned());
        merged
            .predicate_definitions
            .extend(local.predicate_definitions.iter().cloned());
        merged
            .click_function_definitions
            .extend(local.click_function_definitions.iter().cloned());
        merged
            .resource_definitions
            .extend(local.resource_definitions.iter().cloned());
        merged.theorem_definitions.extend(
            local
                .theorem_definitions
                .iter()
                .map(clone_theorem_definition_iteratively),
        );
    }
    Ok(merged)
}

pub(in crate::surface) fn reject_theorem_justification_cycles(
    file: &ClickFile,
) -> Result<(), ClickError> {
    let known = file
        .theorem_definitions()
        .iter()
        .map(|theorem| theorem.name().to_string())
        .collect::<BTreeSet<_>>();
    let mut graph = BTreeMap::<String, BTreeSet<String>>::new();
    for theorem in file.theorem_definitions() {
        let mut dependencies = BTreeSet::new();
        for ensure in theorem.ensures() {
            verification::collect_applied_theorems_from_proof(&ensure.proof, &mut dependencies);
        }
        dependencies.retain(|dependency| known.contains(dependency));
        graph.insert(theorem.name().to_string(), dependencies);
    }
    let mut permanent = BTreeSet::new();
    let mut visiting = Vec::new();
    for theorem in graph.keys() {
        visit_theorem(theorem, &graph, &mut permanent, &mut visiting)?;
    }
    Ok(())
}

fn visit_theorem(
    theorem: &str,
    graph: &BTreeMap<String, BTreeSet<String>>,
    permanent: &mut BTreeSet<String>,
    visiting: &mut Vec<String>,
) -> Result<(), ClickError> {
    if permanent.contains(theorem) {
        return Ok(());
    }
    if let Some(start) = visiting.iter().position(|name| name == theorem) {
        let mut cycle = visiting[start..].to_vec();
        cycle.push(theorem.to_string());
        return Err(ClickError::new(format!(
            "circular theorem justification: {}",
            bounded_chain(&cycle)
        )));
    }
    visiting.push(theorem.to_string());
    for dependency in graph.get(theorem).into_iter().flatten() {
        visit_theorem(dependency, graph, permanent, visiting)?;
    }
    visiting.pop();
    permanent.insert(theorem.to_string());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn three_file_project(entry_source: &str) -> ClickProject {
        ClickProject::new(
            "proofs/entry.click",
            [
                ClickModuleSource::new(
                    "models/list.click",
                    r#"
spec enum SmallList { Nil, Cons(int32, SmallList), }
function list_head(xs: SmallList) -> int32 {
    match xs { SmallList::Nil => 0, SmallList::Cons(head, tail) => head, }
}
predicate list_empty(xs: SmallList) { xs == SmallList::Nil }
abstract resource list_token(key: int32);
theorem imported_false(x: int32) {
    ensures x == x + 1 by { simp(); }
}
"#,
                    [],
                ),
                ClickModuleSource::new(
                    "models/tree.click",
                    r#"
import "list.click";
spec enum SmallTree { Empty, Node(SmallList), }
function tree_head(tree: SmallTree) -> int32 {
    match tree { SmallTree::Empty => 0, SmallTree::Node(xs) => list_head(xs), }
}
predicate tree_empty(tree: SmallTree) { tree == SmallTree::Empty }
abstract resource tree_token(key: int32);
"#,
                    ["models/list.click".to_string()],
                ),
                ClickModuleSource::new(
                    "proofs/entry.click",
                    entry_source,
                    ["models/tree.click".to_string()],
                ),
            ],
        )
    }

    /// A project preprocesses its C once and records one target in every
    /// proof artifact, so its modules must agree on the selected target. An
    /// imported module may restate the entry module's selection.
    #[test]
    fn project_modules_must_agree_on_the_selected_c_target() {
        let agreeing = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "library.click",
                    "target \"x86_64-linux-userspace\";\npredicate positive(x: int32) { x > 0 }\n",
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"library.click\";\ntarget \"x86_64-linux-userspace\";\n",
                    ["library.click".to_string()],
                ),
            ],
        );
        assert_eq!(
            super::super::selected_project_c_target(&agreeing).expect("agreeing targets"),
            crate::languages::c::target::CTarget::X86_64LinuxUserspace
        );
        let file = resolve_click_project(&agreeing, &[]).expect("agreeing module graph resolves");
        assert_eq!(
            file.selected_c_target(),
            crate::languages::c::target::CTarget::X86_64LinuxUserspace
        );

        let conflicting = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "library.click",
                    "target \"x86_64-linux-userspace\";\npredicate positive(x: int32) { x > 0 }\n",
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"library.click\";\ntarget \"x86_64-linux-kernel\";\n",
                    ["library.click".to_string()],
                ),
            ],
        );
        let error = super::super::selected_project_c_target(&conflicting)
            .expect_err("conflicting module targets");
        assert!(error.message().contains("selects C target"), "{error:?}");
        let error =
            resolve_click_project(&conflicting, &[]).expect_err("conflicting module targets");
        assert!(error.message().contains("selects C target"), "{error:?}");
    }

    #[test]
    fn transitive_imports_supply_interfaces_without_running_imported_proofs() {
        let project = three_file_project(
            r#"
import "../models/tree.click";
theorem local_conditional(x: int32) {
    ensures x == x + 1 by { apply(imported_false(x)); assumption(); }
}
"#,
        );
        let file = resolve_click_project(&project, &[]).expect("module graph should resolve");
        assert!(
            file.algebraic_type_definitions()
                .iter()
                .any(|definition| definition.name() == "SmallList")
        );
        super::proof::PROVED_THEOREMS.with(|proved| proved.borrow_mut().clear());
        verify_c0_project(&project, &[])
            .expect("the local theorem should assume the imported theorem statement");
        super::proof::PROVED_THEOREMS.with(|proved| {
            assert_eq!(proved.borrow().as_slice(), ["local_conditional"]);
        });

        let library = ClickProject::new("models/list.click", [project.modules()[0].clone()]);
        let error = verify_c0_project(&library, &[])
            .expect_err("selecting the imported theorem's own failing proof must fail");
        assert!(error.message().contains("models/list.click"), "{error:?}");
    }

    #[test]
    fn imported_theorem_statement_can_certify_a_selected_c_contract() {
        let project = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "library.click",
                    "theorem false_step(x: int32) { ensures x == x + 1 by simp; }",
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    r#"
import "library.click";
verifying "test.c";
int32 identity(int32 x) {
    ensures result == x + 1 by {
        execute();
        apply(false_step(result));
        assumption();
    }
}
"#,
                    ["library.click".to_string()],
                ),
            ],
        );
        let c = "int identity(int x) { return x; }";
        verify_c0_project(&project, &[("test.c", c)])
            .expect("the selected C proof may assume the imported theorem statement");
        let library = ClickProject::new("library.click", [project.modules()[0].clone()]);
        verify_c0_project(&library, &[])
            .expect_err("selecting the theorem itself must check and reject its proof");
    }

    #[test]
    fn artifacts_bind_imported_inputs_and_retain_the_selection_boundary() {
        let entry = ClickModuleSource::new(
            "entry.click",
            r#"
import "library.click";
verifying "test.c";
int32 identity(int32 x) { ensures result == x by { execute(); simp(); } }
"#,
            ["library.click".to_string()],
        );
        let library = ClickModuleSource::new(
            "library.click",
            "theorem library_fact(x: int32) { ensures x == x by simp; }",
            [],
        );
        let c = [("test.c", "int identity(int x) { return x; }")];
        let first = ClickProject::new("entry.click", [entry.clone(), library.clone()]);
        let reordered = ClickProject::new("entry.click", [library.clone(), entry.clone()]);
        assert_eq!(
            c0_project_selected_proof_names(&first, &c).unwrap(),
            ["function:identity"]
        );
        let first_artifact = verify_c0_project(&first, &c).unwrap().remove(0);
        let reordered_artifact = verify_c0_project(&reordered, &c).unwrap().remove(0);
        assert_eq!(
            first_artifact.artifact_identity,
            reordered_artifact.artifact_identity
        );
        let selection = first_artifact.selection.expect("selection metadata");
        assert_eq!(selection.entry_module.as_deref(), Some("entry.click"));
        assert_eq!(selection.selected_proofs, ["function:identity"]);
        assert_eq!(selection.assumed_theorems, ["library_fact"]);

        let changed = ClickProject::new(
            "entry.click",
            [
                entry,
                ClickModuleSource::new(
                    "library.click",
                    "# changed imported input\ntheorem library_fact(x: int32) { ensures x == x by simp; }",
                    [],
                ),
            ],
        );
        let changed_artifact = verify_c0_project(&changed, &c).unwrap().remove(0);
        assert_ne!(
            reordered_artifact.artifact_identity,
            changed_artifact.artifact_identity
        );
    }

    #[test]
    fn location_inventory_expansion_and_session_keep_imported_proofs_unselected() {
        let project = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "library.click",
                    "theorem imported_bad() { ensures 0 == 1 by simp; }",
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"library.click\";\ntheorem local_ok() { ensures 0 == 0 by auto; }",
                    ["library.click".to_string()],
                ),
            ],
        );
        let sites = expansion::c0_project_smart_tactic_source_sites(&project, &[]).unwrap();
        assert_eq!(sites.len(), 1);
        assert_eq!(sites[0].claim_label, "local_ok.ensures_0");
        let position = expansion::c0_project_tactic_source_position(
            &project,
            &[],
            &sites[0].claim_label,
            sites[0].source_index,
        )
        .unwrap();
        let expanded = expansion::expand_c0_project_tactic_source_at(
            &project,
            &[],
            position.line,
            position.column,
        )
        .unwrap();
        let rewritten = project.with_entry_source(expanded.clone());
        assert_eq!(
            rewritten.modules()[0].source(),
            "theorem imported_bad() { ensures 0 == 1 by simp; }"
        );
        let rewritten_position =
            expansion::c0_project_tactic_source_position(&rewritten, &[], "local_ok.ensures_0", 0)
                .unwrap();
        verify_c0_project_at(
            &rewritten,
            &[],
            rewritten_position.line,
            rewritten_position.column,
        )
        .expect("the expanded local theorem should verify without the imported proof");
        let (session, _) = C0VerificationSession::new_project(&project, &[]).unwrap();
        session
            .verify_at_project(
                &expanded,
                rewritten_position.line,
                rewritten_position.column,
            )
            .expect("an audit-style retained session should preserve the import boundary");
    }

    #[test]
    fn location_selection_does_not_execute_a_failing_local_sibling() {
        let project = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "library.click",
                    "theorem imported_bad() { ensures 0 == 1 by simp; }",
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    r#"
import "library.click";
theorem selected_ok() { ensures 0 == 0 by auto; }
theorem sibling_bad() { ensures 0 == 1 by simp; }
"#,
                    ["library.click".to_string()],
                ),
            ],
        );
        let position =
            expansion::c0_project_tactic_source_position(&project, &[], "selected_ok.ensures_0", 0)
                .unwrap();
        super::proof::PROVED_THEOREMS.with(|proved| proved.borrow_mut().clear());
        verify_c0_project_at(&project, &[], position.line, position.column)
            .expect("the selected proof should assume declarations without running siblings");
        super::proof::PROVED_THEOREMS.with(|proved| {
            assert_eq!(proved.borrow().as_slice(), ["selected_ok"]);
        });
        verify_c0_project(&project, &[])
            .expect_err("file selection must still execute and reject the local sibling proof");
    }

    #[test]
    fn prepared_c_inputs_use_the_same_module_selection_and_expansion_path() {
        let project = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "library.click",
                    "theorem imported_ok(x: int32) { ensures x == x by simp; }",
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"library.click\"; verifying \"test.c\"; int32 identity(int32 x) { ensures result == x by auto; }",
                    ["library.click".to_string()],
                ),
            ],
        );
        let imports = [
            crate::languages::c::compiler_import::PreparedCImport::for_test(
                "test.c",
                "int identity(int x) { return x; }",
            ),
        ];
        verify_c0_prepared_project(&project, &imports).unwrap();
        let sites =
            expansion::c0_prepared_project_smart_tactic_source_sites(&project, &imports).unwrap();
        assert_eq!(sites.len(), 1);
        let position = expansion::c0_prepared_project_tactic_source_position(
            &project,
            &imports,
            &sites[0].claim_label,
            sites[0].source_index,
        )
        .unwrap();
        let expanded = expansion::expand_c0_prepared_project_tactic_source_at(
            &project,
            &imports,
            position.line,
            position.column,
        )
        .unwrap();
        let rewritten = project.with_entry_source(expanded);
        let rewritten_position = expansion::c0_prepared_project_tactic_source_position(
            &rewritten,
            &imports,
            "identity.ensures_0",
            0,
        )
        .unwrap();
        verify_c0_prepared_project_at(
            &rewritten,
            &imports,
            rewritten_position.line,
            rewritten_position.column,
        )
        .unwrap();
    }

    #[test]
    fn module_cannot_capture_an_importer_only_name() {
        let project = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "library.click",
                    "function bad(x: int32) -> int32 { importer_only(x) }",
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"library.click\"; function importer_only(x: int32) -> int32 { x }",
                    ["library.click".to_string()],
                ),
            ],
        );
        let error = resolve_click_project(&project, &[])
            .expect_err("an importer declaration must not satisfy a library reference");
        assert!(
            error.message().contains("importer_only"),
            "{}",
            error.message()
        );
    }

    #[test]
    fn imported_proof_ownership_and_collisions_are_rejected() {
        let verifying = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new("library.click", "verifying \"library.c\";", []),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"library.click\"; theorem ok() { ensures 0 == 0 by simp; }",
                    ["library.click".to_string()],
                ),
            ],
        );
        let error = resolve_click_project(&verifying, &[])
            .expect_err("an imported module cannot own C verification declarations");
        assert!(error.message().contains("entry.click:1:"), "{error:?}");
        assert!(error.message().contains("library.click"), "{error:?}");

        let collision = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new("left.click", "function same(x: int32) -> int32 { x }", []),
                ClickModuleSource::new("right.click", "function same(x: int32) -> int32 { x }", []),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"left.click\"; import \"right.click\";",
                    ["left.click".to_string(), "right.click".to_string()],
                ),
            ],
        );
        let error = resolve_click_project(&collision, &[])
            .expect_err("unqualified imported names must not be ambiguous");
        assert!(error.message().contains("left.click"), "{error:?}");
        assert!(error.message().contains("right.click"), "{error:?}");

        let local_collision = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "library.click",
                    "function same(x: int32) -> int32 { x }",
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"library.click\"; function same(x: int32) -> int32 { x }",
                    ["library.click".to_string()],
                ),
            ],
        );
        let error = resolve_click_project(&local_collision, &[])
            .expect_err("a local declaration cannot shadow an imported declaration");
        assert!(error.message().contains("library.click"), "{error:?}");
        assert!(error.message().contains("entry.click"), "{error:?}");

        let builtin_collision = ClickProject::new(
            "entry.click",
            [ClickModuleSource::new(
                "entry.click",
                "function to_int32(x: int32) -> int32 { x }",
                [],
            )],
        );
        let error = resolve_click_project(&builtin_collision, &[])
            .expect_err("a declaration cannot shadow a built-in conversion");
        assert!(error.message().contains("built-in"), "{error:?}");
    }

    #[test]
    fn diamond_deduplicates_shared_declarations_and_import_order() {
        let modules = [
            ClickModuleSource::new("shared.click", "spec enum Shared { One, }", []),
            ClickModuleSource::new(
                "left.click",
                "import \"shared.click\"; function left(x: Shared) -> Shared { x }",
                ["shared.click".to_string()],
            ),
            ClickModuleSource::new(
                "right.click",
                "import \"shared.click\"; function right(x: Shared) -> Shared { x }",
                ["shared.click".to_string()],
            ),
            ClickModuleSource::new(
                "entry.click",
                "import \"right.click\"; import \"left.click\"; theorem ok() { ensures 0 == 0 by simp; }",
                ["right.click".to_string(), "left.click".to_string()],
            ),
        ];
        let first = ClickProject::new("entry.click", modules.clone());
        let mut reversed = modules;
        reversed[3] = ClickModuleSource::new(
            "entry.click",
            "import \"left.click\"; import \"right.click\"; theorem ok() { ensures 0 == 0 by simp; }",
            ["left.click".to_string(), "right.click".to_string()],
        );
        let second = ClickProject::new("entry.click", reversed);
        let first_file = resolve_click_project(&first, &[]).expect("first diamond");
        let second_file = resolve_click_project(&second, &[]).expect("reordered diamond");
        assert_eq!(
            first_file
                .algebraic_type_definitions()
                .iter()
                .filter(|definition| definition.name() == "Shared")
                .count(),
            1
        );
        assert_eq!(
            first_file.click_function_definitions(),
            second_file.click_function_definitions()
        );
    }

    #[test]
    fn import_and_theorem_cycles_are_rejected_before_selection() {
        let import_cycle = ClickProject::new(
            "a.click",
            [
                ClickModuleSource::new(
                    "a.click",
                    "import \"b.click\"; theorem a() { ensures 0 == 0 by simp; }",
                    ["b.click".to_string()],
                ),
                ClickModuleSource::new(
                    "b.click",
                    "import \"a.click\"; theorem b() { ensures 0 == 0 by simp; }",
                    ["a.click".to_string()],
                ),
            ],
        );
        assert!(
            resolve_click_project(&import_cycle, &[])
                .unwrap_err()
                .message()
                .contains("import cycle")
        );

        let theorem_cycle = ClickProject::new(
            "cycle.click",
            [ClickModuleSource::new(
                "cycle.click",
                r#"
theorem a() { ensures 0 == 0 by { apply(b()); assumption(); } }
theorem b() { ensures 0 == 0 by { apply(a()); assumption(); } }
"#,
                [],
            )],
        );
        assert!(
            resolve_click_project(&theorem_cycle, &[])
                .unwrap_err()
                .message()
                .contains("circular theorem justification")
        );

        let self_cycle = ClickProject::new(
            "self.click",
            [ClickModuleSource::new(
                "self.click",
                "theorem self_cycle() { ensures 0 == 0 by { apply(self_cycle()); assumption(); } }",
                [],
            )],
        );
        assert!(
            resolve_click_project(&self_cycle, &[])
                .unwrap_err()
                .message()
                .contains("self_cycle -> self_cycle")
        );

        let invalid_recursion = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "bad.click",
                    "function recurse(x: int32) -> int32 { recurse(x) }",
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"bad.click\"; theorem selected() { ensures 0 == 0 by simp; }",
                    ["bad.click".to_string()],
                ),
            ],
        );
        let error = resolve_click_project(&invalid_recursion, &[])
            .expect_err("partial selection must not hide invalid recursion");
        assert!(error.message().contains("recurse"), "{error:?}");

        let checked_recursion = ClickProject::new(
            "entry.click",
            [
                ClickModuleSource::new(
                    "good.click",
                    r#"
spec enum Countdown { Done, More(Countdown), }
function finish(x: Countdown) -> int32 decreases x {
    match x { Countdown::Done => 0, Countdown::More(previous) => finish(previous), }
}
"#,
                    [],
                ),
                ClickModuleSource::new(
                    "entry.click",
                    "import \"good.click\"; theorem selected() { ensures 0 == 0 by simp; }",
                    ["good.click".to_string()],
                ),
            ],
        );
        resolve_click_project(&checked_recursion, &[])
            .expect("the existing checked structural recursion rule remains valid");
    }
}
