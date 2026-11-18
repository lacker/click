use super::constructor_inference::{CallKind, ConstructorTypes};
use super::*;

#[cfg(test)]
mod tests;

#[derive(Clone, Debug, Eq, PartialEq)]
struct DeclaredResourceInfo {
    fields: std::sync::Arc<BTreeMap<String, (usize, ClickType)>>,
    field_schema: Option<crate::kernel::ResourceFieldSchema>,
    parameter_types: Vec<InterfaceType>,
    resource_parameter_families: Vec<String>,
    kind: ResourceKind,
    has_fields: bool,
    /// Declared `authorized resource`.
    authorized: bool,
    /// Each matched-arm child slot of this resource and the resource that
    /// slot declares, or `None` when two arms give one slot name different
    /// resources. A child may name another declared resource, so the slot's
    /// family is a property of this definition rather than of the proof.
    child_slots: std::sync::Arc<BTreeMap<String, Option<String>>>,
    /// The field this resource's body matches on, and each arm's child slots
    /// with their resources ([`CompositeResourceBody::arm_child_slot_resources`]).
    arm_child_slots: std::sync::Arc<Option<(String, BTreeMap<String, BTreeMap<String, String>>)>>,
}

/// Declared resources plus what the expansion has learned about the resource
/// instances a proof names. `let { slot: name } = unfold(parent)` introduces
/// `name` before any definition is available to the parser, so the parser
/// records the parent's family provisionally and the slot decides the real
/// one here.
struct DeclaredResourceScope {
    /// Whether the family rules apply: only `authorized` families are
    /// counted. The standard library's own expansion applies none.
    family_rules: bool,
    definitions: BTreeMap<String, DeclaredResourceInfo>,
    /// What the current proof path has fixed about each instance identity,
    /// in source order. A proof name keeps one identity in its declaration,
    /// so two alternative arms can bind it to different resources; each arm
    /// starts from the state before the alternatives ([`Self::alternatives`]).
    families: std::cell::RefCell<BTreeMap<Variable, InstanceFamily>>,
    /// The previous value of each `families` entry changed since the
    /// declaration began, so an arm's changes can be undone.
    family_log: std::cell::RefCell<Vec<(Variable, Option<InstanceFamily>)>>,
    /// The arms enclosing proof `match`es select, innermost last: the
    /// instance, its field and the variant.
    selected_arms: std::cell::RefCell<Vec<(Variable, String, String)>>,
    unowned_resource_parameters: std::cell::RefCell<BTreeMap<Variable, SurfaceBinder>>,
    /// The enclosing C function's parameters of signed character pointer
    /// type. A resource argument naming one, passed to `uint8` bytes, is
    /// read through its explicit byte view, as a predicate argument is.
    character_parameters: std::cell::RefCell<BTreeSet<String>>,
    /// Fills in the type arguments of constructors that leave them out.
    constructors: ConstructorTypes,
    /// These declarations impose no premises. Index once for the file; their
    /// applications with value arguments need no premise search.
    premise_free_theorems: BTreeSet<String>,
    /// Local induction bindings shadow global theorem signatures and their
    /// premise-free optimization from the declaration through this block.
    local_hypotheses: std::cell::RefCell<PersistentBinderMap<()>>,
}

impl DeclaredResourceScope {
    /// Binder IDs are allocated by each module's parser. Only the enclosing
    /// declaration gives them meaning; another declaration (especially in an
    /// importer) may reuse an ID for a different resource family. Clear only
    /// the preceding declaration's learned instances, retaining the shared
    /// immutable resource definitions without a per-declaration clone.
    fn begin_declaration(&self) {
        self.families.borrow_mut().clear();
        self.family_log.borrow_mut().clear();
        self.unowned_resource_parameters.borrow_mut().clear();
        self.character_parameters.borrow_mut().clear();
    }

    /// `arguments` of a resource whose parameters have `parameter_types`,
    /// expanded, with the C-string bridge of a predicate argument: a bare
    /// name of a signed character pointer parameter passed to `uint8` bytes
    /// becomes its explicit byte view
    /// ([`crate::surface::lowering::character_byte_view`]).
    fn expand_arguments(
        &self,
        arguments: Vec<ContractExpression>,
        parameter_types: &[InterfaceType],
    ) -> Result<Vec<ContractExpression>, ClickError> {
        let character_parameters = self.character_parameters.borrow();
        arguments
            .into_iter()
            .enumerate()
            .map(|(index, argument)| {
                let named = match &argument {
                    ContractExpression::ProgramExpression(ProgramExpression::Variable(
                        crate::kernel::BindingName::Named(name),
                    ))
                    | ContractExpression::Binding(name)
                    | ContractExpression::ProgramBinding(name) => Some(name.as_str()),
                    _ => None,
                };
                match (named, parameter_types.get(index)) {
                    (
                        Some(name),
                        Some(InterfaceType::UInt8Pointer | InterfaceType::UInt8Array(_)),
                    ) if character_parameters.contains(name) => {
                        Ok(crate::surface::lowering::character_byte_view(name))
                    }
                    _ => expand_declared_resource_expression(argument, self),
                }
            })
            .collect()
    }

    fn get(&self, name: &str) -> Option<&DeclaredResourceInfo> {
        self.definitions.get(name)
    }

    fn contains_key(&self, name: &str) -> bool {
        self.definitions.contains_key(name)
    }

    fn family(&self, identity: Variable) -> Option<InstanceFamily> {
        self.families.borrow().get(&identity).cloned()
    }

    fn set_family(&self, identity: Variable, family: Option<InstanceFamily>) {
        let previous = match &family {
            Some(family) => self.families.borrow_mut().insert(identity, family.clone()),
            None => self.families.borrow_mut().remove(&identity),
        };
        if previous != family {
            self.family_log.borrow_mut().push((identity, previous));
        }
    }

    /// The resource of the instance `identity`, if the current path has
    /// fixed it.
    fn instance_resource(&self, identity: Variable) -> Option<String> {
        match self.family(identity)? {
            InstanceFamily::Child(name) | InstanceFamily::Instance(name) => Some(name),
            InstanceFamily::FieldValue | InstanceFamily::Ambiguous(_) => None,
        }
    }

    /// Refuses a use of `name` when alternative paths bound it to
    /// instances of different resources.
    fn refuse_ambiguous(&self, identity: Variable, name: &str) -> Result<(), ClickError> {
        match self.family(identity) {
            Some(InstanceFamily::Ambiguous(resources)) => Err(ClickError::new(format!(
                "`{name}` names a `{}` instance on one path and a `{}` instance on another; give each its own name",
                resources.0, resources.1
            ))),
            _ => Ok(()),
        }
    }

    /// Record the resource of `identity`. An explicit `fold(name(...), ...)`
    /// construction names its own resource, so it also replaces whatever
    /// child slot the identity was introduced by.
    fn record_instance(&self, identity: Variable, name: &str, construction: bool) {
        if !construction && matches!(self.family(identity), Some(InstanceFamily::Child(_))) {
            return;
        }
        self.set_family(identity, Some(InstanceFamily::Instance(name.to_string())));
    }

    fn record_field_binder(&self, identity: Variable) {
        self.set_family(identity, Some(InstanceFamily::FieldValue));
    }

    fn record_child(&self, identity: Variable, name: &str) {
        self.set_family(identity, Some(InstanceFamily::Child(name.to_string())));
    }

    /// The resource slot `slot` of `parent`'s instance `identity` owns in
    /// the arm an enclosing proof `match` on its matched field selects.
    fn selected_arm_slot(&self, identity: Variable, parent: &str, slot: &str) -> Option<String> {
        let info = self.get(parent)?;
        let (field, arms) = info.arm_child_slots.as_ref().as_ref()?;
        let selected = self.selected_arms.borrow();
        let (_, _, variant) = selected
            .iter()
            .rev()
            .find(|(selected, selected_field, _)| {
                *selected == identity && selected_field == field
            })?;
        arms.get(variant)?.get(slot).cloned()
    }

    /// Begins alternative arms: each arm ([`Self::arm`]) starts from the
    /// state here, and [`Self::finish_alternatives`] joins them.
    fn begin_alternatives(&self) -> Alternatives {
        Alternatives {
            start: self.family_log.borrow().len(),
            outcomes: Default::default(),
        }
    }

    /// Expands one alternative arm, then undoes its changes, keeping what
    /// it left for the identities it changed.
    fn arm<T>(
        &self,
        alternatives: &Alternatives,
        expand: impl FnOnce() -> Result<T, ClickError>,
    ) -> Result<T, ClickError> {
        let expanded = expand()?;
        let changes = self.family_log.borrow_mut().split_off(alternatives.start);
        let mut outcome = BTreeMap::new();
        for (identity, _) in &changes {
            outcome
                .entry(*identity)
                .or_insert_with(|| self.family(*identity));
        }
        let mut families = self.families.borrow_mut();
        for (identity, previous) in changes.into_iter().rev() {
            match previous {
                Some(family) => families.insert(identity, family),
                None => families.remove(&identity),
            };
        }
        alternatives.outcomes.borrow_mut().push(outcome);
        Ok(expanded)
    }

    /// After alternative arms, an instance holds what every arm agrees on.
    /// An arm that left it alone agrees with the state before them, unless
    /// that held nothing. Arms that gave it different resources leave it
    /// ambiguous, so a later use is refused rather than read with one arm's
    /// resource. The work is the arms' own changes.
    fn finish_alternatives(&self, alternatives: Alternatives) {
        let outcomes = alternatives.outcomes.into_inner();
        let changed = outcomes
            .iter()
            .flat_map(BTreeMap::keys)
            .copied()
            .collect::<BTreeSet<_>>();
        for identity in changed {
            let before = self.family(identity);
            let joined = outcomes
                .iter()
                .map(|outcome| outcome.get(&identity).cloned().unwrap_or(before.clone()))
                .reduce(join_instance_families)
                .flatten();
            self.set_family(identity, joined);
        }
    }
}

/// Alternative arms in progress ([`DeclaredResourceScope::begin_alternatives`]).
struct Alternatives {
    start: usize,
    outcomes: std::cell::RefCell<Vec<BTreeMap<Variable, Option<InstanceFamily>>>>,
}

fn join_instance_families(
    left: Option<InstanceFamily>,
    right: Option<InstanceFamily>,
) -> Option<InstanceFamily> {
    use InstanceFamily::*;
    let (left, right) = match (left, right) {
        (None, family) | (family, None) => return family,
        (Some(left), Some(right)) => (left, right),
    };
    match (left, right) {
        (Ambiguous(resources), _) | (_, Ambiguous(resources)) => Some(Ambiguous(resources)),
        (left, right) if left == right => Some(left),
        (FieldValue, _) | (_, FieldValue) => Some(FieldValue),
        (Child(left) | Instance(left), Child(right) | Instance(right)) if left == right => {
            Some(Child(left))
        }
        (Child(left) | Instance(left), Child(right) | Instance(right)) => {
            Some(Ambiguous(Box::new((left, right))))
        }
    }
}

/// What a proof path has fixed about one resource instance identity.
#[derive(Clone, Debug, PartialEq, Eq)]
enum InstanceFamily {
    /// A child an unfold introduced, of its slot's resource. A later use
    /// under another resource keeps the slot's: the parser could only
    /// record the parent's.
    Child(String),
    /// An instance of a resource a declaration, fold or call named.
    Instance(String),
    /// A name an unfold pattern bound to a scalar field's value.
    FieldValue,
    /// Alternative paths gave it these two resources.
    Ambiguous(Box<(String, String)>),
}

// Only immutable surface syntax is shared. Lowered environments, authorities,
// and certificates must still be constructed in each verification session.
// Only a successful parse is shared: the parse charges the run that performs
// it, so a run whose budget or containment bound expires mid-parse fails that
// run alone instead of every later run in the process.
static LIBRARY_MODULES: std::sync::OnceLock<Vec<LibraryModule>> = std::sync::OnceLock::new();
static STANDARD_LIBRARY_INITIALIZATION: std::sync::Mutex<()> = std::sync::Mutex::new(());
/// Every library selection built in this process, by its module mask. A
/// selection is a few modules' declarations, and a process sees at most one
/// per distinct set of library imports, so each is built once and kept.
static LIBRARY_SELECTIONS: std::sync::Mutex<BTreeMap<u64, &'static LibrarySelection>> =
    std::sync::Mutex::new(BTreeMap::new());

#[cfg(test)]
static STANDARD_LIBRARY_PARSES: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// The Click library modules every file sees without an import. A C
/// program's declarations bring the library interfaces they name, such as
/// `click::c::string`; see `ProgramLayouts::library_modules`.
const IMPLICIT_LIBRARY_MODULES: &[&str] = &[
    "library/primitives.click",
    "library/nat.click",
    "library/list.click",
    "library/option.click",
    "library/result.click",
    "library/c/builtins.click",
];

/// The `library/` identities of the implicit Click library modules.
pub(in crate::surface) fn implicit_library_modules() -> impl Iterator<Item = &'static str> {
    IMPLICIT_LIBRARY_MODULES.iter().copied()
}

/// One parsed Click library module and the mask of the modules it needs: its
/// own bit and those of its library imports, transitively.
struct LibraryModule {
    file: ClickFile,
    closure: u64,
}

/// The declarations of a set of Click library modules in library order, with
/// a name index of its theorems.
#[derive(Debug)]
pub(in crate::surface) struct LibrarySelection {
    file: ClickFile,
    theorem_index: BTreeMap<String, usize>,
    theorem_conclusions: planning::theorems::TheoremConclusionIndex,
}

impl LibrarySelection {
    /// The library's function blocks, which lead
    /// [`combined_external_function_blocks`].
    pub(in crate::surface) fn function_blocks(&'static self) -> &'static [FunctionBlock] {
        self.file.function_blocks()
    }

    pub(in crate::surface) fn resource_definitions(&'static self) -> &'static [ResourceDefinition] {
        self.file.resource_definitions()
    }

    pub(in crate::surface) fn theorem_definitions(&'static self) -> &'static [TheoremDefinition] {
        self.file.theorem_definitions()
    }

    pub(in crate::surface) fn theorem_index(&'static self) -> &'static BTreeMap<String, usize> {
        &self.theorem_index
    }

    pub(in crate::surface) fn theorem_conclusions(
        &'static self,
    ) -> &'static planning::theorems::TheoremConclusionIndex {
        &self.theorem_conclusions
    }
}

fn library_modules() -> Result<&'static [LibraryModule], ClickError> {
    if let Some(modules) = LIBRARY_MODULES.get() {
        return Ok(modules);
    }
    let _initializing = STANDARD_LIBRARY_INITIALIZATION
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if let Some(modules) = LIBRARY_MODULES.get() {
        return Ok(modules);
    }
    #[cfg(test)]
    STANDARD_LIBRARY_PARSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let modules = load_library_modules(CLICK_LIBRARY_MODULES)?;
    Ok(LIBRARY_MODULES.get_or_init(|| modules))
}

/// The `let` value parameters of the Click library's declaration of the C
/// function `name`: `strlen`'s `let n: uint64;` is `n`. A call map in a
/// program's sidecar names them.
pub(in crate::surface) fn library_program_function_value_parameters(
    name: &str,
) -> Result<Vec<String>, ClickError> {
    Ok(library_modules()?
        .iter()
        .flat_map(|module| module.file.function_blocks())
        .find(|block| block.is_external() && block.signature().name() == name)
        .map(|block| {
            let parameters = block.signature().parameters();
            parameters[parameters.len() - block.witness_count()..]
                .iter()
                .map(|parameter| parameter.name().to_string())
                .collect()
        })
        .unwrap_or_default())
}

/// The library modules visible to `file`: the implicit modules and the
/// file's own library imports, each with its library imports.
fn library_mask(file: &ClickFile) -> Result<u64, ClickError> {
    let modules = library_modules()?;
    let mut mask = 0;
    for identity in IMPLICIT_LIBRARY_MODULES
        .iter()
        .copied()
        .chain(file.library_imports().iter().map(String::as_str))
    {
        let index = library_module_index(identity)?;
        mask |= modules[index].closure;
    }
    Ok(mask)
}

fn library_module_index(identity: &str) -> Result<usize, ClickError> {
    CLICK_LIBRARY_MODULES
        .iter()
        .position(|(module, _)| *module == identity)
        .ok_or_else(|| ClickError::new(format!("unknown Click library module `{identity}`")))
}

/// The Click library as `file` sees it.
pub(in crate::surface) fn file_library(
    file: &ClickFile,
) -> Result<&'static LibrarySelection, ClickError> {
    library_selection(library_mask(file)?)
}

/// Every Click library module. The library's own proofs are checked against
/// this, and a library theorem cited by a certified proof is checked once
/// against the declarations before it.
pub(in crate::surface) fn full_library() -> Result<&'static LibrarySelection, ClickError> {
    library_selection((1u64 << CLICK_LIBRARY_MODULES.len()) - 1)
}

fn library_selection(mask: u64) -> Result<&'static LibrarySelection, ClickError> {
    let modules = library_modules()?;
    if let Some(selection) = LIBRARY_SELECTIONS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .get(&mask)
    {
        return Ok(selection);
    }
    // Built outside the lock: two runs that race build equal selections, and
    // the first one stored is kept. A selection can first be needed in the
    // middle of a proof, and expansion resets the thread's ambient proof
    // source and diagnostic naming, so it is built on its own thread.
    let (file, theorem_index) = std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("click-library-selection".to_string())
            .stack_size(64 * 1024 * 1024)
            .spawn_scoped(scope, || build_library_selection(modules, mask))
            .map_err(|error| {
                ClickError::new(format!(
                    "could not build a Click library selection: {error}"
                ))
            })?
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })?;
    let mut selections = LIBRARY_SELECTIONS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    Ok(*selections.entry(mask).or_insert_with(|| {
        Box::leak(Box::new(LibrarySelection {
            theorem_conclusions: {
                let mut index = planning::theorems::TheoremConclusionIndex::default();
                for (ordinal, theorem) in file.theorem_definitions().iter().enumerate() {
                    index.insert(theorem, ordinal);
                }
                index
            },
            file,
            theorem_index,
        }))
    }))
}

/// The library module position of each Click library theorem.
fn library_theorem_owners() -> Result<&'static BTreeMap<String, usize>, ClickError> {
    static OWNERS: std::sync::OnceLock<BTreeMap<String, usize>> = std::sync::OnceLock::new();
    let modules = library_modules()?;
    Ok(OWNERS.get_or_init(|| {
        modules
            .iter()
            .enumerate()
            .flat_map(|(index, module)| {
                module
                    .file
                    .theorem_definitions()
                    .iter()
                    .map(move |theorem| (theorem.name().to_string(), index))
            })
            .collect()
    }))
}

/// Refuses a theorem a proof in `file` cites by name when the theorem is
/// declared in a Click library module that `file` does not see.
pub(in crate::surface) fn reject_unimported_library_citations(
    file: &ClickFile,
) -> Result<(), ClickError> {
    // Library theorems are cited by their qualified identity, so a file
    // theorem may share a library theorem's bare name.
    let owners = library_theorem_owners()?;
    let mut cited = BTreeSet::new();
    for theorem in file.theorem_definitions() {
        for clause in theorem.ensures() {
            crate::surface::collect_applied_theorems_from_proof(&clause.proof, &mut cited);
        }
    }
    for function in file.function_blocks() {
        if let Some(proof) = function.grouped_proof() {
            crate::surface::collect_applied_theorems_from_proof(proof, &mut cited);
        }
        for clause in function.ensures() {
            crate::surface::collect_applied_theorems_from_proof(&clause.proof, &mut cited);
        }
    }
    if cited.is_empty() {
        return Ok(());
    }
    let local = file
        .theorem_definitions()
        .iter()
        .map(|theorem| theorem.name())
        .collect::<BTreeSet<_>>();
    let visible = library_mask(file)?;
    for name in cited.iter().filter(|name| !local.contains(name.as_str())) {
        if let Some(index) = owners.get(name)
            && visible & (1 << index) == 0
        {
            let bare = name.rsplit("::").next().unwrap_or(name);
            return Err(ClickError::new(format!(
                "unknown theorem `{bare}`{}",
                library_import_hint(name)
            )));
        }
    }
    Ok(())
}

/// The Click library modules, in library order, that declare a theorem
/// among `cited` and that a file importing `imported` does not see.
pub(in crate::surface) fn library_modules_to_import<'a>(
    imported: &[String],
    cited: impl IntoIterator<Item = &'a str>,
) -> Vec<&'static str> {
    let Ok(modules) = library_modules() else {
        return Vec::new();
    };
    let mut visible = 0u64;
    for identity in IMPLICIT_LIBRARY_MODULES
        .iter()
        .copied()
        .chain(imported.iter().map(String::as_str))
    {
        if let Ok(index) = library_module_index(identity) {
            visible |= modules[index].closure;
        }
    }
    let cited = cited.into_iter().collect::<BTreeSet<_>>();
    let mut needed = 0u64;
    for (index, module) in modules.iter().enumerate() {
        if visible & (1 << index) == 0
            && module.file.theorem_definitions().iter().any(|theorem| {
                let name = theorem.name();
                cited.contains(name.rsplit("::").next().unwrap_or(name))
            })
        {
            needed |= 1 << index;
        }
    }
    (0..modules.len())
        .filter(|index| needed & (1 << index) != 0)
        .map(|index| CLICK_LIBRARY_MODULES[index].0)
        .collect()
}

/// The note an unknown-name error adds when `name` is declared in a Click
/// library module that is not implicit, so the fix is that module's import.
pub(in crate::surface) fn library_import_hint(name: &str) -> String {
    static OWNERS: std::sync::OnceLock<BTreeMap<String, &'static str>> = std::sync::OnceLock::new();
    let Ok(modules) = library_modules() else {
        return String::new();
    };
    let owners = OWNERS.get_or_init(|| {
        let implicit = IMPLICIT_LIBRARY_MODULES
            .iter()
            .filter_map(|identity| library_module_index(identity).ok())
            .fold(0, |mask, index| mask | modules[index].closure);
        let mut owners = BTreeMap::new();
        for (index, module) in modules.iter().enumerate() {
            if implicit & (1 << index) != 0 {
                continue;
            }
            let identity = CLICK_LIBRARY_MODULES[index].0;
            let file = &module.file;
            let names = file
                .algebraic_type_definitions()
                .iter()
                .map(|definition| definition.name())
                .chain(
                    file.predicate_definitions()
                        .iter()
                        .map(|definition| definition.name()),
                )
                .chain(
                    file.click_function_definitions()
                        .iter()
                        .map(|definition| definition.name()),
                )
                .chain(
                    file.resource_definitions()
                        .iter()
                        .map(|definition| definition.name()),
                )
                .chain(
                    file.theorem_definitions()
                        .iter()
                        .map(|definition| definition.name()),
                )
                .chain(
                    file.function_blocks()
                        .iter()
                        .map(|block| block.signature().name()),
                );
            for name in names {
                owners.insert(name.to_string(), identity);
            }
        }
        owners
    });
    owners.get(name).map_or_else(String::new, |identity| {
        let path = crate::surface::library_module_path(identity);
        // A library proof sees only the theorems declared above it, since
        // built-in bridges apply library theorems by name without a
        // citation, so a later sibling is out of scope and an import would
        // change nothing.
        let proving_in_same_module = crate::surface::ambient_declaration()
            .is_some_and(|declaration| owners.get(declaration.as_str()) == Some(identity));
        if proving_in_same_module {
            format!(
                "; it is declared later in Click library module `{path}`, and a library proof \
                 can cite only theorems declared above it, so move it above this one"
            )
        } else {
            format!("; it is declared in Click library module `{path}`, so add `import {path};`")
        }
    })
}

fn build_library_selection(
    modules: &[LibraryModule],
    mask: u64,
) -> Result<(ClickFile, BTreeMap<String, usize>), ClickError> {
    let mut file = empty_library_file()?;
    for (index, module) in modules.iter().enumerate() {
        if mask & (1 << index) != 0 {
            append_library_module(&mut file, module.file.clone());
        }
    }
    let file = expand_declared_resource_clauses(file)?;
    let theorem_index = file
        .theorem_definitions()
        .iter()
        .enumerate()
        .map(|(index, theorem)| (theorem.name().to_string(), index))
        .collect();
    Ok((file, theorem_index))
}

/// The whole Click library, for the accessors that are not specific to one
/// file's library imports.
fn standard_library() -> Result<&'static ClickFile, ClickError> {
    Ok(&full_library()?.file)
}

fn empty_library_file() -> Result<ClickFile, ClickError> {
    parser::parse_file_items_for_module(
        "",
        "library",
        0,
        &[],
        &[],
        &[],
        &[],
        &BTreeSet::new(),
        &BTreeSet::new(),
        &BTreeSet::new(),
        &BTreeMap::new(),
        Default::default(),
    )
}

/// Parses each module in library order with the declarations of the modules
/// before it. A module's library imports must name earlier modules.
fn load_library_modules(modules: &[(&str, &str)]) -> Result<Vec<LibraryModule>, ClickError> {
    if modules.len() > 64 {
        return Err(ClickError::new(
            "the Click library has more than 64 modules",
        ));
    }
    let mut loaded: Vec<LibraryModule> = Vec::new();
    let mut context = empty_library_file()?;
    for (position, (identity, source)) in modules.iter().enumerate() {
        let callees = context
            .function_blocks()
            .iter()
            .map(parser::ImportedCallee::Function)
            .chain(
                context
                    .contract_definitions()
                    .iter()
                    .map(parser::ImportedCallee::Contract),
            )
            .collect::<Vec<_>>();
        let resources = context.resource_definitions().iter().collect::<Vec<_>>();
        let module = parser::parse_file_items_for_module(
            source,
            identity,
            0,
            context.algebraic_type_definitions(),
            &callees,
            &resources,
            &[],
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeSet::new(),
            &BTreeMap::new(),
            Default::default(),
        )?;
        if !module.verifying_sources().is_empty()
            || !module.imports().is_empty()
            || module
                .function_blocks()
                .iter()
                .any(|function| !function.is_external())
        {
            return Err(ClickError::new(format!(
                "Click library module `{identity}` must not contain file imports, verifying sources, or body-bearing C function specs"
            )));
        }
        let mut closure = 1u64 << position;
        for import in module.library_imports() {
            let index = modules[..position]
                .iter()
                .position(|(earlier, _)| earlier == import)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "Click library module `{identity}` imports `{import}`, which is not an earlier library module"
                    ))
                })?;
            closure |= loaded[index].closure;
        }
        let mut module = module;
        let path = crate::surface::library_module_path(identity);
        for theorem in &mut module.theorem_definitions {
            theorem.name = format!("{path}::{}", theorem.name);
        }
        for function in &mut module.click_function_definitions {
            if crate::surface::names::is_qualified_declaration(identity, &function.name) {
                function.name = format!("{path}::{}", function.name);
            }
        }
        for predicate in &mut module.predicate_definitions {
            if crate::surface::names::is_qualified_declaration(identity, &predicate.name) {
                predicate.name = format!("{path}::{}", predicate.name);
            }
        }
        append_library_module(&mut context, module.clone());
        loaded.push(LibraryModule {
            file: module,
            closure,
        });
    }
    Ok(loaded)
}

#[cfg(test)]
fn load_standard_library(modules: &[(&str, &str)]) -> Result<ClickFile, ClickError> {
    let mut file = empty_library_file()?;
    for module in load_library_modules(modules)? {
        append_library_module(&mut file, module.file);
    }
    expand_declared_resource_clauses(file)
}

/// Appends one library module's declarations after the earlier modules', so
/// the library keeps one declaration order across its files.
fn append_library_module(file: &mut ClickFile, module: ClickFile) {
    std::sync::Arc::make_mut(&mut file.program_function_names).extend(
        module
            .program_function_names
            .iter()
            .map(|(spelling, name)| (spelling.clone(), name.clone())),
    );
    file.imports.extend(module.imports);
    file.library_imports.extend(module.library_imports);
    file.verifying_sources.extend(module.verifying_sources);
    file.algebraic_type_definitions
        .extend(module.algebraic_type_definitions);
    file.predicate_definitions
        .extend(module.predicate_definitions);
    file.click_function_definitions
        .extend(module.click_function_definitions);
    file.resource_definitions
        .extend(module.resource_definitions);
    file.theorem_definitions.extend(module.theorem_definitions);
    file.contract_definitions
        .extend(module.contract_definitions);
    file.function_blocks.extend(module.function_blocks);
    file.tactic_definitions.extend(module.tactic_definitions);
}

pub(in crate::surface) fn combined_algebraic_type_definitions(
    file: &ClickFile,
) -> Result<Vec<AlgebraicTypeDefinition>, ClickError> {
    let mut definitions = file_library(file)?.file.algebraic_type_definitions.clone();
    definitions.extend(file.algebraic_type_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::surface) fn combined_external_function_blocks(
    file: &ClickFile,
) -> Result<Vec<FunctionBlock>, ClickError> {
    let mut function_blocks = file_library(file)?.file.function_blocks().to_vec();
    function_blocks.extend(file.function_blocks().iter().cloned());
    Ok(function_blocks)
}

/// The parsed standard-library function block whose declaration name is
/// `name`, if the library declares one. A recognized builtin effect is bound
/// to this exact declaration: matching a bare name would let an unrelated
/// user function acquire the effect when it merely shares the spelling.
pub(in crate::surface) fn standard_library_function_block(
    name: &str,
) -> Result<Option<FunctionBlock>, ClickError> {
    Ok(standard_library()?
        .function_blocks()
        .iter()
        .find(|function| function.signature().name() == name)
        .cloned())
}

/// The standard library's expansion. The field schemas and family rules need
/// the library itself, so it applies neither; every verification unit's
/// expansion below applies both.
fn expand_declared_resource_clauses(file: ClickFile) -> Result<ClickFile, ClickError> {
    expand_declared_resource_clauses_with_rules(file, false)
}

/// The expansion every verification unit passes through, single-file or
/// project. It
/// applies the declared field schemas and refuses a count or quantity of a
/// family that is not `authorized`.
pub(in crate::surface) fn expand_declared_resource_clauses_for_project(
    file: ClickFile,
) -> Result<ClickFile, ClickError> {
    expand_declared_resource_clauses_with_rules(file, true)
}

fn expand_declared_resource_clauses_with_rules(
    mut file: ClickFile,
    family_rules: bool,
) -> Result<ClickFile, ClickError> {
    // A failure before the first declaration belongs to none of them.
    crate::surface::clear_ambient_proof_source();
    // The standard library's expansion must not re-enter its OnceLock.
    // Field schemas use the same checked algebraic definitions as lowering.
    if family_rules {
        super::validate_resource_fields(&file)?;
    }
    // A verification unit sees the resources of the library modules it sees,
    // as it sees their predicates and functions; the file's own declarations
    // follow them. The standard library's own expansion has its resources in
    // `file` already.
    let library_resources = if family_rules {
        file_library(&file)?.resource_definitions()
    } else {
        &[]
    };
    let field_environment = if family_rules
        && library_resources
            .iter()
            .chain(file.resource_definitions())
            .any(|definition| !definition.is_fieldless())
    {
        Some(ClickFunctionEnvironment::with_algebraic_types(
            &[],
            &combined_algebraic_type_definitions(&file)?,
        ))
    } else {
        None
    };
    let mut resource_definitions = library_resources
        .iter()
        .chain(file.resource_definitions())
        .map(|definition| {
            Ok((
                definition.name().to_string(),
                DeclaredResourceInfo {
                    fields: std::sync::Arc::new(definition.fields().iter().enumerate()
                        .map(|(index, field)| (field.name().to_string(), (index, field.click_type().clone())))
                        .collect()),
                    field_schema: field_environment.as_ref().map(|environment|
                        crate::surface::lowering::resolve_resource_field_schema(definition, environment)
                    ).transpose()?,
                    has_fields: !definition.is_fieldless(),
                    authorized: definition.is_authorized(),
                    resource_parameter_families: definition.resource_parameters().iter().map(|parameter| {
                        let ResourceClause::Named { resource, .. } = parameter else { unreachable!() };
                        let ResourceClause::Declared { name, .. } = resource.as_ref() else { unreachable!() };
                        name.clone()
                    }).collect(),
                    parameter_types: definition
                        .parameters()
                        .iter()
                        .map(|parameter| {
                            parameter.click_type().interface_type().ok_or_else(|| {
                                ClickError::new(format!(
                                    "resource `{}` parameter `{}` uses an algebraic type; algebraic resource arguments are not supported yet",
                                    definition.name(),
                                    parameter.name()
                                ))
                            })
                        })
                        .collect::<Result<Vec<_>, ClickError>>()?,
                    kind: if definition.composite_body().is_some() {
                        ResourceKind::Composite
                    } else {
                        ResourceKind::Token
                    },
                    child_slots: std::sync::Arc::new(
                        definition
                            .composite_body()
                            .map(CompositeResourceBody::child_slot_resources)
                            .unwrap_or_default(),
                    ),
                    arm_child_slots: std::sync::Arc::new(
                        definition
                            .composite_body()
                            .and_then(CompositeResourceBody::arm_child_slot_resources),
                    ),
                },
            ))
        })
        .collect::<Result<BTreeMap<_, _>, ClickError>>()?;
    resource_definitions
        .entry(ResourceFact::ALLOCATION_RESOURCE_NAME.to_string())
        .or_insert_with(|| DeclaredResourceInfo {
            fields: Default::default(),
            field_schema: None,
            has_fields: false,
            authorized: false,
            resource_parameter_families: Vec::new(),
            parameter_types: vec![InterfaceType::Int32Pointer, InterfaceType::Int32],
            kind: ResourceKind::Token,
            child_slots: Default::default(),
            arm_child_slots: Default::default(),
        });
    resource_definitions.insert(
        "mutex_guard".into(),
        DeclaredResourceInfo {
            fields: Default::default(),
            field_schema: None,
            has_fields: false,
            authorized: false,
            resource_parameter_families: Vec::new(),
            parameter_types: vec![InterfaceType::VoidPointer],
            kind: ResourceKind::Token,
            child_slots: Default::default(),
            arm_child_slots: Default::default(),
        },
    );
    resource_definitions.insert(
        "mutex_live".into(),
        DeclaredResourceInfo {
            fields: Default::default(),
            field_schema: None,
            has_fields: false,
            authorized: false,
            resource_parameter_families: Vec::new(),
            parameter_types: vec![InterfaceType::VoidPointer],
            kind: ResourceKind::Token,
            child_slots: Default::default(),
            arm_child_slots: Default::default(),
        },
    );
    resource_definitions.insert(
        "mutex_use".into(),
        DeclaredResourceInfo {
            fields: Default::default(),
            field_schema: None,
            has_fields: false,
            authorized: false,
            resource_parameter_families: Vec::new(),
            parameter_types: vec![InterfaceType::VoidPointer],
            kind: ResourceKind::Token,
            child_slots: Default::default(),
            arm_child_slots: Default::default(),
        },
    );
    for side in ["publisher", "subscriber"] {
        resource_definitions.insert(
            side.into(),
            DeclaredResourceInfo {
                fields: Default::default(),
                field_schema: None,
                has_fields: false,
                authorized: false,
                resource_parameter_families: Vec::new(),
                parameter_types: vec![InterfaceType::VoidPointer],
                kind: ResourceKind::Token,
                child_slots: Default::default(),
                arm_child_slots: Default::default(),
            },
        );
    }
    resource_definitions.insert(
        "authority".into(),
        DeclaredResourceInfo {
            fields: Default::default(),
            field_schema: None,
            has_fields: false,
            authorized: false,
            resource_parameter_families: Vec::new(),
            parameter_types: Vec::new(),
            kind: ResourceKind::Token,
            child_slots: Default::default(),
            arm_child_slots: Default::default(),
        },
    );
    // The standard library's own expansion reads only its own
    // declarations; it must not re-enter its OnceLock.
    let constructors = if family_rules {
        let library = &file_library(&file)?.file;
        ConstructorTypes::new(
            library
                .algebraic_type_definitions()
                .iter()
                .chain(file.algebraic_type_definitions()),
            library
                .click_function_definitions()
                .iter()
                .chain(file.click_function_definitions()),
            library
                .predicate_definitions()
                .iter()
                .chain(file.predicate_definitions()),
            library
                .theorem_definitions()
                .iter()
                .chain(file.theorem_definitions()),
        )
    } else {
        ConstructorTypes::new(
            file.algebraic_type_definitions(),
            file.click_function_definitions(),
            file.predicate_definitions(),
            file.theorem_definitions(),
        )
    };
    let premise_free_theorems = if family_rules {
        file_library(&file)?.theorem_definitions()
    } else {
        &[]
    }
    .iter()
    .chain(file.theorem_definitions())
    .filter(|theorem| theorem.requires().is_empty())
    .map(|theorem| theorem.name().to_string())
    .collect();
    let resource_definitions = DeclaredResourceScope {
        premise_free_theorems,
        local_hypotheses: Default::default(),
        family_rules,
        definitions: resource_definitions,
        families: Default::default(),
        family_log: Default::default(),
        selected_arms: Default::default(),
        unowned_resource_parameters: Default::default(),
        character_parameters: Default::default(),
        constructors,
    };

    file.resource_definitions = file
        .resource_definitions
        .drain(..)
        .map(|definition| {
            resource_definitions.begin_declaration();
            resource_definitions
                .constructors
                .enter_declaration(declaration_parameter_types(definition.parameters()));
            expand_declared_resource_definition(definition, &resource_definitions)
        })
        .collect::<Result<Vec<_>, _>>()?;

    for predicate in &mut file.predicate_definitions {
        resource_definitions.begin_declaration();
        resource_definitions
            .constructors
            .enter_declaration(declaration_parameter_types(predicate.parameters()));
        predicate.body =
            expand_declared_resource_proposition(predicate.body.clone(), &resource_definitions)?;
    }

    for function in &mut file.click_function_definitions {
        resource_definitions.begin_declaration();
        resource_definitions
            .constructors
            .enter_declaration(declaration_parameter_types(function.parameters()));
        // The return type fixes the constructors in the body's result
        // positions before their arguments are read, so an argument that
        // converts to a field exactly does not fix a narrower type argument.
        if let Some(mut body) = function.body.clone() {
            resource_definitions
                .constructors
                .push_expected(&mut body, &function.return_type);
            let mut body = expand_declared_resource_expression(body, &resource_definitions)?;
            resource_definitions
                .constructors
                .push_expected(&mut body, &function.return_type);
            function.body = Some(body);
        }
        function.decreases = function
            .decreases
            .take()
            .map(|expression| {
                expand_declared_resource_expression(expression, &resource_definitions)
            })
            .transpose()?;
    }

    for contract in &mut file.contract_definitions {
        resource_definitions.begin_declaration();
        if let Some(parameters) = &mut contract.proof_parameters {
            for parameter in parameters {
                *parameter =
                    expand_declared_resource_clause(parameter.clone(), &resource_definitions)?;
            }
        }
        expand_declared_resources_in_function_block(
            &mut contract.function_block,
            &resource_definitions,
        )?;
    }

    for function in &mut file.function_blocks {
        resource_definitions.begin_declaration();
        expand_declared_resources_in_function_block(function, &resource_definitions)?;
    }
    for tactic in &mut file.tactic_definitions {
        resource_definitions.begin_declaration();
        expand_declared_resources_in_function_block(
            tactic.function_block_mut(),
            &resource_definitions,
        )?;
    }

    for theorem in &mut file.theorem_definitions {
        resource_definitions.begin_declaration();
        resource_definitions
            .constructors
            .enter_declaration(declaration_parameter_types(theorem.parameters()));
        crate::surface::enter_ambient_declaration(theorem.name());
        theorem.requires = theorem
            .requires
            .drain(..)
            .map(|requirement| {
                expand_declared_resource_requirement(requirement, &resource_definitions)
            })
            .collect::<Result<Vec<_>, _>>()?;
        theorem.ensures = theorem
            .ensures
            .drain(..)
            .map(|clause| expand_declared_resource_ensure_clause(clause, &resource_definitions))
            .collect::<Result<Vec<_>, _>>()?;
    }

    crate::surface::clear_ambient_proof_source();
    Ok(file)
}

/// The declared parameters of a declaration, by name and type, for
/// constructor type inference.
fn declaration_parameter_types(
    parameters: &[FunctionParameter],
) -> impl Iterator<Item = (String, ClickType)> + '_ {
    parameters.iter().map(|parameter| {
        (
            parameter.name().to_string(),
            parameter.click_type_with_object_class(),
        )
    })
}

fn expand_declared_resources_in_function_block(
    function: &mut FunctionBlock,
    resource_definitions: &DeclaredResourceScope,
) -> Result<(), ClickError> {
    resource_definitions.constructors.enter_declaration(
        declaration_parameter_types(function.signature().parameters()).chain(
            (function.signature().return_type() != InterfaceType::Void).then(|| {
                (
                    "result".to_string(),
                    ClickType::Program(function.signature().return_type()),
                )
            }),
        ),
    );
    crate::surface::enter_ambient_declaration(function.signature().name());
    *resource_definitions.character_parameters.borrow_mut() = function
        .signature()
        .parameters()
        .iter()
        .filter(|parameter| {
            crate::surface::lowering::needs_character_byte_view(
                parameter.interface_type(),
                crate::kernel::ProgramType::UInt8Pointer,
            )
        })
        .map(|parameter| parameter.name().to_string())
        .collect();
    let declared_binders = function
        .requires
        .iter()
        .filter_map(|requirement| match requirement {
            Requirement::Resource(ResourceClause::Named { binding, .. }) => {
                Some(binding.name.clone())
            }
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    function.decreases = function
        .decreases
        .take()
        .map(|decreases| match decreases {
            FunctionDecrease::Unresolved(expression) => {
                classify_function_decrease(expression, &declared_binders, resource_definitions)
            }
            FunctionDecrease::Numeric(expression) => Ok(FunctionDecrease::Numeric(
                expand_declared_resource_expression(expression, resource_definitions)?,
            )),
            // Every component of a tuple is numeric: a structural measure
            // is one resource, never a component of a tuple.
            FunctionDecrease::Lexicographic(components) => Ok(FunctionDecrease::Lexicographic(
                components
                    .into_iter()
                    .map(|component| {
                        expand_declared_resource_expression(component, resource_definitions)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            )),
            FunctionDecrease::Resource(resource) => Ok(FunctionDecrease::Resource(
                expand_declared_resource_clause(resource, resource_definitions)?,
            )),
            FunctionDecrease::Binder(name) => Ok(FunctionDecrease::Binder(name)),
        })
        .transpose()?;
    function.requires = function
        .requires
        .drain(..)
        .map(|requirement| expand_declared_resource_requirement(requirement, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.ensures = function
        .ensures
        .drain(..)
        .map(|clause| expand_declared_resource_ensure_clause(clause, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.constructs = function
        .constructs
        .drain(..)
        .map(|resource| expand_declared_resource_clause(resource, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    function.grouped_proof = function
        .grouped_proof
        .take()
        .map(|proof| {
            expand_declared_resource_proof(
                std::sync::Arc::unwrap_or_clone(proof),
                resource_definitions,
            )
            .map(std::sync::Arc::new)
        })
        .transpose()?;
    Ok(())
}

fn expand_declared_resource_definition(
    mut definition: ResourceDefinition,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ResourceDefinition, ClickError> {
    crate::surface::enter_ambient_declaration(definition.name());
    if !definition.resource_parameters.is_empty() && definition.fields().is_empty() {
        return Err(ClickError::new(
            "resource parameters currently require a resource with fields",
        ));
    }
    definition.resource_parameters = definition
        .resource_parameters
        .into_iter()
        .map(|parameter| expand_declared_resource_clause(parameter, resource_definitions))
        .collect::<Result<_, _>>()?;
    if let Some(composite_body) = definition.composite_body {
        if !definition.resource_parameters.is_empty() && composite_body.matched.is_some() {
            return Err(ClickError::new(
                "resource parameters in matched resource bodies are not supported yet",
            ));
        }
        let owned = composite_body
            .contains
            .iter()
            .filter_map(|clause| match clause {
                ResourceClause::Named { binding, .. } => Some(binding.identity),
                _ => None,
            })
            .collect::<BTreeSet<_>>();
        let unavailable = definition
            .resource_parameters
            .iter()
            .filter_map(|parameter| {
                let ResourceClause::Named { binding, .. } = parameter else {
                    unreachable!()
                };
                (!owned.contains(&binding.identity))
                    .then(|| (binding.identity, SurfaceBinder::from(binding.name.clone())))
            })
            .collect();
        let previous = resource_definitions
            .unowned_resource_parameters
            .replace(unavailable);
        definition.composite_body = Some(expand_declared_composite_resource_body(
            composite_body,
            resource_definitions,
        )?);
        resource_definitions
            .unowned_resource_parameters
            .replace(previous);
    }
    Ok(definition)
}

fn expand_declared_composite_resource_body(
    composite_body: CompositeResourceBody,
    resource_definitions: &DeclaredResourceScope,
) -> Result<CompositeResourceBody, ClickError> {
    Ok(CompositeResourceBody {
        children: composite_body.children,
        fields: composite_body.fields,
        matched: composite_body
            .matched
            .map(|matched| {
                Ok(ResourceMatchBody {
                    field: matched.field,
                    arms: matched
                        .arms
                        .into_iter()
                        .map(|arm| {
                            Ok(ResourceMatchArm {
                                type_name: arm.type_name,
                                variant: arm.variant,
                                bindings: arm.bindings,
                                body: expand_declared_composite_resource_body(
                                    arm.body,
                                    resource_definitions,
                                )?,
                            })
                        })
                        .collect::<Result<Vec<_>, ClickError>>()?,
                })
            })
            .transpose()?,
        witnesses: composite_body.witnesses.clone(),
        condition: composite_body
            .condition
            .map(|condition| expand_declared_resource_proposition(condition, resource_definitions))
            .transpose()?,
        contains: composite_body
            .contains
            .into_iter()
            .map(|resource| expand_declared_resource_clause(resource, resource_definitions))
            .collect::<Result<Vec<_>, _>>()?,
        facts: composite_body
            .facts
            .into_iter()
            .map(|fact| expand_declared_resource_proposition(fact, resource_definitions))
            .collect::<Result<Vec<_>, _>>()?,
    })
}

fn expand_declared_resource_requirement(
    requirement: Requirement,
    resource_definitions: &DeclaredResourceScope,
) -> Result<Requirement, ClickError> {
    match requirement {
        Requirement::Proposition(ClickProposition::PredicateCall { name, arguments })
            if resource_definitions.contains_key(&name) =>
        {
            declared_resource_info(&name, arguments.len(), resource_definitions)?;
            Err(ClickError::new(format!(
                "`requires` accepts pure propositions only; use `owns {name}(...)`, `views {name}(...)`, or `consumes {name}(...)`"
            )))
        }
        Requirement::Resource(resource) => Ok(Requirement::Resource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        Requirement::Proposition(proposition) => Ok(Requirement::Proposition(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        )),
        _ => Ok(requirement),
    }
}

fn expand_declared_resource_ensure_clause(
    mut clause: EnsureClause,
    resource_definitions: &DeclaredResourceScope,
) -> Result<EnsureClause, ClickError> {
    clause.ensure = match clause.ensure {
        Ensure::Proposition(ClickProposition::PredicateCall { name, arguments })
            if resource_definitions.contains_key(&name) =>
        {
            declared_resource_info(&name, arguments.len(), resource_definitions)?;
            return Err(ClickError::new(format!(
                "`ensures` accepts pure propositions only; use `owns {name}(...)` or `produces {name}(...)`"
            )));
        }
        Ensure::Proposition(proposition) => Ensure::Proposition(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        ),
        Ensure::Resource(resource) => Ensure::Resource(expand_declared_resource_clause(
            resource,
            resource_definitions,
        )?),
    };
    let goal = match &clause.ensure {
        Ensure::Proposition(proposition) => Some(proposition.clone()),
        _ => None,
    };
    clause.proof =
        expand_declared_resource_proof_of(clause.proof, goal.as_ref(), resource_definitions)?;
    Ok(clause)
}

fn expand_declared_resource_structural_clause(
    mut clause: StructuralClause,
    resource_definitions: &DeclaredResourceScope,
) -> Result<StructuralClause, ClickError> {
    clause.items = std::mem::take(&mut clause.items)
        .into_iter()
        .map(|item| expand_declared_resource_structural_item(item, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    clause.resources = std::mem::take(&mut clause.resources)
        .into_iter()
        .map(|resource| expand_declared_resource_clause(resource, resource_definitions))
        .collect::<Result<Vec<_>, _>>()?;
    clause.initialize_proof = clause
        .initialize_proof
        .take()
        .map(|proof| expand_declared_resource_proof(proof, resource_definitions))
        .transpose()?;
    clause.preserve_proof = clause
        .preserve_proof
        .take()
        .map(|proof| expand_declared_resource_proof(proof, resource_definitions))
        .transpose()?;
    // A `decreases` component is an ordinary contract expression now that the
    // slot takes pure expressions, so a resource field it reads needs the same
    // declared-resource expansion an invariant's does. Without it the field's
    // declared type never reaches the component and lowering refuses a
    // perfectly ordinary `decreases c.rank`.
    clause.decreases = clause
        .decreases
        .take()
        .map(|measure| {
            Ok::<_, ClickError>(TerminationMeasure::new(
                measure
                    .components()
                    .iter()
                    .cloned()
                    .map(|component| {
                        expand_declared_resource_expression(component, resource_definitions)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            ))
        })
        .transpose()?;
    Ok(clause)
}

fn expand_declared_resource_structural_item(
    mut item: StructuralItem,
    resource_definitions: &DeclaredResourceScope,
) -> Result<StructuralItem, ClickError> {
    item.claim = expand_declared_resource_proposition(item.claim, resource_definitions)?;
    Ok(item)
}

fn expand_declared_resource_proof(
    proof: SourceProof,
    resource_definitions: &DeclaredResourceScope,
) -> Result<SourceProof, ClickError> {
    expand_declared_resource_proof_of(proof, None, resource_definitions)
}

/// Expands a proof of `goal`. A name the script binds, an `intro()`
/// variable or an `obtain` witness, has its type for constructor inference
/// in the tactics after it, as a match arm's binder has in its arm.
fn expand_declared_resource_proof_of(
    proof: SourceProof,
    goal: Option<&ClickProposition>,
    resource_definitions: &DeclaredResourceScope,
) -> Result<SourceProof, ClickError> {
    let SourceProof::Script(tactics) = proof else {
        return Ok(proof);
    };
    let constructors = &resource_definitions.constructors;
    let mut goal = goal.cloned();
    let mut bound = Vec::new();
    let mut expanded = Vec::with_capacity(tactics.len());
    let mut result = Ok(());
    let outer_hypotheses = resource_definitions.local_hypotheses.borrow().clone();
    for tactic in tactics {
        if let ProofTactic::LetSatisfy(obtain) = &tactic {
            for (name, click_type) in &obtain.bindings {
                bound.push(constructors.bind(name, Some(click_type.clone())));
            }
        }
        let introduced = match &tactic {
            ProofTactic::Intro => Some(None),
            ProofTactic::IntroAs(name) => Some(Some(SurfaceBinder::from(name))),
            ProofTactic::IntroBinder(name) => Some(Some(name.clone())),
            _ => None,
        };
        match expand_declared_resource_tactic(tactic, resource_definitions) {
            Ok(tactic) => expanded.push(tactic),
            Err(error) => {
                result = Err(error);
                break;
            }
        }
        if let Some(rename) = introduced {
            goal = match goal.take() {
                Some(ClickProposition::ForAll {
                    click_type,
                    name,
                    written_name,
                    body,
                }) => {
                    let _ = written_name;
                    let name = rename.unwrap_or(name);
                    bound.push(constructors.bind(&name, Some(click_type)));
                    Some(*body)
                }
                Some(ClickProposition::Implies(_, consequent)) => Some(*consequent),
                _ => None,
            };
        }
    }
    if let Some(first) = bound.first() {
        constructors.restore(*first);
    }
    *resource_definitions.local_hypotheses.borrow_mut() = outer_hypotheses;
    result.map(|()| SourceProof::Script(expanded))
}

/// Expands declared resources in the assertions of a join's `ensuring`
/// block.
fn expand_declared_join_interface(
    ensuring: Option<Vec<ProofAssertion>>,
    resource_definitions: &DeclaredResourceScope,
) -> Result<Option<Vec<ProofAssertion>>, ClickError> {
    ensuring
        .map(|assertions| {
            assertions
                .into_iter()
                .map(|assertion| match assertion {
                    ProofAssertion::Fact(fact) => Ok(ProofAssertion::Fact(
                        expand_declared_resource_proposition(fact, resource_definitions)?,
                    )),
                    ProofAssertion::Resource(resource) => Ok(ProofAssertion::Resource(
                        expand_declared_resource_clause(resource, resource_definitions)?,
                    )),
                })
                .collect::<Result<Vec<_>, ClickError>>()
        })
        .transpose()
}

// Keep the recursive tactic dispatcher small. Each helper owns only one
// family of large syntax temporaries, so nested proof scripts do not retain
// every tactic variant's frame at once.
#[inline(never)]
fn expand_declared_resource_tactic(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    match tactic {
        tactic @ ProofTactic::Induct { .. } => {
            let ProofTactic::Induct { hypothesis, .. } = &tactic else {
                unreachable!()
            };
            let inner = resource_definitions
                .local_hypotheses
                .borrow()
                .with_inserted(hypothesis.clone(), ());
            *resource_definitions.local_hypotheses.borrow_mut() = inner;
            Ok(tactic)
        }
        tactic @ (ProofTactic::ApplyTheorem(_)
        | ProofTactic::Witness(_)
        | ProofTactic::ApplyInduction { .. }
        | ProofTactic::ApplyInductionUsing { .. }
        | ProofTactic::ApplyTheoremUsing { .. }
        | ProofTactic::UnfoldFunction(_)
        | ProofTactic::Instantiate { .. }) => {
            expand_declared_resource_tactic_with_expressions(tactic, resource_definitions)
        }
        tactic @ (ProofTactic::ArithmeticUsing(_)
        | ProofTactic::Contradiction(_)
        | ProofTactic::ApplyFact(_)
        | ProofTactic::ApplyFactUsing { .. }
        | ProofTactic::Preserve(_)
        | ProofTactic::Rewrite(_)
        | ProofTactic::Transport { .. }
        | ProofTactic::TransportUsing { .. }
        | ProofTactic::SolveUsing(_)
        | ProofTactic::NormalizeUsing(_)) => {
            expand_declared_resource_tactic_with_propositions(tactic, resource_definitions)
        }
        tactic @ (ProofTactic::UnfoldResource(_)
        | ProofTactic::UnfoldWitnesses { .. }
        | ProofTactic::ObserveResource(_)
        | ProofTactic::ObserveSavedMemory { .. }
        | ProofTactic::FoldResource(_)
        | ProofTactic::ConstructResource(_)
        | ProofTactic::Iterated(_)) => {
            expand_declared_resource_tactic_with_resources(tactic, resource_definitions)
        }
        tactic @ (ProofTactic::Have(_)
        | ProofTactic::Open(_)
        | ProofTactic::If(_)
        | ProofTactic::Match(_)
        | ProofTactic::Cases(_)
        | ProofTactic::Branch(_)
        | ProofTactic::Loop(_)) => {
            expand_declared_resource_tactic_with_nested_proofs(tactic, resource_definitions)
        }
        tactic @ (ProofTactic::Both(_) | ProofTactic::CloseInvariantsBy(_)) => {
            expand_declared_resource_tactic_with_plain_scripts(tactic, resource_definitions)
        }
        ProofTactic::StepProved { step, proof } => {
            let step = Box::new(expand_declared_resource_tactic(
                *step,
                resource_definitions,
            )?);
            let proof = match proof {
                StepProof::By(body) => StepProof::By(
                    body.into_iter()
                        .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                        .collect::<Result<_, _>>()?,
                ),
                StepProof::Requires(entries) => StepProof::Requires(
                    entries
                        .into_iter()
                        .map(|entry| {
                            let ProofTactic::Have(have) = expand_declared_resource_tactic(
                                ProofTactic::Have(entry.have),
                                resource_definitions,
                            )?
                            else {
                                unreachable!("a `have` expands to a `have`")
                            };
                            Ok(StepRequirement {
                                label: entry.label,
                                have,
                            })
                        })
                        .collect::<Result<_, ClickError>>()?,
                ),
            };
            Ok(ProofTactic::StepProved { step, proof })
        }
        ProofTactic::StepCall(transport) => {
            record_produced_instances(&transport, resource_definitions);
            Ok(ProofTactic::StepCall(transport.try_map_type_arguments(
                |resource| expand_declared_resource_clause(resource, resource_definitions),
            )?))
        }
        ProofTactic::UserTactic(application) => {
            record_produced_instances(&application, resource_definitions);
            Ok(ProofTactic::UserTactic(application))
        }

        tactic => Ok(tactic),
    }
}

/// A tactic whose children are ordinary scripts and nothing else.
///
/// `both` nests as deeply as a written conjunction does, so it gets its own
/// helper rather than sharing the nested-proof dispatcher's frame, which holds
/// one large syntax temporary per tactic family. `close_invariants() by { .. }`
/// joins it because generated closers are exactly such a conjunction, and a
/// resource field named inside one needs the same expansion every other script
/// gets.
#[inline(never)]
fn expand_declared_resource_tactic_with_plain_scripts(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    enum Frame {
        Visit(ProofTactic),
        Script(Vec<ProofTactic>),
        RestoreHypotheses(PersistentBinderMap<()>),
        Both { left: usize, right: usize },
        Close { count: usize },
    }
    let mut pending = vec![Frame::Visit(tactic)];
    let mut expanded = Vec::new();
    while let Some(frame) = pending.pop() {
        match frame {
            Frame::Script(tactics) => {
                pending.push(Frame::RestoreHypotheses(
                    resource_definitions.local_hypotheses.borrow().clone(),
                ));
                pending.extend(tactics.into_iter().rev().map(Frame::Visit));
            }
            Frame::RestoreHypotheses(outer) => {
                *resource_definitions.local_hypotheses.borrow_mut() = outer;
            }
            Frame::Visit(ProofTactic::Both(both)) => {
                pending.push(Frame::Both {
                    left: both.left_tactics.len(),
                    right: both.right_tactics.len(),
                });
                pending.push(Frame::Script(both.right_tactics));
                pending.push(Frame::Script(both.left_tactics));
            }
            Frame::Visit(ProofTactic::CloseInvariantsBy(tactics)) => {
                pending.push(Frame::Close {
                    count: tactics.len(),
                });
                pending.push(Frame::Script(tactics));
            }
            Frame::Visit(tactic) => expanded.push(expand_declared_resource_tactic(
                tactic,
                resource_definitions,
            )?),
            Frame::Both { left, right } => {
                let right_tactics = expanded.split_off(expanded.len() - right);
                let left_tactics = expanded.split_off(expanded.len() - left);
                expanded.push(ProofTactic::Both(ProofBoth {
                    left_tactics,
                    right_tactics,
                }));
            }
            Frame::Close { count } => {
                let tactics = expanded.split_off(expanded.len() - count);
                expanded.push(ProofTactic::CloseInvariantsBy(tactics));
            }
        }
    }
    Ok(expanded.pop().expect("a plain script expansion has a root"))
}

/// A value argument introduces no argument-definedness search. Computed
/// arguments still use the smart application even when the theorem itself
/// declares no requirements (for example `to_integer(x + 1)`).
fn theorem_argument_is_value(argument: &ContractExpression) -> bool {
    match argument {
        ContractExpression::IntegerLiteral(_)
        | ContractExpression::Binding(_)
        | ContractExpression::ProgramBinding(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::ProgramExpression(
            ProgramExpression::Value(_) | ProgramExpression::Variable(_),
        ) => true,
        ContractExpression::AlgebraicConstructor { arguments, .. }
        | ContractExpression::SequenceLiteral(arguments) => {
            arguments.iter().all(theorem_argument_is_value)
        }
        _ => false,
    }
}

#[inline(never)]
fn expand_declared_resource_tactic_with_expressions(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    match tactic {
        ProofTactic::ApplyTheorem(mut application) => {
            application.arguments = application
                .arguments
                .into_iter()
                .map(|argument| expand_declared_resource_expression(argument, resource_definitions))
                .collect::<Result<_, _>>()?;
            let local_hypothesis = resource_definitions
                .local_hypotheses
                .borrow()
                .contains_key(&application.name);
            if !local_hypothesis {
                resource_definitions.constructors.resolve_call(
                    CallKind::Theorem,
                    &application.name,
                    &mut application.arguments,
                );
            }
            if !local_hypothesis
                && resource_definitions
                    .premise_free_theorems
                    .contains(&application.name)
                && application.arguments.iter().all(theorem_argument_is_value)
            {
                Ok(ProofTactic::ApplyTheoremUsing {
                    application,
                    premises: Vec::new(),
                })
            } else {
                Ok(ProofTactic::ApplyTheorem(application))
            }
        }
        ProofTactic::Witness(witness) => {
            Ok(ProofTactic::Witness(witness.try_map_values(|value| {
                expand_declared_resource_expression(value.clone(), resource_definitions)
            })?))
        }
        ProofTactic::ApplyInduction {
            hypothesis,
            arguments,
        } => Ok(ProofTactic::ApplyInduction {
            hypothesis,
            arguments: arguments
                .into_iter()
                .map(|argument| expand_declared_resource_expression(argument, resource_definitions))
                .collect::<Result<_, _>>()?,
        }),
        ProofTactic::ApplyInductionUsing {
            hypothesis,
            arguments,
            premises,
        } => Ok(ProofTactic::ApplyInductionUsing {
            hypothesis,
            arguments: arguments
                .into_iter()
                .map(|argument| expand_declared_resource_expression(argument, resource_definitions))
                .collect::<Result<_, _>>()?,
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<_, _>>()?,
        }),
        ProofTactic::ApplyTheoremUsing {
            application,
            premises,
        } => Ok(ProofTactic::ApplyTheoremUsing {
            application: {
                let mut arguments = application
                    .arguments
                    .into_iter()
                    .map(|argument| {
                        expand_declared_resource_expression(argument, resource_definitions)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if !resource_definitions
                    .local_hypotheses
                    .borrow()
                    .contains_key(&application.name)
                {
                    resource_definitions.constructors.resolve_call(
                        CallKind::Theorem,
                        &application.name,
                        &mut arguments,
                    );
                }
                TheoremApplication {
                    name: application.name,
                    arguments,
                }
            },
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ProofTactic::UnfoldFunction(application)
            if resource_definitions.contains_key(&application.name) =>
        {
            Ok(ProofTactic::UnfoldResource(
                expand_declared_resource_clause(
                    ResourceClause::Declared {
                        type_schema: None,
                        resource_type_arguments: Vec::new(),
                        resource_arguments: Vec::new(),
                        access: ResourceAccessMode::Own,
                        kind: ResourceKind::Token,
                        name: application.name,
                        arguments: application.arguments,
                        parameter_types: Vec::new(),
                    },
                    resource_definitions,
                )?,
            ))
        }
        ProofTactic::UnfoldFunction(mut application) => {
            application.arguments = application
                .arguments
                .into_iter()
                .map(|argument| expand_declared_resource_expression(argument, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?;
            resource_definitions.constructors.resolve_call(
                CallKind::Function,
                &application.name,
                &mut application.arguments,
            );
            Ok(ProofTactic::UnfoldFunction(application))
        }
        ProofTactic::Instantiate {
            quantified,
            argument,
        } => Ok(ProofTactic::Instantiate {
            quantified: expand_declared_resource_proposition(quantified, resource_definitions)?,
            argument: expand_declared_resource_expression(argument, resource_definitions)?,
        }),
        _ => unreachable!("tactic dispatched to the wrong declaration-expansion helper"),
    }
}

#[inline(never)]
fn expand_declared_resource_tactic_with_propositions(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    match tactic {
        ProofTactic::ArithmeticUsing(premises) => Ok(ProofTactic::ArithmeticUsing(
            premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<_, _>>()?,
        )),
        ProofTactic::Contradiction(proposition) => Ok(ProofTactic::Contradiction(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        )),
        ProofTactic::ApplyFact(fact) => Ok(ProofTactic::ApplyFact(
            expand_declared_resource_proposition(fact, resource_definitions)?,
        )),
        ProofTactic::ApplyFactUsing { fact, premises } => Ok(ProofTactic::ApplyFactUsing {
            fact: expand_declared_resource_proposition(fact, resource_definitions)?,
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<_, _>>()?,
        }),
        ProofTactic::Preserve(proposition) => Ok(ProofTactic::Preserve(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        )),
        ProofTactic::Rewrite(proposition) => Ok(ProofTactic::Rewrite(
            expand_declared_resource_proposition(proposition, resource_definitions)?,
        )),
        ProofTactic::Transport { source, target } => Ok(ProofTactic::Transport {
            source: expand_declared_resource_proposition(source, resource_definitions)?,
            target: expand_declared_resource_proposition(target, resource_definitions)?,
        }),
        ProofTactic::TransportUsing {
            source,
            target,
            premises,
        } => Ok(ProofTactic::TransportUsing {
            source: expand_declared_resource_proposition(source, resource_definitions)?,
            target: expand_declared_resource_proposition(target, resource_definitions)?,
            premises: premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        }),
        ProofTactic::SolveUsing(solve) => Ok(ProofTactic::SolveUsing(ProofSolveUsing {
            premises: solve
                .premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
        })),
        ProofTactic::NormalizeUsing(premises) => Ok(ProofTactic::NormalizeUsing(
            premises
                .into_iter()
                .map(|premise| expand_declared_resource_proposition(premise, resource_definitions))
                .collect::<Result<_, _>>()?,
        )),
        _ => unreachable!("tactic dispatched to the wrong declaration-expansion helper"),
    }
}

#[inline(never)]
fn expand_declared_resource_tactic_with_resources(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    let expand_slot = |mut slot: Box<IteratedSlot>| -> Result<Box<IteratedSlot>, ClickError> {
        slot.resource = expand_resource_application(slot.resource, resource_definitions, true)?;
        Ok(slot)
    };
    match tactic {
        ProofTactic::UnfoldResource(resource) => Ok(ProofTactic::UnfoldResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::UnfoldWitnesses { resource, names } => Ok(ProofTactic::UnfoldWitnesses {
            resource: expand_declared_resource_clause(resource, resource_definitions)?,
            names,
        }),
        ProofTactic::ObserveResource(resource) => Ok(ProofTactic::ObserveResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::FoldResource(resource) => Ok(ProofTactic::FoldResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::ConstructResource(resource) => Ok(ProofTactic::ConstructResource(
            expand_declared_resource_clause(resource, resource_definitions)?,
        )),
        ProofTactic::Iterated(IteratedTactic::Gather(resource)) => {
            Ok(ProofTactic::Iterated(IteratedTactic::Gather(
                expand_declared_resource_clause(resource, resource_definitions)?,
            )))
        }
        ProofTactic::Iterated(IteratedTactic::Scatter(resource)) => {
            Ok(ProofTactic::Iterated(IteratedTactic::Scatter(
                expand_declared_resource_clause(resource, resource_definitions)?,
            )))
        }
        ProofTactic::Iterated(IteratedTactic::UnfoldSlot(slot)) => Ok(ProofTactic::Iterated(
            IteratedTactic::UnfoldSlot(expand_slot(slot)?),
        )),
        ProofTactic::Iterated(IteratedTactic::FoldSlot(slot)) => Ok(ProofTactic::Iterated(
            IteratedTactic::FoldSlot(expand_slot(slot)?),
        )),
        tactic @ ProofTactic::ObserveSavedMemory { .. } => Ok(tactic),
        _ => unreachable!("tactic dispatched to the wrong declaration-expansion helper"),
    }
}

#[inline(never)]
fn expand_declared_resource_script(
    tactics: Vec<ProofTactic>,
    resource_definitions: &DeclaredResourceScope,
) -> Result<Vec<ProofTactic>, ClickError> {
    let SourceProof::Script(expanded) = expand_declared_resource_proof_of(
        SourceProof::Script(tactics),
        None,
        resource_definitions,
    )?
    else {
        unreachable!()
    };
    Ok(expanded)
}

fn expand_declared_resource_tactic_with_nested_proofs(
    tactic: ProofTactic,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ProofTactic, ClickError> {
    match tactic {
        ProofTactic::Have(have) => {
            let proposition =
                expand_declared_resource_proposition(have.proposition, resource_definitions)?;
            let proof = expand_declared_resource_proof_of(
                have.proof,
                Some(&proposition),
                resource_definitions,
            )?;
            Ok(ProofTactic::Have(ProofHave { proposition, proof }))
        }
        ProofTactic::Open(open) => Ok(ProofTactic::Open(ProofOpen {
            resource: expand_declared_resource_clause(open.resource, resource_definitions)?,
            tactics: open
                .tactics
                .into_iter()
                .map(|tactic| expand_declared_resource_tactic(tactic, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?,
            deferred_tail: open.deferred_tail,
        })),
        ProofTactic::If(proof_if) => {
            let condition =
                expand_declared_resource_proposition(proof_if.condition, resource_definitions)?;
            let ensuring = expand_declared_join_interface(proof_if.ensuring, resource_definitions)?;
            let alternatives = resource_definitions.begin_alternatives();
            let then_tactics = resource_definitions.arm(&alternatives, || {
                expand_declared_resource_script(proof_if.then_tactics, resource_definitions)
            })?;
            let else_tactics = resource_definitions.arm(&alternatives, || {
                expand_declared_resource_script(proof_if.else_tactics, resource_definitions)
            })?;
            resource_definitions.finish_alternatives(alternatives);
            Ok(ProofTactic::If(ProofIf {
                condition,
                ensuring,
                then_tactics,
                else_tactics,
            }))
        }
        ProofTactic::Cases(proof_cases) => {
            let alternatives = resource_definitions.begin_alternatives();
            let proof_cases = proof_cases.try_map(
                |assumption| {
                    expand_declared_resource_proposition(assumption.clone(), resource_definitions)
                },
                |tactics| {
                    resource_definitions.arm(&alternatives, || {
                        expand_declared_resource_script(tactics.to_vec(), resource_definitions)
                    })
                },
            )?;
            resource_definitions.finish_alternatives(alternatives);
            Ok(ProofTactic::Cases(proof_cases))
        }
        ProofTactic::Match(proof_match) => {
            let proof_match = std::sync::Arc::unwrap_or_clone(proof_match);
            let constructors = &resource_definitions.constructors;
            let scrutinee =
                expand_declared_resource_expression(proof_match.scrutinee, resource_definitions)?;
            let scrutinee_type = constructors.scrutinee_type(&scrutinee);
            // A match on an instance's own field selects one arm of its
            // resource's matched body in each proof arm.
            let selected_field = match &scrutinee {
                ContractExpression::ResourceField(access) if access.children.is_empty() => {
                    Some((access.identity, access.field.clone()))
                }
                _ => None,
            };
            let ensuring =
                expand_declared_join_interface(proof_match.ensuring, resource_definitions)?;
            let alternatives = resource_definitions.begin_alternatives();
            let arms = proof_match
                .arms
                .into_iter()
                .map(|arm| {
                    let types = constructors.proof_arm_binding_types(scrutinee_type.as_ref(), &arm);
                    if let Some((identity, field)) = &selected_field {
                        resource_definitions.selected_arms.borrow_mut().push((
                            *identity,
                            field.clone(),
                            arm.variant.clone(),
                        ));
                    }
                    let tactics = constructors.with_bindings(&arm.bindings, types, || {
                        resource_definitions.arm(&alternatives, || {
                            expand_declared_resource_script(arm.tactics, resource_definitions)
                        })
                    });
                    if selected_field.is_some() {
                        resource_definitions.selected_arms.borrow_mut().pop();
                    }
                    let tactics = tactics?;
                    Ok(ProofInductionArm {
                        type_name: arm.type_name,
                        variant: arm.variant,
                        bindings: arm.bindings,
                        tactics,
                    })
                })
                .collect::<Result<_, ClickError>>()?;
            resource_definitions.finish_alternatives(alternatives);
            Ok(ProofTactic::Match(std::sync::Arc::new(ProofMatch {
                scrutinee,
                ensuring,
                arms,
            })))
        }
        ProofTactic::Branch(proof_branch) => {
            let ensuring =
                expand_declared_join_interface(proof_branch.ensuring, resource_definitions)?;
            let alternatives = resource_definitions.begin_alternatives();
            let then_tactics = resource_definitions.arm(&alternatives, || {
                expand_declared_resource_script(proof_branch.then_tactics, resource_definitions)
            })?;
            let else_tactics = resource_definitions.arm(&alternatives, || {
                expand_declared_resource_script(proof_branch.else_tactics, resource_definitions)
            })?;
            resource_definitions.finish_alternatives(alternatives);
            Ok(ProofTactic::Branch(ProofBranch {
                ensuring,
                then_tactics,
                else_tactics,
            }))
        }
        ProofTactic::Loop(clause) => Ok(ProofTactic::Loop(
            expand_declared_resource_structural_clause(clause, resource_definitions)?,
        )),
        _ => unreachable!("tactic dispatched to the wrong declaration-expansion helper"),
    }
}

/// Decides what a C function's parsed `decreases` expression names (D6).
///
/// Functions and resources share one namespace and declaration order creates
/// no scope, so the parser cannot make this decision; this pass can, because
/// it holds every declared resource and the function's own contract binders.
/// An application of a declared resource is a structural measure over that
/// entry resource, a bare contract resource binder is a structural measure
/// over the instance that binder names, and everything else stays the
/// existing numeric measure over an int32 parameter.
///
/// Cost is the one expression's head, not a search.
fn classify_function_decrease(
    expression: ContractExpression,
    declared_binders: &BTreeSet<String>,
    resource_definitions: &DeclaredResourceScope,
) -> Result<FunctionDecrease, ClickError> {
    match &expression {
        ContractExpression::Call { name, arguments } if resource_definitions.contains_key(name) => {
            Ok(FunctionDecrease::Resource(expand_declared_resource_clause(
                ResourceClause::Declared {
                    type_schema: None,
                    resource_type_arguments: Vec::new(),
                    resource_arguments: Vec::new(),
                    access: ResourceAccessMode::View,
                    kind: ResourceKind::Token,
                    name: name.clone(),
                    arguments: arguments.clone(),
                    parameter_types: Vec::new(),
                },
                resource_definitions,
            )?))
        }
        ContractExpression::Binding(name)
        | ContractExpression::ProgramBinding(name)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        )) if declared_binders.contains(name) => Ok(FunctionDecrease::Binder(name.clone())),
        _ => Ok(FunctionDecrease::Numeric(
            expand_declared_resource_expression(expression, resource_definitions)?,
        )),
    }
}

fn expand_declared_resource_clause(
    resource: ResourceClause,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ResourceClause, ClickError> {
    match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => Ok(ResourceClause::Conditional {
            condition: expand_declared_resource_proposition(condition, resource_definitions)?,
            resource: Box::new(expand_declared_resource_clause(
                *resource,
                resource_definitions,
            )?),
        }),
        ResourceClause::Named {
            mut binding,
            resource,
        } => {
            let ResourceClause::Declared {
                access: ResourceAccessMode::Own,
                name,
                arguments,
                type_schema,
                resource_type_arguments,
                resource_arguments,
                ..
            } = *resource
            else {
                return Err(ClickError::new(
                    "named ownership requires a declared resource",
                ));
            };
            if name == "authority" {
                return Err(ClickError::new(
                    "named authority binders are unsupported; use an ordinary unnamed authority clause",
                ));
            }
            if matches!(
                name.as_str(),
                "mutex_live"
                    | "mutex_guard"
                    | "mutex_use"
                    | "authority"
                    | "publisher"
                    | "subscriber"
            ) {
                if binding.fold_fields.is_some() || binding.child_bindings.is_some() {
                    return Err(ClickError::new(
                        "mutex authority has no fields or resource body to fold or unfold",
                    ));
                }
                let resource_type_arguments = expand_resource_type_arguments(
                    &name,
                    resource_type_arguments,
                    resource_definitions,
                )?;
                let info = declared_resource_info(
                    &name,
                    arguments.len() + resource_arguments.len(),
                    resource_definitions,
                )?;
                validate_resource_reference_arguments(
                    &name,
                    &arguments,
                    &resource_arguments,
                    &info,
                    resource_definitions,
                )?;
                return Ok(ResourceClause::Named {
                    binding,
                    resource: Box::new(ResourceClause::Declared {
                        type_schema: type_schema.clone(),
                        resource_type_arguments: resource_type_arguments.clone(),
                        resource_arguments: resource_arguments.clone(),
                        access: ResourceAccessMode::Own,
                        kind: info.kind,
                        name,
                        arguments: arguments
                            .into_iter()
                            .map(|arg| {
                                expand_declared_resource_expression(arg, resource_definitions)
                            })
                            .collect::<Result<_, _>>()?,
                        parameter_types: info.parameter_types,
                    }),
                });
            }
            let info = declared_resource_info_with_fields(
                &name,
                arguments.len() + resource_arguments.len(),
                resource_definitions,
                true,
            )?;
            validate_resource_reference_arguments(
                &name,
                &arguments,
                &resource_arguments,
                &info,
                resource_definitions,
            )?;
            if !info.has_fields {
                return Err(ClickError::new(format!(
                    "resource `{name}` has no fields; use ordinary unnamed ownership"
                )));
            }
            // The parent's family decides what its child slots are. An
            // explicit fold names it; for an unfolded child instance the
            // parser could only record the family it was unfolded from, so
            // prefer what an earlier declaration fixed.
            let construction = binding.fold_fields.is_some();
            if !construction {
                resource_definitions.refuse_ambiguous(binding.identity, &binding.name)?;
            }
            let parent = if construction {
                name.clone()
            } else {
                resource_definitions
                    .instance_resource(binding.identity)
                    .unwrap_or_else(|| name.clone())
            };
            // Unfold syntax can still carry the parser's provisional parent
            // family for a child. Keep the family resolved above, including
            // after an explicit child fold removed its slot annotation.
            resource_definitions.record_instance(binding.identity, &parent, construction);
            if let Some(children) = binding.child_bindings.as_ref() {
                let slots = resource_definitions
                    .get(&parent)
                    .map(|info| info.child_slots.clone())
                    .unwrap_or_default();
                let fields = resource_definitions
                    .get(&parent)
                    .map(|info| info.fields.clone())
                    .unwrap_or_default();
                for (slot, child, identity) in children.iter() {
                    // An unfold pattern may also name a scalar field: the
                    // binder is then a proof name for the field's folded
                    // value, not a child instance.
                    if let Some((_, field_type)) = fields.get(slot) {
                        if construction {
                            return Err(ClickError::new(format!(
                                "`{slot}` is a field of `{parent}`, not a child slot; supply it in the fold's field map"
                            )));
                        }
                        if !matches!(field_type, ClickType::Program(_)) {
                            return Err(ClickError::new(format!(
                                "field `{slot}` of `{parent}` is not C-typed; an unfold pattern binds only C scalar and pointer fields, so read an algebraic field's payload with a proof `match` on `{}.{slot}` before the unfold",
                                binding.name
                            )));
                        }
                        resource_definitions.record_field_binder(*identity);
                        continue;
                    }
                    let Some(declared) = slots.get(slot) else {
                        return Err(ClickError::new(format!(
                            "resource `{parent}` has no child slot or field `{slot}`"
                        )));
                    };
                    // A slot whose resource differs between the parent's
                    // arms owns the one in the arm an enclosing proof
                    // `match` selects.
                    let Some(declared) = declared.clone().or_else(|| {
                        resource_definitions.selected_arm_slot(binding.identity, &parent, slot)
                    }) else {
                        continue;
                    };
                    let declared = &declared;
                    match resource_definitions.instance_resource(*identity) {
                        // An introduced child takes the slot's resource.
                        None => resource_definitions.record_child(*identity, declared),
                        Some(actual) if actual != *declared => {
                            return Err(ClickError::new(format!(
                                "child `{child}` is `{actual}`, but slot `{slot}` of `{parent}` owns `{declared}`"
                            )));
                        }
                        Some(_) => {}
                    }
                }
            }
            // A child a fold's map left out defaults to the in-scope
            // resource of the slot's name only when that resource is of the
            // family the slot owns; any other candidate is dropped, and the
            // fold then reports the slot as missing.
            if let Some(defaults) = binding.default_child_bindings.take() {
                let slots = resource_definitions
                    .get(&parent)
                    .map(|info| info.child_slots.clone())
                    .unwrap_or_default();
                let kept = defaults
                    .iter()
                    .filter(|(slot, _, identity)| match slots.get(slot) {
                        Some(Some(declared)) => resource_definitions
                            .instance_resource(*identity)
                            .is_none_or(|actual| actual == *declared),
                        Some(None) => true,
                        None => false,
                    })
                    .cloned()
                    .collect::<Vec<_>>();
                binding.default_child_bindings = (!kept.is_empty()).then(|| kept.into());
            }
            if let Some(fields) = binding.fold_fields.take() {
                binding.fold_fields = Some(
                    fields
                        .into_iter()
                        .map(|(name, value)| {
                            Ok((
                                name,
                                expand_declared_resource_expression(value, resource_definitions)?,
                            ))
                        })
                        .collect::<Result<_, ClickError>>()?,
                );
            }
            Ok(ResourceClause::Named {
                binding,
                resource: Box::new(ResourceClause::Declared {
                    type_schema: type_schema.clone(),
                    resource_type_arguments: resource_type_arguments.clone(),
                    resource_arguments: resource_arguments.clone(),
                    access: ResourceAccessMode::Own,
                    kind: info.kind,
                    name,
                    arguments: resource_definitions
                        .expand_arguments(arguments, &info.parameter_types)?,
                    parameter_types: info.parameter_types,
                }),
            })
        }
        ResourceClause::Quantified { quantity, resource } => {
            reject_counted_field_resource(&resource, resource_definitions)?;
            Ok(ResourceClause::Quantified {
                quantity: expand_declared_resource_expression(quantity, resource_definitions)?,
                resource: Box::new(expand_declared_resource_clause(
                    *resource,
                    resource_definitions,
                )?),
            })
        }
        ResourceClause::Declared { .. } => {
            expand_resource_application(resource, resource_definitions, false)
        }
        resource => Ok(resource),
    }
}

/// Resolve and type the application. A slot operand uses the declaration's
/// clause, so it can name a family's arguments even when a whole instance
/// of that family would require a bound model.
fn expand_resource_application(
    resource: ResourceClause,
    resource_definitions: &DeclaredResourceScope,
    allow_fields: bool,
) -> Result<ResourceClause, ClickError> {
    match resource {
        ResourceClause::Declared {
            type_schema,
            resource_type_arguments,
            resource_arguments,
            access,
            kind: _,
            name,
            arguments,
            parameter_types,
        } if parameter_types.is_empty() => {
            let resource_type_arguments = expand_resource_type_arguments(
                &name,
                resource_type_arguments,
                resource_definitions,
            )?;
            let info = declared_resource_info_with_fields(
                &name,
                arguments.len() + resource_arguments.len(),
                resource_definitions,
                allow_fields,
            )?;
            validate_resource_reference_arguments(
                &name,
                &arguments,
                &resource_arguments,
                &info,
                resource_definitions,
            )?;
            if (name == ResourceFact::ALLOCATION_RESOURCE_NAME
                || name == "mutex_guard"
                || name == "mutex_live"
                || name == "mutex_use"
                || name == "authority"
                || name == "publisher"
                || name == "subscriber")
                && access == ResourceAccessMode::View
            {
                return Err(ClickError::new(format!(
                    "{name} authority is owned and cannot be viewed or duplicated"
                )));
            }
            Ok(ResourceClause::Declared {
                type_schema: type_schema.clone(),
                resource_type_arguments: resource_type_arguments.clone(),
                resource_arguments: resource_arguments.clone(),
                access,
                kind: info.kind,
                name,
                arguments: resource_definitions
                    .expand_arguments(arguments, &info.parameter_types)?,
                parameter_types: info.parameter_types,
            })
        }
        resource => Ok(resource),
    }
}

fn declared_resource_type_schema(
    info: &DeclaredResourceInfo,
) -> Result<crate::kernel::ResourceFieldSchema, ClickError> {
    if let Some(schema) = &info.field_schema {
        return Ok(schema.clone());
    }
    let mut fields = info
        .fields
        .iter()
        .map(|(name, (index, ty))| {
            let ty = match ty {
                ClickType::Program(ty)
                | ClickType::CObjectPointer {
                    interface_type: ty, ..
                } => crate::kernel::ResourceFieldType::Program(ty.to_kernel_type()),
                ClickType::Integer => crate::kernel::ResourceFieldType::Integer,
                _ => {
                    return Err(ClickError::new(
                        "protected resource types currently require C or integer model fields",
                    ));
                }
            };
            Ok((*index, name.clone(), ty))
        })
        .collect::<Result<Vec<_>, ClickError>>()?;
    fields.sort_by_key(|(index, _, _)| *index);
    let schema = crate::kernel::ResourceFieldSchema::new(
        fields.into_iter().map(|(_, name, ty)| (name, ty)).collect(),
    )
    .ok_or_else(|| ClickError::new("invalid protected resource field schema"))?;
    Ok(schema)
}

fn expand_resource_type_arguments(
    name: &str,
    arguments: Vec<ResourceClause>,
    definitions: &DeclaredResourceScope,
) -> Result<Vec<ResourceClause>, ClickError> {
    let is_authority = name == "authority";
    if name == "authority" && arguments.len() != 1 {
        return Err(ClickError::new(
            "authority expects exactly one resource type",
        ));
    }
    if arguments.is_empty() {
        return Ok(arguments);
    }
    if !matches!(name, "mutex_use" | "authority" | "publisher" | "subscriber")
        || arguments.len() != 1
    {
        return Err(ClickError::new(format!(
            "resource `{name}` does not accept these resource type arguments"
        )));
    }
    arguments
        .into_iter()
        .map(|argument| {
            let ResourceClause::Declared {
                access,
                name,
                arguments,
                resource_arguments,
                resource_type_arguments,
                ..
            } = argument
            else {
                return Err(ClickError::new("expected a declared resource type"));
            };
            if !resource_arguments.is_empty()
                || !resource_type_arguments.is_empty()
                || matches!(
                    name.as_str(),
                    "mutex_live"
                        | "mutex_use"
                        | "mutex_guard"
                        | "authority"
                        | "publisher"
                        | "subscriber"
                )
            {
                return Err(ClickError::new(
                    "protected resource types currently require ordinary value arguments",
                ));
            }
            let info =
                declared_resource_info_with_fields(&name, arguments.len(), definitions, true)?;
            if is_authority && !info.authorized {
                return Err(unauthorized_family_error("authority", &name));
            }
            if is_authority
                && (arguments.is_empty()
                    || !info.parameter_types[0].is_pointer()
                    || access != ResourceAccessMode::Own
                    || matches!(arguments[0], ContractExpression::ResourceWildcard)
                    || arguments
                        .iter()
                        .skip(1)
                        .any(|argument| !matches!(argument, ContractExpression::ResourceWildcard)))
            {
                return Err(ClickError::new(
                    "authority requires R(anchor) or R(anchor, _, ...) with a pointer anchor",
                ));
            }
            let schema = declared_resource_type_schema(&info)?;
            Ok(ResourceClause::Declared {
                type_schema: Some(schema),
                access,
                name,
                kind: info.kind,
                parameter_types: info.parameter_types,
                arguments: arguments
                    .into_iter()
                    .map(|arg| expand_declared_resource_expression(arg, definitions))
                    .collect::<Result<_, _>>()?,
                resource_arguments,
                resource_type_arguments,
            })
        })
        .collect()
}

fn expand_declared_resource_subject(
    resource: ResourceSubject,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ResourceSubject, ClickError> {
    match resource {
        ResourceSubject::At { selector, resource } => Ok(ResourceSubject::At {
            selector,
            resource: Box::new(expand_declared_resource_subject(
                *resource,
                resource_definitions,
            )?),
        }),
        ResourceSubject::Emp => Ok(ResourceSubject::Emp),
        ResourceSubject::Star(left, right) => Ok(ResourceSubject::Star(
            Box::new(expand_declared_resource_subject(
                *left,
                resource_definitions,
            )?),
            Box::new(expand_declared_resource_subject(
                *right,
                resource_definitions,
            )?),
        )),
        ResourceSubject::Declared {
            kind: _,
            name,
            arguments,
            parameter_types,
        } if parameter_types.is_empty() => {
            let info = declared_resource_info(&name, arguments.len(), resource_definitions)?;
            Ok(ResourceSubject::Declared {
                kind: info.kind,
                name,
                arguments: resource_definitions
                    .expand_arguments(arguments, &info.parameter_types)?,
                parameter_types: info.parameter_types,
            })
        }
        resource => Ok(resource),
    }
}

fn expand_declared_resource_proposition(
    proposition: ClickProposition,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ClickProposition, ClickError> {
    enum Frame {
        Visit(ClickProposition),
        BuildAt(ProgramPointSelector),
        BuildAnd,
        BuildOr,
        BuildNot,
        BuildImplies,
        BuildForAll {
            click_type: ClickType,
            name: SurfaceBinder,
            written_name: Option<String>,
            shadowed: crate::surface::scoped_names::Scope,
        },
        BuildExists {
            click_type: ClickType,
            name: SurfaceBinder,
            written_name: Option<String>,
            shadowed: crate::surface::scoped_names::Scope,
        },
        BuildRangeAll {
            start: ContractExpression,
            end: ContractExpression,
            item: SurfaceBinder,
            written_item: Option<String>,
            shadowed: crate::surface::scoped_names::Scope,
        },
        BuildRangeAny {
            start: ContractExpression,
            end: ContractExpression,
            item: SurfaceBinder,
            written_item: Option<String>,
            shadowed: crate::surface::scoped_names::Scope,
        },
    }
    let constructors = &resource_definitions.constructors;
    // A binder's type holds for its body; the frame that rebuilds the
    // binder restores what its name meant outside. On an error the whole
    // declaration fails, so nothing is left to restore.

    let mut frames = vec![Frame::Visit(proposition)];
    let mut expanded = Vec::new();
    while let Some(frame) = frames.pop() {
        match frame {
            Frame::Visit(proposition) => match proposition {
                ClickProposition::And(left, right) => {
                    frames.push(Frame::BuildAnd);
                    frames.push(Frame::Visit(*right));
                    frames.push(Frame::Visit(*left));
                }
                ClickProposition::Or(left, right) => {
                    frames.push(Frame::BuildOr);
                    frames.push(Frame::Visit(*right));
                    frames.push(Frame::Visit(*left));
                }
                ClickProposition::Implies(left, right) => {
                    frames.push(Frame::BuildImplies);
                    frames.push(Frame::Visit(*right));
                    frames.push(Frame::Visit(*left));
                }
                ClickProposition::Not(body) => {
                    frames.push(Frame::BuildNot);
                    frames.push(Frame::Visit(*body));
                }
                ClickProposition::At {
                    selector,
                    proposition,
                } => {
                    frames.push(Frame::BuildAt(selector));
                    frames.push(Frame::Visit(*proposition));
                }
                ClickProposition::ForAll {
                    click_type,
                    name,
                    written_name,
                    body,
                } => {
                    let shadowed = constructors.bind(&name, Some(click_type.clone()));
                    frames.push(Frame::BuildForAll {
                        click_type,
                        name,
                        written_name,
                        shadowed,
                    });
                    frames.push(Frame::Visit(*body));
                }
                ClickProposition::Exists {
                    click_type,
                    name,
                    written_name,
                    body,
                } => {
                    let shadowed = constructors.bind(&name, Some(click_type.clone()));
                    frames.push(Frame::BuildExists {
                        click_type,
                        name,
                        written_name,
                        shadowed,
                    });
                    frames.push(Frame::Visit(*body));
                }
                ClickProposition::RangeAll {
                    start,
                    end,
                    item,
                    written_item,
                    body,
                } => {
                    let start = expand_declared_resource_expression(start, resource_definitions)?;
                    let end = expand_declared_resource_expression(end, resource_definitions)?;
                    let shadowed = constructors.bind(&item, None);
                    frames.push(Frame::BuildRangeAll {
                        start,
                        end,
                        item,
                        written_item,
                        shadowed,
                    });
                    frames.push(Frame::Visit(*body));
                }
                ClickProposition::RangeAny {
                    start,
                    end,
                    item,
                    written_item,
                    body,
                } => {
                    let start = expand_declared_resource_expression(start, resource_definitions)?;
                    let end = expand_declared_resource_expression(end, resource_definitions)?;
                    let shadowed = constructors.bind(&item, None);
                    frames.push(Frame::BuildRangeAny {
                        start,
                        end,
                        item,
                        written_item,
                        shadowed,
                    });
                    frames.push(Frame::Visit(*body));
                }
                proposition => expanded.push(expand_declared_resource_proposition_one(
                    proposition,
                    resource_definitions,
                )?),
            },
            Frame::BuildAnd => {
                let right = expanded.pop().expect("expanded conjunction right operand");
                let left = expanded.pop().expect("expanded conjunction left operand");
                expanded.push(ClickProposition::And(Box::new(left), Box::new(right)));
            }
            Frame::BuildOr => {
                let right = expanded.pop().expect("expanded disjunction right operand");
                let left = expanded.pop().expect("expanded disjunction left operand");
                expanded.push(ClickProposition::Or(Box::new(left), Box::new(right)));
            }
            Frame::BuildImplies => {
                let right = expanded.pop().expect("expanded implication right operand");
                let left = expanded.pop().expect("expanded implication left operand");
                expanded.push(ClickProposition::Implies(Box::new(left), Box::new(right)));
            }
            Frame::BuildNot => {
                let body = expanded.pop().expect("expanded negation body");
                expanded.push(ClickProposition::Not(Box::new(body)));
            }
            Frame::BuildAt(selector) => {
                let proposition = expanded.pop().expect("expanded state proposition");
                expanded.push(ClickProposition::At {
                    selector,
                    proposition: Box::new(proposition),
                });
            }
            Frame::BuildForAll {
                click_type,
                name,
                written_name,
                shadowed,
            } => {
                constructors.restore(shadowed);
                let body = expanded.pop().expect("expanded universal body");
                expanded.push(ClickProposition::ForAll {
                    click_type,
                    name,
                    written_name,
                    body: Box::new(body),
                });
            }
            Frame::BuildExists {
                click_type,
                name,
                written_name,
                shadowed,
            } => {
                constructors.restore(shadowed);
                let body = expanded.pop().expect("expanded existential body");
                expanded.push(ClickProposition::Exists {
                    click_type,
                    name,
                    written_name,
                    body: Box::new(body),
                });
            }
            Frame::BuildRangeAll {
                start,
                end,
                item,
                written_item,
                shadowed,
            } => {
                constructors.restore(shadowed);
                let body = expanded.pop().expect("expanded range universal body");
                expanded.push(ClickProposition::RangeAll {
                    start,
                    end,
                    item,
                    written_item,
                    body: Box::new(body),
                });
            }
            Frame::BuildRangeAny {
                start,
                end,
                item,
                written_item,
                shadowed,
            } => {
                constructors.restore(shadowed);
                let body = expanded.pop().expect("expanded range existential body");
                expanded.push(ClickProposition::RangeAny {
                    start,
                    end,
                    item,
                    written_item,
                    body: Box::new(body),
                });
            }
        }
    }
    Ok(expanded
        .pop()
        .expect("expanded proposition should have one root"))
}

fn expand_declared_resource_proposition_one(
    proposition: ClickProposition,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ClickProposition, ClickError> {
    match proposition {
        ClickProposition::Value(expression) => Ok(ClickProposition::Value(
            expand_declared_resource_expression(expression, resource_definitions)?,
        )),

        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let mut left = expand_declared_resource_expression(left, resource_definitions)?;
            let mut right = expand_declared_resource_expression(right, resource_definitions)?;
            resource_definitions
                .constructors
                .resolve_comparison(&mut left, &mut right);
            Ok(ClickProposition::Comparison {
                left,
                operator,
                right,
            })
        }
        ClickProposition::Defined { expression } => Ok(ClickProposition::Defined {
            expression: expand_declared_resource_expression(expression, resource_definitions)?,
        }),
        ClickProposition::Separate { left, right } => Ok(ClickProposition::Separate {
            left: expand_declared_resource_subject(left, resource_definitions)?,
            right: expand_declared_resource_subject(right, resource_definitions)?,
        }),
        ClickProposition::Contains { parent, child } => Ok(ClickProposition::Contains {
            parent: expand_declared_resource_subject(parent, resource_definitions)?,
            child: expand_declared_resource_subject(child, resource_definitions)?,
        }),
        ClickProposition::ResourceViewable { resource } => Ok(ClickProposition::ResourceViewable {
            resource: expand_declared_resource_subject(resource, resource_definitions)?,
        }),
        ClickProposition::And(left, right) => Ok(ClickProposition::And(
            Box::new(expand_declared_resource_proposition(
                *left,
                resource_definitions,
            )?),
            Box::new(expand_declared_resource_proposition(
                *right,
                resource_definitions,
            )?),
        )),
        ClickProposition::Or(left, right) => Ok(ClickProposition::Or(
            Box::new(expand_declared_resource_proposition(
                *left,
                resource_definitions,
            )?),
            Box::new(expand_declared_resource_proposition(
                *right,
                resource_definitions,
            )?),
        )),
        ClickProposition::Implies(left, right) => Ok(ClickProposition::Implies(
            Box::new(expand_declared_resource_proposition(
                *left,
                resource_definitions,
            )?),
            Box::new(expand_declared_resource_proposition(
                *right,
                resource_definitions,
            )?),
        )),
        ClickProposition::Not(body) => Ok(ClickProposition::Not(Box::new(
            expand_declared_resource_proposition(*body, resource_definitions)?,
        ))),
        ClickProposition::At {
            selector,
            proposition,
        } => Ok(ClickProposition::At {
            selector,
            proposition: Box::new(expand_declared_resource_proposition(
                *proposition,
                resource_definitions,
            )?),
        }),
        ClickProposition::ForAll {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => Ok(ClickProposition::ForAll {
            click_type: interface_type,
            name,
            written_name,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::Exists {
            click_type: interface_type,
            name,
            written_name,
            body,
        } => Ok(ClickProposition::Exists {
            click_type: interface_type,
            name,
            written_name,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::RangeAll {
            start,
            end,
            item,
            written_item,
            body,
        } => Ok(ClickProposition::RangeAll {
            start: expand_declared_resource_expression(start, resource_definitions)?,
            end: expand_declared_resource_expression(end, resource_definitions)?,
            item,
            written_item,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::RangeAny {
            start,
            end,
            item,
            written_item,
            body,
        } => Ok(ClickProposition::RangeAny {
            start: expand_declared_resource_expression(start, resource_definitions)?,
            end: expand_declared_resource_expression(end, resource_definitions)?,
            item,
            written_item,
            body: Box::new(expand_declared_resource_proposition(
                *body,
                resource_definitions,
            )?),
        }),
        ClickProposition::PredicateCall { name, arguments } => {
            let mut arguments = arguments
                .into_iter()
                .map(|argument| expand_declared_resource_expression(argument, resource_definitions))
                .collect::<Result<Vec<_>, _>>()?;
            resource_definitions.constructors.resolve_call(
                CallKind::Predicate,
                &name,
                &mut arguments,
            );
            Ok(ClickProposition::PredicateCall { name, arguments })
        }
        proposition => Ok(proposition),
    }
}

fn expand_declared_resource_expression(
    expression: ContractExpression,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ContractExpression, ClickError> {
    let mut add_depth = 0;
    let mut add_cursor = &expression;
    while let ContractExpression::Add(left, _) = add_cursor {
        add_depth += 1;
        add_cursor = left;
    }
    if add_depth > 0 {
        let mut operands = Vec::with_capacity(add_depth);
        let mut current = expression;
        while let ContractExpression::Add(left, right) = current {
            operands.push(*right);
            current = *left;
        }
        let mut expanded = expand_declared_resource_expression(current, resource_definitions)?;
        for operand in operands.into_iter().rev() {
            expanded = ContractExpression::Add(
                Box::new(expanded),
                Box::new(expand_declared_resource_expression(
                    operand,
                    resource_definitions,
                )?),
            );
        }
        return Ok(expanded);
    }
    // Peel a direct conditional chain before entering the large child match.
    // Conditions and sibling branches retain their source order while the
    // recursively nested `then` spine is rebuilt from the inside out.
    let mut conditionals = Vec::new();
    let mut expression = expression;
    while let ContractExpression::If {
        condition,
        then_branch,
        else_branch,
    } = expression
    {
        conditionals.push((
            expand_declared_resource_proposition(*condition, resource_definitions)?,
            expand_declared_resource_expression(*else_branch, resource_definitions)?,
        ));
        expression = *then_branch;
    }

    // Let chains are common in generated specifications and can be much
    // deeper than the surrounding expression tree. Peel consecutive lets
    // iteratively so expanding their bodies does not retain one large match
    // frame per binding.
    type ExpandedLet = (
        SurfaceBinder,
        Option<ClickType>,
        ContractExpression,
        crate::surface::scoped_names::Scope,
    );
    let mut lets: Vec<ExpandedLet> = Vec::new();
    while let ContractExpression::Let {
        name,
        click_type,
        value,
        body,
    } = expression
    {
        let expanded = expand_let_value(&name, click_type.as_ref(), *value, resource_definitions);
        let (value, previous) = match expanded {
            Ok(expanded) => expanded,
            Err(error) => {
                if let Some((_, _, _, first)) = lets.first() {
                    resource_definitions.constructors.restore(*first);
                }
                return Err(error);
            }
        };
        lets.push((name, click_type, value, previous));
        expression = *body;
    }
    let expanded = expand_declared_resource_expression_node(expression, resource_definitions);
    if let Some((_, _, _, first)) = lets.first() {
        resource_definitions.constructors.restore(*first);
    }
    let mut expanded = expanded?;
    while let Some((name, click_type, value, _)) = lets.pop() {
        expanded = ContractExpression::Let {
            name,
            click_type,
            value: Box::new(value),
            body: Box::new(expanded),
        };
    }
    while let Some((condition, else_branch)) = conditionals.pop() {
        expanded = ContractExpression::If {
            condition: Box::new(condition),
            then_branch: Box::new(expanded),
            else_branch: Box::new(else_branch),
        };
    }
    Ok(expanded)
}

/// A `let` value, expanded, with a written type pushed into it, and the
/// binding its name had before the `let`, for the caller to restore once
/// the body is expanded.
fn expand_let_value(
    name: impl Into<SurfaceBinder>,
    click_type: Option<&ClickType>,
    value: ContractExpression,
    resource_definitions: &DeclaredResourceScope,
) -> Result<(ContractExpression, crate::surface::scoped_names::Scope), ClickError> {
    let name = name.into();
    let constructors = &resource_definitions.constructors;
    let mut value = value;
    if let Some(click_type) = click_type {
        constructors.push_expected(&mut value, click_type);
    }
    let mut value = expand_declared_resource_expression(value, resource_definitions)?;
    if let Some(click_type) = click_type {
        constructors.push_expected(&mut value, click_type);
    }
    let bound = click_type
        .cloned()
        .or_else(|| constructors.binding_type(&value));
    Ok((value, constructors.bind(name, bound)))
}

fn expand_declared_resource_expression_node(
    expression: ContractExpression,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ContractExpression, ClickError> {
    match expression {
        ContractExpression::Resource(subject) => Ok(ContractExpression::Resource(Box::new(
            expand_declared_resource_subject(*subject, resource_definitions)?,
        ))),
        ContractExpression::Call { name, arguments }
            if resource_definitions.definitions.contains_key(&name) =>
        {
            Ok(ContractExpression::Resource(Box::new(
                expand_declared_resource_subject(
                    ResourceSubject::Declared {
                        kind: ResourceKind::Token,
                        name,
                        arguments,
                        parameter_types: vec![],
                    },
                    resource_definitions,
                )?,
            )))
        }

        ContractExpression::ResourceField(mut access) => {
            if let Some(name) = resource_definitions
                .unowned_resource_parameters
                .borrow()
                .get(&access.identity)
            {
                return Err(ClickError::new(format!("Requires owns {name}")));
            }
            match resource_definitions.family(access.identity) {
                Some(InstanceFamily::FieldValue) => {
                    return Err(ClickError::new(format!(
                        "`{}` names the value of a resource field, not a resource instance",
                        access.owner
                    )));
                }
                Some(InstanceFamily::Child(name)) => access.resource_name = name,
                _ => resource_definitions.refuse_ambiguous(access.identity, &access.owner)?,
            }
            let info = resource_definitions
                .get(&access.resource_name)
                .ok_or_else(|| {
                    ClickError::new(format!("unknown resource `{}`", access.resource_name))
                })?;
            // A hidden record retains child fields under their structural
            // dotted path. Select that slot without opening the child.
            if !access.children.is_empty() {
                let path = access
                    .children
                    .iter()
                    .map(String::as_str)
                    .chain(std::iter::once(access.field.as_str()))
                    .collect::<Vec<_>>()
                    .join(".");
                if info.fields.contains_key(&path) {
                    access.field = path;
                    access.children.clear();
                }
            }
            let (index, field) = info.fields.get(&access.field).ok_or_else(|| {
                ClickError::new(format!(
                    "resource `{}` has no field `{}`",
                    access.resource_name, access.field
                ))
            })?;
            access.field_index = *index;
            access.click_type = Some(field.clone());
            Ok(ContractExpression::ResourceField(access))
        }
        ContractExpression::ResourceCount(resource) => {
            if resource_definitions.family_rules
                && let ResourceClause::Declared { name, .. } = resource.as_ref()
                && resource_definitions
                    .get(name)
                    .is_some_and(|info| !info.authorized)
                && !matches!(
                    name.as_str(),
                    "authority"
                        | "mutex_guard"
                        | "mutex_live"
                        | "mutex_use"
                        | "publisher"
                        | "subscriber"
                )
                && name != ResourceFact::ALLOCATION_RESOURCE_NAME
            {
                return Err(unauthorized_family_error("count", name));
            }
            if resource_definitions.family_rules
                && let ResourceClause::Declared {
                    name,
                    arguments,
                    resource_arguments,
                    resource_type_arguments,
                    access,
                    ..
                } = resource.as_ref()
                && resource_definitions
                    .get(name)
                    .is_some_and(|info| info.has_fields)
            {
                let info = declared_resource_info_with_fields(
                    name,
                    arguments.len(),
                    resource_definitions,
                    true,
                )?;
                if !resource_arguments.is_empty() || !resource_type_arguments.is_empty() {
                    return Err(ClickError::new("count requires ordinary value arguments"));
                }
                return Ok(ContractExpression::ResourceCount(Box::new(
                    ResourceClause::Declared {
                        type_schema: Some(declared_resource_type_schema(&info)?),
                        kind: info.kind,
                        parameter_types: info.parameter_types,
                        name: name.clone(),
                        arguments: arguments
                            .iter()
                            .cloned()
                            .map(|argument| {
                                expand_declared_resource_expression(argument, resource_definitions)
                            })
                            .collect::<Result<_, _>>()?,
                        resource_arguments: resource_arguments.clone(),
                        resource_type_arguments: resource_type_arguments.clone(),
                        access: *access,
                    },
                )));
            }
            reject_counted_field_resource(&resource, resource_definitions)?;
            let resource = expand_declared_resource_clause(*resource, resource_definitions)?;
            Ok(ContractExpression::ResourceCount(Box::new(resource)))
        }
        expression @ (ContractExpression::SequenceConcat(..)
        | ContractExpression::Add(..)
        | ContractExpression::Subtract(..)
        | ContractExpression::Multiply(..)
        | ContractExpression::Divide(..)
        | ContractExpression::Remainder(..)
        | ContractExpression::ShiftLeft(..)
        | ContractExpression::RustShiftLeft(..)
        | ContractExpression::ShiftRight(..)
        | ContractExpression::RustShiftRight(..)
        | ContractExpression::BitwiseAnd(..)
        | ContractExpression::BitwiseOr(..)
        | ContractExpression::BitwiseXor(..)
        | ContractExpression::Index(..)) => {
            expand_declared_resource_binary_expression(expression, resource_definitions)
        }
        expression => {
            expand_declared_resource_expression_children(expression, resource_definitions)
        }
    }
}

// Keep the recursive expression walk's large child-rewriting match out of the
// frame retained by each nested expression.
#[inline(never)]
fn expand_declared_resource_binary_expression(
    expression: ContractExpression,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ContractExpression, ClickError> {
    let recurse =
        |expression| expand_declared_resource_expression(expression, resource_definitions);
    Ok(match expression {
        ContractExpression::SequenceConcat(left, right) => ContractExpression::SequenceConcat(
            Box::new(recurse(*left)?),
            Box::new(recurse(*right)?),
        ),
        ContractExpression::Add(left, right) => {
            ContractExpression::Add(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::Subtract(left, right) => {
            ContractExpression::Subtract(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::Multiply(left, right) => match (recurse(*left)?, recurse(*right)?) {
            (ContractExpression::Resource(left), ContractExpression::Resource(right)) => {
                ContractExpression::Resource(Box::new(ResourceSubject::Star(left, right)))
            }
            (left, right) => ContractExpression::Multiply(Box::new(left), Box::new(right)),
        },
        ContractExpression::Divide(left, right) => {
            ContractExpression::Divide(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::Remainder(left, right) => {
            ContractExpression::Remainder(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::ShiftLeft(left, right) => {
            ContractExpression::ShiftLeft(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::RustShiftLeft(left, right) => {
            ContractExpression::RustShiftLeft(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::ShiftRight(left, right) => {
            ContractExpression::ShiftRight(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::RustShiftRight(left, right) => ContractExpression::RustShiftRight(
            Box::new(recurse(*left)?),
            Box::new(recurse(*right)?),
        ),
        ContractExpression::BitwiseAnd(left, right) => {
            ContractExpression::BitwiseAnd(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::BitwiseOr(left, right) => {
            ContractExpression::BitwiseOr(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::BitwiseXor(left, right) => {
            ContractExpression::BitwiseXor(Box::new(recurse(*left)?), Box::new(recurse(*right)?))
        }
        ContractExpression::Index(base, index) => {
            ContractExpression::Index(Box::new(recurse(*base)?), Box::new(recurse(*index)?))
        }
        _ => unreachable!("non-binary contract expression"),
    })
}

// Keep the remaining recursive expression cases out of the frame retained by
// each nested expression.
#[inline(never)]
fn expand_declared_resource_expression_children(
    expression: ContractExpression,
    resource_definitions: &DeclaredResourceScope,
) -> Result<ContractExpression, ClickError> {
    let recurse =
        |expression| expand_declared_resource_expression(expression, resource_definitions);
    Ok(match expression {
        ContractExpression::Negate(inner) => ContractExpression::Negate(Box::new(recurse(*inner)?)),
        ContractExpression::Proposition(proposition) => ContractExpression::Proposition(Box::new(
            expand_declared_resource_proposition(*proposition, resource_definitions)?,
        )),

        ContractExpression::Lambda {
            parameters,
            result,
            body,
        } => {
            let constructors = &resource_definitions.constructors;
            let scopes = parameters
                .iter()
                .map(|(name, ty)| constructors.bind(name, Some(ty.clone())))
                .collect::<Vec<_>>();
            let body = recurse(*body);
            if let Some(scope) = scopes.first() {
                constructors.restore(*scope);
            }
            ContractExpression::Lambda {
                parameters,
                result,
                body: Box::new(body?),
            }
        }
        ContractExpression::Apply {
            function,
            arguments,
        } => ContractExpression::Apply {
            function: Box::new(recurse(*function)?),
            arguments: arguments
                .into_iter()
                .map(recurse)
                .collect::<Result<_, _>>()?,
        },

        ContractExpression::IntegerContext(value) => {
            ContractExpression::IntegerContext(Box::new(recurse(*value)?))
        }
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => {
            let mut constructor = ContractExpression::AlgebraicConstructor {
                algebraic_type,
                variant,
                arguments: arguments
                    .into_iter()
                    .map(recurse)
                    .collect::<Result<_, _>>()?,
            };
            resource_definitions
                .constructors
                .resolve_constructor(&mut constructor);
            constructor
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            let scrutinee = recurse(*scrutinee)?;
            let constructors = &resource_definitions.constructors;
            ContractExpression::AlgebraicMatch {
                arms: arms
                    .into_iter()
                    .map(|mut arm| {
                        let types = constructors.arm_binding_types(&scrutinee, &arm);
                        let body =
                            std::mem::replace(&mut arm.body, ContractExpression::ResourceWildcard);
                        arm.body =
                            constructors.with_bindings(&arm.bindings, types, || recurse(body))?;
                        Ok(arm)
                    })
                    .collect::<Result<_, ClickError>>()?,
                scrutinee: Box::new(scrutinee),
            }
        }
        ContractExpression::SequenceLiteral(elements) => ContractExpression::SequenceLiteral(
            elements
                .into_iter()
                .map(recurse)
                .collect::<Result<_, _>>()?,
        ),
        ContractExpression::CUnary { operand, lowered } => ContractExpression::CUnary {
            operand: Box::new(recurse(*operand)?),
            lowered,
        },
        ContractExpression::Field {
            base,
            field,
            lowered,
            offset_bytes,
            pointee_struct,
        } => ContractExpression::Field {
            pointee_struct,
            base: Box::new(recurse(*base)?),
            field,
            lowered,
            offset_bytes,
        },
        ContractExpression::Old(body) => ContractExpression::Old(Box::new(recurse(*body)?)),
        ContractExpression::At {
            selector,
            expression,
        } => match recurse(*expression)? {
            ContractExpression::Resource(resource) => {
                ContractExpression::Resource(Box::new(ResourceSubject::At { selector, resource }))
            }
            expression => ContractExpression::At {
                selector,
                expression: Box::new(expression),
            },
        },
        ContractExpression::BitwiseNot(body) => {
            ContractExpression::BitwiseNot(Box::new(recurse(*body)?))
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => ContractExpression::If {
            condition: Box::new(expand_declared_resource_proposition(
                *condition,
                resource_definitions,
            )?),
            then_branch: Box::new(recurse(*then_branch)?),
            else_branch: Box::new(recurse(*else_branch)?),
        },
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let start = recurse(*start)?;
            let end = recurse(*end)?;
            let initial = recurse(*initial)?;
            let constructors = &resource_definitions.constructors;
            let accumulator_previous = constructors.bind(&accumulator, None);
            let item_previous = constructors.bind(&item, None);
            let body = recurse(*body);
            constructors.restore(item_previous);
            constructors.restore(accumulator_previous);
            ContractExpression::RangeFold {
                start: Box::new(start),
                end: Box::new(end),
                initial: Box::new(initial),
                accumulator,
                item,
                body: Box::new(body?),
            }
        }
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            let (value, previous) =
                expand_let_value(&name, click_type.as_ref(), *value, resource_definitions)?;
            let body = recurse(*body);
            resource_definitions.constructors.restore(previous);
            ContractExpression::Let {
                name,
                click_type,
                value: Box::new(value),
                body: Box::new(body?),
            }
        }
        ContractExpression::Call { name, arguments } => {
            let mut arguments = arguments
                .into_iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?;
            resource_definitions.constructors.resolve_call(
                CallKind::Function,
                &name,
                &mut arguments,
            );
            ContractExpression::Call { name, arguments }
        }
        ContractExpression::MethodCall {
            receiver,
            method,
            arguments,
        } => {
            let receiver = recurse(*receiver)?;
            let arguments = arguments
                .into_iter()
                .map(recurse)
                .collect::<Result<Vec<_>, _>>()?;
            resource_definitions
                .constructors
                .resolve_method(receiver, &method, arguments)?
        }
        expression => expression,
    })
}

fn declared_resource_info(
    name: &str,
    actual: usize,
    resource_definitions: &DeclaredResourceScope,
) -> Result<DeclaredResourceInfo, ClickError> {
    declared_resource_info_with_fields(name, actual, resource_definitions, false)
}

/// Population accounting covers only families declared `authorized resource`;
/// `authority(...)` and `count(...)` name nothing on any other family.
fn unauthorized_family_error(form: &str, family: &str) -> ClickError {
    ClickError::new(format!(
        "`{form}` names `{family}`, which is not an authorized family; declare it `authorized resource {family}(...)`"
    ))
}

fn declared_resource_info_with_fields(
    name: &str,
    actual: usize,
    resource_definitions: &DeclaredResourceScope,
    allow_fields: bool,
) -> Result<DeclaredResourceInfo, ClickError> {
    let Some(info) = resource_definitions.get(name) else {
        return Err(ClickError::new(format!(
            "unknown resource `{name}`{}",
            library_import_hint(name)
        )));
    };
    let expected = info.parameter_types.len() + info.resource_parameter_families.len();
    if expected != actual {
        return Err(ClickError::new(format!(
            "resource `{name}` expects {expected} argument(s), got {actual}"
        )));
    }
    if info.has_fields && !allow_fields {
        return Err(ClickError::new(format!(
            "resource `{name}` has fields; bind it with `owns name: {name}(...);`"
        )));
    }
    Ok(info.clone())
}

fn reject_counted_field_resource(
    resource: &ResourceClause,
    definitions: &DeclaredResourceScope,
) -> Result<(), ClickError> {
    match resource {
        ResourceClause::Declared { name, .. } if name == "mutex_use" => Err(ClickError::new(
            "`mutex_use` is exclusive and not countable",
        )),
        ResourceClause::Declared { name, .. }
            if matches!(name.as_str(), "publisher" | "subscriber") =>
        {
            Err(ClickError::new(format!(
                "`{name}` is exclusive and not countable"
            )))
        }
        ResourceClause::Declared { name, .. } if name == "mutex_live" => Err(ClickError::new(
            "`mutex_live` is exclusive and not countable",
        )),
        ResourceClause::Declared { name, .. } if name == "mutex_guard" => Err(ClickError::new(
            "`mutex_guard` is exclusive and not countable",
        )),
        ResourceClause::Declared { name, .. } if name == "authority" => Err(ClickError::new(
            "`authority` is exclusive and not countable",
        )),
        ResourceClause::Declared { name, .. }
            if definitions.get(name).is_some_and(|info| info.has_fields) =>
        {
            Err(ClickError::new(format!(
                "resource `{name}` has fields; quantities require separately named members"
            )))
        }
        ResourceClause::Quantified { resource, .. } => {
            reject_counted_field_resource(resource, definitions)
        }
        _ => Ok(()),
    }
}

pub(in crate::surface) fn combined_predicate_definitions(
    file: &ClickFile,
) -> Result<Vec<PredicateDefinition>, ClickError> {
    let mut definitions = file_library(file)?.file.predicate_definitions().to_vec();
    definitions.extend(file.predicate_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::surface) fn combined_click_function_definitions(
    file: &ClickFile,
) -> Result<Vec<ClickFunctionDefinition>, ClickError> {
    let mut definitions = file_library(file)?
        .file
        .click_function_definitions()
        .to_vec();
    definitions.extend(file.click_function_definitions().iter().cloned());
    Ok(definitions)
}

pub(in crate::surface) fn combined_resource_definitions(
    file: &ClickFile,
) -> Result<Vec<ResourceDefinition>, ClickError> {
    let mut definitions = file_library(file)?.resource_definitions().to_vec();
    definitions.extend(file.resource_definitions().iter().cloned());
    Ok(definitions)
}

/// The standard library's definitions followed by a file's, borrowed rather
/// than copied: the library is shared by every verification in the process.
pub(in crate::surface) struct CombinedDefinitions<'a, T: 'static> {
    standard_library: &'static [T],
    file: &'a [T],
}

impl<'a, T> CombinedDefinitions<'a, T> {
    pub(in crate::surface) fn iter(
        &self,
    ) -> std::iter::Chain<std::slice::Iter<'a, T>, std::slice::Iter<'a, T>> {
        self.standard_library.iter().chain(self.file.iter())
    }
}

impl<'a, T> IntoIterator for &CombinedDefinitions<'a, T> {
    type Item = &'a T;
    type IntoIter = std::iter::Chain<std::slice::Iter<'a, T>, std::slice::Iter<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub(in crate::surface) fn combined_theorem_definitions(
    file: &ClickFile,
) -> Result<CombinedDefinitions<'_, TheoremDefinition>, ClickError> {
    Ok(CombinedDefinitions {
        standard_library: file_library(file)?.theorem_definitions(),
        file: file.theorem_definitions(),
    })
}

/// The whole Click library's theorems followed by `file`'s, as proof
/// checking sees them: built-in tactics apply library theorems whatever a
/// file imports.
#[cfg(test)]
pub(in crate::surface) fn proof_theorem_definitions(
    file: &ClickFile,
) -> Result<CombinedDefinitions<'_, TheoremDefinition>, ClickError> {
    Ok(CombinedDefinitions {
        standard_library: full_library()?.theorem_definitions(),
        file: file.theorem_definitions(),
    })
}

/// The standard library's theorem definitions in declaration order.
///
/// A verification uses these as dependency declarations; it does not re-prove
/// them. [`crate::surface::verify_standard_library`] is the one entry point that
/// proves them.
pub(in crate::surface) fn standard_library_theorem_definitions()
-> Result<&'static [TheoremDefinition], ClickError> {
    Ok(full_library()?.theorem_definitions())
}

/// The declaration-order position of the named theorem in the whole Click
/// library.
pub(in crate::surface) fn standard_library_theorem_index(name: &str) -> Option<usize> {
    full_library().ok()?.theorem_index().get(name).copied()
}

/// A produced instance is of the resource its callee's contract names,
/// as an explicit fold's result is. The name it binds may have held a child
/// an earlier unfold introduced, whose slot fixed another resource; that
/// child's resource no longer describes it.
fn record_produced_instances(transport: &CallBinderTransport, definitions: &DeclaredResourceScope) {
    for produced in transport.produced() {
        if let Some(family) = produced.family() {
            definitions.record_instance(produced.identity(), family, true);
        }
    }
}

fn validate_resource_reference_arguments(
    name: &str,
    arguments: &[ContractExpression],
    references: &[ResourceInstanceBinding],
    info: &DeclaredResourceInfo,
    definitions: &DeclaredResourceScope,
) -> Result<(), ClickError> {
    if arguments.len() != info.parameter_types.len()
        || references.len() != info.resource_parameter_families.len()
    {
        return Err(ClickError::new(format!(
            "resource `{name}` expects {} ordinary and {} named resource argument(s)",
            info.parameter_types.len(),
            info.resource_parameter_families.len()
        )));
    }
    for (reference, expected) in references.iter().zip(&info.resource_parameter_families) {
        definitions.refuse_ambiguous(reference.identity, &reference.name)?;
        let actual = definitions
            .instance_resource(reference.identity)
            .ok_or_else(|| {
                ClickError::new(format!("unknown resource argument `{}`", reference.name))
            })?;
        if &actual != expected {
            return Err(ClickError::new(format!(
                "resource argument `{}` is `{actual}`, requires `{expected}`",
                reference.name
            )));
        }
    }
    Ok(())
}
