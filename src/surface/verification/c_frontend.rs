//! The C frontend: parses the verifying translation units of a source
//! bundle or of compiler-prepared C imports, links them, and builds the
//! layouts and objects a sidecar is parsed against. A prepared program of
//! another language arrives already lowered and does not pass through here.

use super::*;

/// Parses the verifying C translation units and links them: declarations
/// checked compatible, globals merged across units and file-scope `static`s
/// kept to their own unit. Each function comes with the source defining it.
pub(super) fn link_c_units(
    verifying_sources: &[String],
    target: CTarget,
    thread_runtime: crate::languages::c::thread_runtime::CThreadRuntime,
    external_functions: &[&str],
    c_sources: &CSourceContext<'_>,
    build_storage: bool,
) -> Result<BTreeMap<String, (String, syntax::C0Function)>, ClickError> {
    let mut parsed = BTreeMap::new();
    let mut units = BTreeMap::new();
    for source_path in verifying_sources {
        let unit = parse_c_source_unit(source_path, c_sources, target)?;
        units.insert(source_path.clone(), unit);
    }

    if thread_runtime == crate::languages::c::thread_runtime::CThreadRuntime::ModeledPthread {
        validate_modeled_pthread_binding(&units)?;
    }

    // Headers may declare libc objects that the verified program never uses.
    // Keep those declarations for compatibility checks, but require storage
    // only when a C value or address expression actually names the object.
    let referenced_external_objects = units
        .values()
        .flat_map(|unit| unit.referenced_external_objects.iter())
        .cloned()
        .collect::<BTreeSet<_>>();

    for (source_path, unit) in &mut units {
        for function in std::mem::take(&mut unit.functions) {
            let function_name = function.name().to_string();
            let previous = parsed.insert(function_name.clone(), (source_path.clone(), function));
            if previous.is_some() {
                return Err(ClickError::new(format!(
                    "more than one `verifying` source defines function `{function_name}`"
                )));
            }
        }
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
    if let Some((name, _)) = globals.iter().find(|(name, global)| {
        referenced_external_objects.contains(name.as_str()) && !global.is_defined()
    }) {
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
    if let Some((name, array)) = global_arrays.iter().find(|(name, array)| {
        !array.is_defined()
            && (array.is_tentative() || referenced_external_objects.contains(name.as_str()))
    }) {
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
    if let Some((name, _)) = global_aggregates.iter().find(|(name, aggregate)| {
        referenced_external_objects.contains(name.as_str()) && !aggregate.is_defined()
    }) {
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
    if let Some((name, _)) = global_aggregate_arrays.iter().find(|(name, aggregate)| {
        referenced_external_objects.contains(name.as_str()) && !aggregate.is_defined()
    }) {
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

    for name in external_functions {
        if parsed.contains_key(*name) {
            return Err(ClickError::new(format!(
                "external function `{name}` is also defined by a `verifying` source"
            )));
        }
    }

    if parsed.contains_key("main") {
        let mut storage_functions = if build_storage {
            parsed
                .values()
                .map(|(_, function)| function.to_kernel_static_storage(function.name() == "main"))
                .collect::<Vec<_>>()
        } else {
            Vec::new()
        };
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
            if build_storage {
                storage_functions.push(storage.to_kernel_static_storage(true));
            }
        }
        if build_storage {
            parsed
                .get_mut("main")
                .expect("main was found")
                .1
                .program_entry_state = Some(std::sync::Arc::new({
                let _timing = VerificationTimingPhase::new("program-entry storage");
                crate::kernel::initialize_c_program_storage(storage_functions).ok_or_else(|| {
                    ClickError::new(format!(
                        "verification budget exhausted inside {}",
                        instrumentation::deadline_context()
                    ))
                })?
            }));
        }
    }
    Ok(parsed)
}

/// The layouts, nameable objects and per-function tables of the verifying C
/// translation units.
pub(super) fn c_layouts(
    verifying_paths: Vec<String>,
    c_sources: &CSourceContext<'_>,
    target: CTarget,
) -> Result<parser::ProgramLayouts, ClickError> {
    if let ProgramSource::PreparedC {
        imports,
        duplicates,
        ..
    } = &c_sources.source
    {
        if *duplicates {
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
    let mut tables = parser::ProgramLayouts::default();
    for source_path in verifying_paths {
        let unit = parse_c_source_unit(&source_path, c_sources, target)?;
        tables
            .qualified_objects
            .insert(source_path.clone(), unit_qualified_objects(&unit));
        for (name, layout) in &unit.structs {
            if let Some(previous) = tables.struct_layouts.insert(name.clone(), layout.clone())
                && previous != *layout
            {
                return Err(ClickError::new(format!(
                    "conflicting declarations for struct `{name}`"
                )));
            }
        }
        for (name, layout) in &unit.unions {
            if let Some(previous) = tables.union_layouts.insert(name.clone(), layout.clone())
                && previous != *layout
            {
                return Err(ClickError::new(format!(
                    "conflicting declarations for union `{name}`"
                )));
            }
        }
        for function in unit.functions {
            record_function_tables(&mut tables, function);
        }
    }
    Ok(tables)
}

pub(super) fn parse_c_source_unit(
    source_path: &str,
    c_sources: &CSourceContext<'_>,
    target: CTarget,
) -> Result<syntax::C0TranslationUnit, ClickError> {
    if let Some(import) = c_sources.prepared_c_import(source_path)
        && import.target() != target
    {
        return Err(ClickError::new(format!(
            "compiler-prepared C source `{source_path}` targets `{}`, but the sidecar selects `{}`",
            import.target().name(),
            target.name()
        )));
    }
    if let Some(unit) = c_sources.parsed_units.borrow().get(source_path) {
        return Ok((**unit).clone());
    }
    let unit = if let ProgramSource::Bundle(bundle) = &c_sources.source {
        let expanded =
            crate::languages::c::source::expand_includes_for_target(source_path, bundle, target)
                .map_err(|error| {
                    ClickError::new(format!(
                        "failed to resolve includes for C source `{source_path}`: {error}"
                    ))
                })?;
        for header_path in expanded.dependencies() {
            let header = crate::languages::c::source::expand_includes_for_target(
                header_path,
                bundle,
                target,
            )
            .map_err(|error| {
                ClickError::new(format!(
                    "failed to resolve includes for C header `{header_path}`: {error}"
                ))
            })?;
            let header_line_map = header
                .line_map()
                .in_containers(&c_sources.c_source_containers);
            syntax::validate_header(header.source(), &header_line_map).map_err(|error| {
                ClickError::new(format!("failed to parse C header `{header_path}`: {error}"))
                    .with_kind(ClickErrorKind::Syntax)
            })?;
        }
        let line_map = expanded
            .line_map()
            .in_containers(&c_sources.c_source_containers);
        syntax::parse_translation_unit_for_source(expanded.source(), source_path, &line_map)
            .map_err(|error| {
                ClickError::new(format!("failed to parse C source `{source_path}`: {error}"))
                    .with_kind(ClickErrorKind::Syntax)
            })?
    } else {
        #[cfg(test)]
        c_sources
            .prepared_parse_count
            .set(c_sources.prepared_parse_count.get() + 1);
        let import = c_sources.prepared_c_import(source_path).ok_or_else(|| {
                ClickError::new(format!(
                    "import configuration has no prepared translation unit for verifying source `{source_path}`"
                ))
            })?;
        syntax::parse_translation_unit_for_import(
            import.source(),
            import.logical_source(),
            import.source_map(),
            import.promise_attributes(),
        )
        .map_err(|error| {
            ClickError::new(format!(
                "failed to parse compiler-prepared C source `{source_path}`: {error}"
            ))
            .with_kind(ClickErrorKind::Syntax)
        })?
    };
    c_sources
        .parsed_units
        .borrow_mut()
        .insert(source_path.to_string(), Arc::new(unit.clone()));
    Ok(unit)
}

/// The globals and function statics of one translation unit a contract may
/// name: `name`, or `function::name` for a static.
pub(super) fn unit_qualified_objects(
    unit: &syntax::C0TranslationUnit,
) -> BTreeMap<String, parser::QualifiedCObject> {
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
                    pointee_constant: false,
                    source: Default::default(),
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
                    expression: CExpression::Value(CValue::typed_pointer_with_pointee_constant(
                        CMemory::global_pointer(array.kernel_name()),
                        pointer_type.to_kernel_type(),
                        array.is_constant(),
                    )),
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
                    expression: CExpression::Value(CValue::typed_pointer_with_pointee_constant(
                        CMemory::global_pointer(aggregate_array.kernel_name()),
                        CType::Int32Pointer,
                        aggregate_array.is_constant(),
                    )),
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
                        pointee_constant: false,
                        source: Default::default(),
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
                    expression: CExpression::Value(CValue::typed_pointer_with_pointee_constant(
                        CMemory::static_pointer(function.name(), aggregate.kernel_name()),
                        CType::Int32Pointer,
                        aggregate.is_constant(),
                    )),
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
                    expression: CExpression::Value(CValue::typed_pointer_with_pointee_constant(
                        CMemory::static_pointer(function.name(), aggregate_array.kernel_name()),
                        CType::Int32Pointer,
                        aggregate_array.is_constant(),
                    )),
                    address: None,
                    struct_name: Some(aggregate_array.struct_name().to_owned()),
                    array_shape: Some(vec![aggregate_array.length()]),
                    ambiguous: false,
                },
            );
        }
    }
    objects
}

/// Records the objects, array shapes and locals of one C function that its
/// contract may name.
pub(super) fn record_function_tables(
    tables: &mut parser::ProgramLayouts,
    function: syntax::C0Function,
) {
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
    // Automatic struct values are address-backed too. Their C
    // spellings must carry a layout into sidecar field expressions;
    // otherwise `.field` silently falls back to offset zero.
    function_aggregate_objects.extend(function.local_struct_values().clone());
    tables
        .aggregate_objects
        .insert(function.name().to_string(), function_aggregate_objects);
    tables.aggregate_array_objects.insert(
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
    tables
        .global_array_shapes
        .insert(function.name().to_string(), function_global_array_shapes);
    // An automatic local of struct-pointer type is a memory base in
    // this function's contract exactly as a parameter is; the C
    // parser is the only place its struct name exists.
    // A sidecar names a function by its source spelling, and an
    // inline body's kernel name carries an `#inline:<source>` suffix,
    // so keying this by the kernel name hid every inline function's
    // locals and read an eight-byte member as a four-byte one. Two
    // definitions sharing one source spelling leave no layouts rather
    // than guessing between them.
    let locals = parser::FunctionLocals {
        execution_name: Some(function.name().to_string()),
        struct_pointers: function.local_struct_pointers().clone(),
        references: function.local_references().clone(),
    };
    match tables
        .local_struct_pointers
        .entry(function.source_name().to_string())
    {
        std::collections::btree_map::Entry::Vacant(entry) => {
            entry.insert(locals);
        }
        std::collections::btree_map::Entry::Occupied(mut entry) => {
            if entry.get() != &locals {
                entry.insert(parser::FunctionLocals::default());
            }
        }
    }
}

pub(super) fn validate_modeled_pthread_binding(
    units: &BTreeMap<String, syntax::C0TranslationUnit>,
) -> Result<(), ClickError> {
    let header_source = BTreeMap::from([(
        "__click_modeled_pthread_reference.c",
        "#include <pthread.h>\n#include <stdatomic.h>\n",
    )]);
    let reference = crate::languages::c::source::expand_includes_for_target(
        "__click_modeled_pthread_reference.c",
        &header_source,
        CTarget::X86_64LinuxUserspace,
    )
    .map_err(|error| {
        ClickError::new(format!("invalid built-in pthread model: {error}"))
            .with_kind(ClickErrorKind::Internal)
    })?;
    let reference = syntax::parse_translation_unit_for_source(
        reference.source(),
        "__click_modeled_pthread_reference.c",
        reference.line_map(),
    )
    .map_err(|error| {
        ClickError::new(format!("invalid built-in pthread model: {error}"))
            .with_kind(ClickErrorKind::Internal)
    })?;

    let mut found_pthread = BTreeSet::new();
    for (source_path, unit) in units {
        for name in [
            "pthread_create",
            "pthread_join",
            "pthread_mutex_init",
            "pthread_mutex_lock",
            "pthread_mutex_unlock",
            "pthread_mutex_destroy",
        ] {
            if unit.shadowed_pthread_names.contains(name) {
                return Err(ClickError::new(format!(
                    "modeled-pthread binding refuses local shadowing of `{name}` in `{source_path}`"
                )));
            }
            if unit
                .functions
                .iter()
                .any(|function| function.name() == name)
            {
                return Err(ClickError::new(format!(
                    "modeled-pthread binding refuses local definition of `{name}` in `{source_path}`"
                )));
            }
            let Some(declaration) = unit.function_declarations.get(name) else {
                continue;
            };
            if !unit.builtin_pthread_declarations.contains(name) {
                return Err(ClickError::new(format!(
                    "modeled-pthread binding requires `{name}` from Click's built-in `<pthread.h>` in `{source_path}`"
                )));
            }
            let expected = &reference.function_declarations[name];
            if !declaration.compatible_with(expected) {
                return Err(ClickError::new(format!(
                    "modeled-pthread binding found noncanonical `{name}` declaration in `{source_path}`"
                )));
            }
            found_pthread.insert(name);
        }
        // The atomic operations the runtime models are optional, but when a
        // unit names one it is Click's own `<stdatomic.h>` declaration:
        // a program's own function of that name is never modeled.
        for name in [
            crate::languages::c::thread_runtime::ATOMIC_INIT_NAME,
            crate::languages::c::thread_runtime::ATOMIC_STORE_NAME,
            crate::languages::c::thread_runtime::ATOMIC_LOAD_NAME,
        ] {
            if unit
                .functions
                .iter()
                .any(|function| function.name() == name)
            {
                return Err(ClickError::new(format!(
                    "modeled-pthread binding refuses local definition of `{name}` in `{source_path}`"
                )));
            }
            let Some(declaration) = unit.function_declarations.get(name) else {
                continue;
            };
            if !unit.builtin_pthread_declarations.contains(name)
                || !declaration.compatible_with(&reference.function_declarations[name])
            {
                return Err(ClickError::new(format!(
                    "modeled-pthread binding requires `{name}` from Click's built-in `<stdatomic.h>` in `{source_path}`"
                )));
            }
        }
        for function in &unit.functions {
            validate_modeled_pthread_calls(function.body(), source_path)?;
        }
    }
    if found_pthread.len() != 6 {
        return Err(ClickError::new(
            "modeled-pthread binding requires selected `<pthread.h>` declarations",
        ));
    }
    Ok(())
}

/// The source names of the file-scope C objects of every verified translation
/// unit: scalars, arrays, aggregates and aggregate arrays. A bare name in an
/// annotation that no parameter or binding shadows resolves to one of these.
/// A compiler-prepared program has no translation units to list here; its
/// objects are reached through qualified names, which need no list.
pub(super) fn file_scope_object_names(
    click_source: &str,
    c_sources: &CSourceContext<'_>,
    target: CTarget,
) -> Result<BTreeSet<String>, ClickError> {
    let mut names = BTreeSet::new();
    if matches!(c_sources.source, ProgramSource::Program { .. }) {
        return Ok(names);
    }
    for source_path in super::verifying_source_paths(click_source)? {
        // The frontend parsed every verifying unit into the cache, so this
        // shares that unit rather than cloning or parsing it again.
        let cached = c_sources.parsed_units.borrow().get(&source_path).cloned();
        let unit = match cached {
            Some(unit) => unit,
            None => Arc::new(parse_c_source_unit(&source_path, c_sources, target)?),
        };
        names.extend(unit.globals.keys().cloned());
        names.extend(unit.global_arrays.keys().cloned());
        names.extend(unit.global_aggregates.keys().cloned());
        names.extend(unit.global_aggregate_arrays.keys().cloned());
    }
    Ok(names)
}
