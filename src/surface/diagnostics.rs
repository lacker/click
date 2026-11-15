use super::*;
use crate::kernel::MachineBinaryOp;
use crate::kernel::{CompareRelation, MachineIntegerType, OverflowOperation};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    uint32_constant, uint64_constant,
};
use crate::surface::proof_diagnostics::render::{
    render_resource_diagnostic, render_resource_fact_diagnostic, render_resource_facts_diagnostic,
};

pub(in crate::surface) fn describe_proof_obligation_context(
    obligation: &ProofObligation,
) -> Option<String> {
    if let Some(source) = obligation.call_requirement_site()
        && let Some(ordinal) = source.source_requirement_ordinal
    {
        return Some(format!(
            "precondition clause {} of `{}`",
            ordinal + 1,
            source.callee
        ));
    }
    obligation.context().map(str::to_owned)
}
use crate::kernel::ExecutionFactSource;
use crate::kernel::SharedMemory;
use crate::kernel::resource_tracker;
use crate::kernel::{
    ComparisonOperator as KernelComparisonOperator, FloatCondition, UpdateOperator,
};
use crate::surface::validation::describe_click_type;

mod cpp_model;
mod object_fields;
mod rust_spelling;
use cpp_model::describe_model_accessor;
pub(in crate::surface) use cpp_model::{CapturedModelAccessors, ModelAccessorScope};
pub(crate) use object_fields::{clear_ambient_object_fields, enter_ambient_object_fields};
use rust_spelling::rust_scalar_spelling;
pub(crate) use rust_spelling::{
    LoopPhaseSpelling, enter_rust_spelling, record_pure_function_slices, rust_spelling,
    rust_variable_spelling, slice_call_arguments, slice_call_spelling, slice_type_spelling,
    subslice_of_length, subslice_spelling,
};

const MAX_DIAGNOSTIC_ITEMS: usize = 12;
const TRUNCATION_SUFFIX: &str =
    "\n… <diagnostic truncated; set CLICK_FULL_DIAGNOSTICS=1 for full internal state>";

thread_local! {
    /// Where each C statement being stepped was written, innermost last; see
    /// [`StatementSiteScope`].
    static C_STATEMENT_SITES: std::cell::RefCell<
        Vec<Option<std::sync::Arc<crate::languages::c::syntax::CStatementSite>>>,
    > = const { std::cell::RefCell::new(Vec::new()) };
}

/// While alive, names the C statement a step is checking, so a refusal that
/// prints its C operation also names the line it was written on and quotes
/// it. Diagnostics only: nothing a check decides reads it, and a refusal
/// built outside any scope (or for a statement with no recorded site) simply
/// prints no location.
#[must_use]
pub(in crate::surface) struct StatementSiteScope(());

impl StatementSiteScope {
    /// Enters the site the source layout records for `statement_index`.
    pub(in crate::surface) fn enter(
        layout: &crate::surface::lowering::SourceExecutionLayout,
        statement_index: usize,
        function: &crate::languages::interface::ImportedFunction,
    ) -> Self {
        let site = layout.site(statement_index).cloned();
        C_STATEMENT_SITES.with(|sites| sites.borrow_mut().push(site));
        let places = layout.diagnostic_places(|| StatementPlaces::of(function));
        REFERENCE_CARRIERS.with(|carriers| {
            carriers.borrow_mut().push(PlaceScope {
                carriers: places.carriers.clone(),
                structs: places.structs.clone(),
                ..PlaceScope::default()
            })
        });
        Self(())
    }
}

impl Drop for StatementSiteScope {
    fn drop(&mut self) {
        C_STATEMENT_SITES.with(|sites| {
            sites.borrow_mut().pop();
        });
        REFERENCE_CARRIERS.with(|carriers| {
            carriers.borrow_mut().pop();
        });
    }
}

/// What a parameter's pointer points at, for printing a read through it as
/// the sidecar writes it.
#[derive(Clone, Debug)]
enum PointeeShape {
    /// `int32& value`: a read of the carrier is `value`.
    ScalarReferent,
    /// A struct: a read at a scalar field's offset is that field, `c.field`
    /// through a reference and `p->field` through a pointer.
    Struct {
        fields: Vec<crate::surface::FieldPlace>,
    },
}

/// What one scope lets the printer name.
#[derive(Default)]
struct PlaceScope {
    // The selected function's input identity, independent of the order in
    // which other functions were verified.
    input_scope: Option<u64>,
    struct_pointer_parameters: Vec<Option<String>>,
    /// The parameters whose reads are printed as places, by the name each
    /// has in a kernel term.
    carriers: std::sync::Arc<BTreeMap<String, PointeeShape>>,
    /// The fields of each struct a pointer field reaches, by struct name, so
    /// a read through a loaded pointer is a place too.
    structs: std::sync::Arc<BTreeMap<String, Vec<crate::surface::FieldPlace>>>,
    /// An expansion scope's function: whether its signature is written in
    /// Rust syntax, and its slice parameters (`enter_rust_spelling`).
    rust_spelling: Option<Option<std::rc::Rc<[String]>>>,
}

thread_local! {
    /// The printer of a kernel term has no parameter list; a step scope or
    /// an expansion scope supplies the innermost of these.
    static REFERENCE_CARRIERS: std::cell::RefCell<Vec<PlaceScope>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// The places a step's refusal names reads by: the function's reference
/// parameters, its struct pointer parameters and locals, and the fields of
/// each struct a pointer field reaches. Built once per function.
pub(in crate::surface) struct StatementPlaces {
    carriers: std::sync::Arc<BTreeMap<String, PointeeShape>>,
    structs: std::sync::Arc<BTreeMap<String, Vec<crate::surface::FieldPlace>>>,
}

impl StatementPlaces {
    fn of(function: &crate::languages::interface::ImportedFunction) -> Self {
        let layouts = function.structs();
        let fields_of = |struct_name: &str| {
            layouts
                .get(struct_name)
                .map(|layout| crate::surface::scalar_field_places(layout, layouts))
        };
        let mut carriers = reference_carriers(function);
        for parameter in function.parameters() {
            if let Some(struct_name) = parameter.struct_name()
                && parameter.interface_type().is_pointer()
                && !carriers.contains_key(parameter.name())
                && let Some(fields) = parameter
                    .pointee_struct_layout()
                    .map(|layout| crate::surface::scalar_field_places(layout, layouts))
                    .or_else(|| fields_of(struct_name))
            {
                carriers.insert(
                    parameter.name().to_string(),
                    PointeeShape::Struct { fields },
                );
            }
        }
        for (local, struct_name) in function.local_struct_pointers() {
            if !carriers.contains_key(local)
                && let Some(fields) = fields_of(struct_name)
            {
                carriers.insert(local.clone(), PointeeShape::Struct { fields });
            }
        }
        let structs = layouts
            .keys()
            .filter_map(|name| Some((name.clone(), fields_of(name)?)))
            .collect();
        Self {
            carriers: std::sync::Arc::new(carriers),
            structs: std::sync::Arc::new(structs),
        }
    }
}

fn reference_carriers(
    function: &crate::languages::interface::ImportedFunction,
) -> BTreeMap<String, PointeeShape> {
    function
        .parameters()
        .iter()
        .filter(|parameter| syntax::referent_of_carrier(parameter.name()).is_some())
        .map(|parameter| {
            let shape = match parameter.struct_name() {
                None => PointeeShape::ScalarReferent,
                Some(struct_name) => PointeeShape::Struct {
                    fields: parameter
                        .pointee_struct_layout()
                        .or_else(|| function.structs().get(struct_name))
                        .map(|layout| {
                            crate::surface::scalar_field_places(layout, function.structs())
                        })
                        .unwrap_or_default(),
                },
            };
            (parameter.name().to_string(), shape)
        })
        .collect()
}

/// While alive, names the reference and struct parameters of the function
/// whose proof text is being written, so `click expand` spells a read
/// through one as the sidecar does.
#[must_use]
pub(in crate::surface) struct ParameterPlaceScope(());

impl ParameterPlaceScope {
    pub(in crate::surface) fn enter(block: &crate::surface::FunctionBlock) -> Self {
        let parameters = block.signature().parameters();
        // The name a parameter or local has in a kernel term: a reference
        // is carried by a pointer named for its address.
        let variable = |name: &str| {
            let reference = parameters
                .iter()
                .any(|parameter| parameter.name() == name && parameter.is_reference());
            if reference && syntax::referent_of_carrier(name).is_none() {
                syntax::reference_carrier_name(name)
            } else {
                name.to_string()
            }
        };
        let mut shapes: BTreeMap<_, _> = parameters
            .iter()
            .filter(|parameter| parameter.is_reference() && parameter.struct_name().is_none())
            .map(|parameter| (variable(parameter.name()), PointeeShape::ScalarReferent))
            .collect();
        for (name, fields) in block.parameter_field_places() {
            shapes.insert(
                variable(name),
                PointeeShape::Struct {
                    fields: fields.clone(),
                },
            );
        }
        REFERENCE_CARRIERS.with(|scopes| {
            scopes.borrow_mut().push(PlaceScope {
                input_scope: Some(lowering::input_scope(block.signature().name())),
                struct_pointer_parameters: parameters.iter().map(|parameter| {
                    (parameter.struct_name().is_some()
                        && !parameter.is_reference()
                        && matches!(parameter.click_type(), ClickType::Program(interface_type) if interface_type.is_pointer()))
                        .then(|| parameter.name().to_string())
                }).collect(),
                carriers: std::sync::Arc::new(shapes),
                structs: std::sync::Arc::new(block.pointee_field_places().clone()),
                rust_spelling: Some(
                    block
                        .signature()
                        .rust_slice_parameters()
                        .map(std::rc::Rc::<[String]>::from),
                ),
            })
        });
        Self(())
    }
}

fn input_struct_pointer_place(base: &ContractExpression) -> Option<String> {
    let ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::Pointer(
        pointer,
    ))) = base
    else {
        return None;
    };
    REFERENCE_CARRIERS.with(|scopes| {
        let scopes = scopes.borrow();
        let scope = scopes.last()?;
        let index = lowering::input_pointer_parameter(scope.input_scope?, pointer)?;
        let name = scope.struct_pointer_parameters.get(index)?.as_ref()?;
        // This is the universal input, even if the parameter was reassigned.
        Some(format!("at(function.entry, {name})"))
    })
}

impl Drop for ParameterPlaceScope {
    fn drop(&mut self) {
        REFERENCE_CARRIERS.with(|scopes| {
            scopes.borrow_mut().pop();
        });
    }
}

/// A pointer expression with the constant byte offsets added to it
/// stripped: a field of a nested struct is one offset inside another.
/// A member's subobject narrowing moves no address, so it is stripped too.
fn strip_byte_offsets(mut pointer: &ProgramExpression) -> Option<(&ProgramExpression, u32)> {
    let mut offset_bytes = 0u32;
    loop {
        match pointer {
            ProgramExpression::PointerOffsetBytes {
                pointer: base,
                bytes,
            } => {
                offset_bytes = offset_bytes.checked_add(*bytes)?;
                pointer = base;
            }
            ProgramExpression::Subobject { pointer: base, .. } => pointer = base,
            _ => return Some((pointer, offset_bytes)),
        }
    }
}

/// The field a typed read at `offset_bytes` into a struct with `fields`
/// finds.
fn field_at(
    fields: &[crate::surface::FieldPlace],
    offset_bytes: u32,
    value_type: ProgramType,
    pointee_constant: bool,
) -> Option<&crate::surface::FieldPlace> {
    fields.iter().find(|field| {
        field.array.is_none()
            && field.offset_bytes == offset_bytes
            && field.value_type == value_type
            && field.pointee_constant == pointee_constant
    })
}

/// The place a typed read at `offset_bytes` names: a scalar field, or an
/// element `field[k]` of an array field.
fn field_place_at(
    fields: &[crate::surface::FieldPlace],
    offset_bytes: u32,
    value_type: ProgramType,
    pointee_constant: bool,
) -> Option<String> {
    if let Some(field) = field_at(fields, offset_bytes, value_type, pointee_constant) {
        return Some(field.name.clone());
    }
    fields.iter().find_map(|field| {
        let (width, length) = field.array?;
        // The whole array, read as an array, is the field itself.
        let whole = match field.value_type {
            ProgramType::Int32 => ProgramType::Int32Array(length),
            ProgramType::UInt32 => ProgramType::UInt32Array(length),
            ProgramType::UInt8 => ProgramType::UInt8Array(length),
            _ => return None,
        };
        if offset_bytes == field.offset_bytes && value_type == whole {
            return Some(field.name.clone());
        }
        let within = offset_bytes.checked_sub(field.offset_bytes)?;
        (field.value_type == value_type
            && !pointee_constant
            && within % width == 0
            && within / width < length)
            .then(|| format!("{}[{}]", field.name, within / width))
    })
}

/// A pointer to a struct the scope can name the fields of, as the sidecar
/// writes it, with those fields: a struct parameter or local `p`, or a
/// pointer loaded from a field of one, `p->next`, to any depth.
fn struct_pointer_place<'a>(
    pointer: &ProgramExpression,
    scope: &'a PlaceScope,
) -> Option<(String, &'a [crate::surface::FieldPlace])> {
    match pointer {
        ProgramExpression::Variable(variable) => match scope.carriers.get(variable)? {
            PointeeShape::Struct { fields } => Some((variable.clone(), fields)),
            PointeeShape::ScalarReferent => None,
        },
        ProgramExpression::TypedLoad {
            pointer,
            value_type,
            volatile: false,
            pointee_constant,
            ..
        } => {
            let (base, offset_bytes) = strip_byte_offsets(pointer)?;
            let (base, fields) = struct_pointer_place(base, scope)?;
            let field = field_at(fields, offset_bytes, *value_type, *pointee_constant)?;
            let fields = scope.structs.get(field.pointee_struct.as_ref()?)?;
            Some((describe_field_place(&base, &field.name), fields))
        }
        _ => None,
    }
}

/// A typed read through `pointer`, as a sidecar writes it, when `pointer`
/// is a parameter the innermost scope names, a field's offset from one, or
/// a field's offset from a struct pointer loaded through one.
fn describe_read_through_parameter(
    pointer: &ProgramExpression,
    value_type: ProgramType,
    pointee_constant: bool,
) -> Option<String> {
    let (base, offset_bytes) = strip_byte_offsets(pointer)?;
    REFERENCE_CARRIERS.with(|scopes| {
        let scopes = scopes.borrow();
        let scope = scopes.last()?;
        if let ProgramExpression::Variable(variable) = base
            && let Some(PointeeShape::ScalarReferent) = scope.carriers.get(variable)
        {
            return (offset_bytes == 0)
                .then(|| syntax::referent_of_carrier(variable).map(str::to_string))
                .flatten();
        }
        let (base, fields) = struct_pointer_place(base, scope)?;
        let field = field_place_at(fields, offset_bytes, value_type, pointee_constant)?;
        // A standard-library model's field prints as its accessor.
        let (path, index) = field
            .split_once('[')
            .map_or((field.as_str(), ""), |(path, _)| {
                (path, &field[path.len()..])
            });
        let root = object_at_address(&base).map_or(base.clone(), str::to_string);
        if let Some(accessor) = cpp_model::describe_model_field_place(&root, path) {
            return Some(format!("{accessor}{index}"));
        }
        Some(describe_field_place(&base, &field))
    })
}

/// The line naming where the C statement being stepped was written, as
/// "\n  C statement at f.c:6:9: `items[i] = 7;`", or nothing when no step
/// scope records one. It follows a refusal's "C operation" line, which
/// spells the checked kernel operation; this line is the source a person
/// edits.
pub(in crate::surface) fn describe_execution_statement_site() -> String {
    C_STATEMENT_SITES.with(|sites| {
        sites
            .borrow()
            .last()
            .and_then(Option::as_ref)
            .map(|site| format!("\n  C statement at {}: `{}`", site.location(), site.text()))
            .unwrap_or_default()
    })
}

pub(super) fn bound_error_message(message: String) -> String {
    bound_error_message_for_mode(message, std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some())
}

pub(super) fn bound_error_message_for_mode(message: String, full_internal_state: bool) -> String {
    if full_internal_state || message.len() <= DEFAULT_DIAGNOSTIC_BYTE_LIMIT {
        return message;
    }
    truncate_utf8_with_suffix(&message, DEFAULT_DIAGNOSTIC_BYTE_LIMIT, TRUNCATION_SUFFIX)
}

fn truncate_utf8_with_suffix(message: &str, limit: usize, suffix: &str) -> String {
    if message.len() <= limit {
        return message.to_string();
    }
    let content_limit = limit.saturating_sub(suffix.len());
    let mut boundary = content_limit.min(message.len());
    while !message.is_char_boundary(boundary) {
        boundary -= 1;
    }
    let mut bounded = String::with_capacity(boundary + suffix.len());
    bounded.push_str(&message[..boundary]);
    bounded.push_str(suffix);
    bounded
}

fn compact_unspelled_facts(entries: &mut Vec<String>) {
    let mut omitted = 0;
    entries.retain(|entry| {
        if entry == "fact has no exact Click spelling at this frontier" {
            omitted += 1;
            false
        } else {
            true
        }
    });
    if omitted > 0 {
        entries.push(format!(
            "{omitted} fact(s) have no exact Click spelling at this frontier"
        ));
    }
}

pub(in crate::surface) fn describe_bounded_list<T>(
    items: &[T],
    mut describe: impl FnMut(&T) -> String,
) -> String {
    if items.is_empty() {
        return "[]".to_string();
    }
    let item_limit = diagnostic_item_limit();
    let mut entries = items
        .iter()
        .take(item_limit)
        .map(&mut describe)
        .collect::<Vec<_>>();
    compact_unspelled_facts(&mut entries);
    if items.len() > item_limit {
        entries.push(format!("… {} more omitted", items.len() - item_limit));
    }
    format!("[{}]", entries.join(", "))
}

pub(super) fn diagnostic_item_limit() -> usize {
    if std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some() {
        usize::MAX
    } else {
        MAX_DIAGNOSTIC_ITEMS
    }
}

fn describe_context_pure_and_execution_facts(
    pure_facts: &[Proposition],
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
    parameter_binding: ParameterBinding<'_>,
) -> String {
    describe_context_facts_with_result(pure_facts, execution_pure_facts, parameter_binding, None)
}

fn describe_context_facts_with_result(
    pure_facts: &[Proposition],
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
    parameter_binding: ParameterBinding<'_>,
    result: Option<&ProgramValue>,
) -> String {
    let mut labels =
        crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(parameter_binding);
    if let Some(result) = result {
        labels.source_value_type(result);
    }
    let text = describe_context_facts_labeled(pure_facts, execution_pure_facts, &mut labels);
    format!("{text}{}", labels.trace_legend())
}

fn describe_context_facts_labeled(
    pure_facts: &[Proposition],
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
    labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels,
) -> String {
    let item_limit = diagnostic_item_limit();
    let mut total = 0;
    let mut entries = Vec::new();
    for fact in pure_facts.iter().chain(
        execution_pure_facts
            .fact_iter()
            .map(ExecutionPureFact::proposition),
    ) {
        // Kernel authority, such as internal bounds evidence, has no
        // authored proof syntax. Keep the context's existing source facts
        // visible beside the actual refusal.
        if fact.is_kernel_authority() {
            continue;
        }
        total += 1;
        if entries.len() < item_limit {
            entries.push(
                crate::surface::proof_diagnostics::render::render_proposition_labeled(fact, labels),
            );
        }
    }
    compact_unspelled_facts(&mut entries);
    if total > item_limit {
        entries.push(format!("… {} more omitted", total - item_limit));
    }
    format!("[{}]", entries.join(", "))
}

/// The bounded spelling of a fact list against the current function's
/// parameters: a diagnostic that reports several fact lists (the condition
/// paths of an undecided C `if`, for one) must not print a kernel debug dump
/// of every memory state those facts read.
pub(super) fn describe_pure_facts_for_diagnostic(
    pure_facts: &[Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    if pure_facts.is_empty() {
        return "[]".to_string();
    }
    let mut labels =
        crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(parameter_binding);
    let text = describe_bounded_list(pure_facts, |fact| {
        crate::surface::proof_diagnostics::render::render_proposition_labeled(fact, &mut labels)
    });
    format!("{text}{}", labels.trace_legend())
}

pub(super) fn describe_pure_facts(pure_facts: &[Proposition]) -> String {
    if pure_facts.is_empty() {
        return "[]".to_string();
    }

    describe_pure_facts_for_diagnostic(pure_facts, ParameterBinding::default())
}

/// Describes one fact, and for a refused concrete named-contract formation
/// appends the explicit refinement theorem the user has to write.
///
/// The skeleton itself comes from the kernel, built from the two declarations
/// the formation check read.
pub(super) fn describe_pure_fact_with_environment(
    fact: &Proposition,
    parameter_binding: ParameterBinding<'_>,
    environment: &crate::kernel::ExecutionEnvironment,
    predicate_environment: Option<&PredicateEnvironment>,
) -> String {
    let description = describe_pure_fact(fact, parameter_binding);
    let Some((contract, target)) = concrete_named_contract_fact(fact) else {
        return description;
    };
    let Some(skeleton) = crate::kernel::program_named_contract_refinement_theorem_skeleton(
        environment,
        contract,
        target,
        &declared_contract_parameter_spellings(predicate_environment, contract),
    ) else {
        return description;
    };
    // A Rust sidecar names a crate function as a value by its path, and the
    // theorem by the function's own name.
    let skeleton = match crate::languages::rust::names::rust_display_name(target) {
        Some(path) => {
            let own = path.rsplit("::").next().unwrap_or(&path).to_string();
            skeleton
                .replace(&format!("&{target}"), &path)
                .replace(&format!("{target}_is_"), &format!("{own}_is_"))
        }
        None => skeleton,
    };
    format!(
        "function `{target}` does not satisfy named contract `{contract}` automatically;\nprove it explicitly:\n{skeleton}"
    )
}

/// The C spelling each of a named contract's parameters has in its source
/// declaration, for the positions the kernel cannot spell on its own.
///
/// The kernel models an aggregate pointer as a layout and keeps no struct
/// tag, so it prints `struct node*` as the pointer type it is modeled by. The
/// declaration that names the struct is right here on the surface, and this
/// is where the skeleton is rendered, so recover the tag from it rather than
/// teaching the kernel about tags. Every other position is left empty and
/// keeps the kernel's spelling.
fn declared_contract_parameter_spellings(
    predicate_environment: Option<&PredicateEnvironment>,
    contract: &str,
) -> Vec<Option<String>> {
    let Some(definition) =
        predicate_environment.and_then(|environment| environment.contract_definition(contract))
    else {
        return Vec::new();
    };
    definition
        .function_block()
        .signature()
        .parameters()
        .iter()
        .map(|parameter| {
            let name = parameter.struct_name()?;
            // A struct-valued parameter is modeled as a byte array; every
            // other tagged parameter is a pointer to the struct.
            let base = if matches!(
                parameter.click_type(),
                ClickType::Program(InterfaceType::UInt8Array(_))
            ) {
                format!("struct {name}")
            } else {
                format!("struct {name}*")
            };
            Some(if parameter.pointee_is_constant() {
                format!("const {base}")
            } else {
                base
            })
        })
        .collect()
}

/// The contract and concrete target of a named-contract fact over an exact
/// function address, which is the shape automatic formation refuses and the
/// shape a missing-fact report has to explain rather than blame.
pub(super) fn concrete_named_contract_fact(fact: &Proposition) -> Option<(&str, &str)> {
    let Proposition::Predicate { name, arguments } = fact else {
        return None;
    };
    let contract = crate::kernel::FunctionContract::surface_name_from_predicate(name)?;
    let [_, Term::ProgramValue(ProgramValue::Pointer(pointer))] = arguments.as_slice() else {
        return None;
    };
    let Pointer {
        block: PointerBlock::Function(target),
        offset: PointerOffsetTerm::Constant(0),
    } = pointer.pointer()
    else {
        return None;
    };
    Some((contract, target))
}

/// A lowering's value environment as the parameter/argument tables surface
/// reconstruction reads.
///
/// This is the only way a kernel variable becomes `hi` in a message, so every
/// diagnostic that holds a value environment and prints a lowered term goes
/// through it rather than showing `v2`. One definition, so a pure theorem and a
/// C proof name the same term the same way.
pub(in crate::surface) fn value_naming_tables(
    values: &std::collections::BTreeMap<String, ProgramValue>,
) -> (
    Vec<crate::languages::interface::ImportedParameter>,
    Vec<ProgramExpression>,
) {
    let mut parameters = Vec::with_capacity(values.len());
    let mut arguments = Vec::with_capacity(values.len());
    for (name, value) in values {
        parameters.push(crate::languages::interface::ImportedParameter::new(
            crate::surface::generics::interface_type_from_program_type(value.program_type()),
            name.clone(),
            None,
        ));
        arguments.push(ProgramExpression::Value(value.numeric_value().clone()));
    }
    (parameters, arguments)
}

/// The kind of comparison or check a kernel condition makes, for a
/// diagnostic that has no source spelling of its operands.
pub(super) fn condition_kind(condition: &ConditionTerm) -> &'static str {
    match condition {
        ConditionTerm::PointerValueEqual(_, _) => "pointer value equality",

        ConditionTerm::AlgebraicEqual(_, _) => "algebraic equality",
        ConditionTerm::IntegerLessThan(_, _) => "Integer less-than",
        ConditionTerm::IntegerLessEqual(_, _) => "Integer less-or-equal",
        ConditionTerm::IntegerGreaterThan(_, _) => "Integer greater-than",
        ConditionTerm::IntegerGreaterEqual(_, _) => "Integer greater-or-equal",
        ConditionTerm::IntegerEqual(_, _) => "Integer equality",
        ConditionTerm::IntegerNotEqual(_, _) => "Integer disequality",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: _,
            right: _,
        } => "signed less-than",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: _,
            right: _,
        } => "signed less-or-equal",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left: _,
            right: _,
        } => "signed greater-than",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: _,
            right: _,
        } => "signed greater-or-equal",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left: _,
            right: _,
        } => "int32 equality",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left: _,
            right: _,
        } => "addition overflow",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Subtract,
            left: _,
            right: _,
        } => "subtraction overflow",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Multiply,
            left: _,
            right: _,
        } => "multiplication overflow",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Divide,
            left: _,
            right: _,
        } => "division overflow",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::ShiftLeft,
            left: _,
            right: _,
        } => "left-shift overflow",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::LessThan,
            left: _,
            right: _,
        } => "int64 signed less-than",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::LessEqual,
            left: _,
            right: _,
        } => "int64 signed less-or-equal",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::GreaterThan,
            left: _,
            right: _,
        } => "int64 signed greater-than",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::GreaterEqual,
            left: _,
            right: _,
        } => "int64 signed greater-or-equal",
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left: _,
            right: _,
        } => "uint64 less-than",
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessEqual,
            left: _,
            right: _,
        } => "uint64 less-or-equal",
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterThan,
            left: _,
            right: _,
        } => "uint64 greater-than",
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterEqual,
            left: _,
            right: _,
        } => "uint64 greater-or-equal",
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::LessThan,
            left: _,
            right: _,
        } => "uint32 less-than",
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::LessEqual,
            left: _,
            right: _,
        } => "uint32 less-or-equal",
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::GreaterThan,
            left: _,
            right: _,
        } => "uint32 greater-than",
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt32,
            relation: CompareRelation::GreaterEqual,
            left: _,
            right: _,
        } => "uint32 greater-or-equal",
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left: _,
            right: _,
        } => "64-bit equality",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Add,
            left: _,
            right: _,
        } => "int64 addition overflow",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Subtract,
            left: _,
            right: _,
        } => "int64 subtraction overflow",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Multiply,
            left: _,
            right: _,
        } => "int64 multiplication overflow",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Divide,
            left: _,
            right: _,
        } => "int64 division overflow",
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::ShiftLeft,
            left: _,
            right: _,
        } => "int64 left-shift overflow",
        ConditionTerm::Compare { .. } => "machine comparison",
        ConditionTerm::Overflows { .. } => "machine overflow test",
        ConditionTerm::Float32(FloatCondition::Comparison { .. }) => "float32 comparison",
        ConditionTerm::Float32(FloatCondition::Classification { .. }) => "float32 classification",
        ConditionTerm::Float64(FloatCondition::Comparison { .. }) => "float64 comparison",
        ConditionTerm::Float64(FloatCondition::Classification { .. }) => "float64 classification",
        ConditionTerm::PointerOffsetEqual(_, _) => "pointer-offset equality",
        ConditionTerm::PointerEqual(_, _) => "pointer equality",
        ConditionTerm::Constant(_) => "constant condition",
        ConditionTerm::Variable(_) => "condition variable",
        ConditionTerm::BoolApplication(_) => "Bool function application",
        ConditionTerm::BoolIf { .. } => "Bool conditional",
        ConditionTerm::BoolEqual(..) => "Bool equality",
        ConditionTerm::BoolLoad(..) => "bool read",
    }
}

/// A fact's shape with every memory label fresh: two facts that differ only
/// in which states their reads name compare equal.
pub(super) fn pure_fact_shape(
    fact: &Proposition,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
    describe_pure_fact(fact, parameter_binding)
}

pub(super) fn describe_pure_fact(
    fact: &Proposition,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let mut labels =
        crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(parameter_binding);
    let mut text =
        crate::surface::proof_diagnostics::render::render_proposition_labeled(fact, &mut labels);
    text.push_str(&labels.trace_legend());
    text
}

pub(super) fn describe_execution_pure_facts(facts: &(impl ExecutionFactSource + ?Sized)) -> String {
    describe_context_pure_and_execution_facts(&[], facts, ParameterBinding::default())
}

pub(super) fn describe_available_facts(
    pure_facts: &[Proposition],
    resource_facts: &[ResourceFact],
    parameter_binding: ParameterBinding<'_>,
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
) -> String {
    format!(
        "available pure facts: {}\n  available resource facts: {}",
        describe_context_pure_and_execution_facts(
            pure_facts,
            execution_pure_facts,
            parameter_binding
        ),
        render_resource_facts_diagnostic(resource_facts, parameter_binding)
    )
}

/// Describes a fact a proof needs and does not have.
///
/// For a missing named-contract fact, also name the routes that establish it.
pub(super) fn describe_required_pure_fact(
    required: &Proposition,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    match concrete_named_contract_fact(required) {
        Some((contract, target)) => format!(
            "no `{contract}(&{target})` fact is available; apply a refinement theorem or pass `&{target}` where `{contract}` is required"
        ),
        None => describe_pure_fact(required, parameter_binding),
    }
}

pub(super) fn describe_missing_pure_fact(
    required: &Proposition,
    pure_facts: &[Proposition],
    resource_facts: &[ResourceFact],
    parameter_binding: ParameterBinding<'_>,
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
) -> String {
    let mut labels =
        crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(parameter_binding);
    let requirement = if concrete_named_contract_fact(required).is_some() {
        describe_required_pure_fact(required, parameter_binding)
    } else {
        crate::surface::proof_diagnostics::render::render_proposition_labeled(required, &mut labels)
    };
    describe_missing_fact_context(
        &requirement,
        pure_facts,
        resource_facts,
        execution_pure_facts,
        &mut labels,
    )
}

fn describe_missing_fact_context(
    requirement: &str,
    pure_facts: &[Proposition],
    resource_facts: &[ResourceFact],
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
    labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels,
) -> String {
    let available = describe_context_facts_labeled(pure_facts, execution_pure_facts, labels);
    let resources = crate::surface::proof_diagnostics::render::render_resource_facts_labeled(
        resource_facts,
        labels,
    );
    format!(
        "missing pure fact: {requirement}\n  available pure facts: {available}\n  available resource facts: {resources}{}",
        labels.trace_legend()
    )
}

pub(super) fn describe_missing_resource_fact(
    required: &ResourceFact,
    pure_facts: &[Proposition],
    resource_facts: &[ResourceFact],
    parameter_binding: ParameterBinding<'_>,
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
) -> String {
    let mut note = String::new();
    if let Resource::Iterated(required_iterated) = required.resource()
        && let Some(held) = resource_facts
            .iter()
            .find_map(|fact| match fact.resource() {
                Resource::Iterated(held)
                    if held.owner() == required_iterated.owner() && !held.holes().is_empty() =>
                {
                    Some(held)
                }
                _ => None,
            })
    {
        note = format!(
            "\n  note: the held iterated ownership of `{}` has index {} taken out, and at a fold it must hold exactly the elements whose guard is true; `give` each element back, or store a guard value that makes its guard false, before folding",
            held.owner(),
            held.holes()
                .iter()
                .map(|hole| format!(
                    "`{}`",
                    describe_bitvector_with_context(hole, parameter_binding)
                ))
                .collect::<Vec<_>>()
                .join(", ")
        );
    }
    format!(
        "missing resource fact `{}`{note}\n  {}",
        render_resource_fact_diagnostic(required, parameter_binding),
        describe_available_facts(
            pure_facts,
            resource_facts,
            parameter_binding,
            execution_pure_facts
        )
    )
}

/// The conditions that tell several statement successors apart.
///
/// A refusal that only says "got 2" leaves the reader to guess which `if`
/// inside an inlined helper is undecided. Each successor's own path facts name
/// the branch it took, so reporting the facts that are *not* common to every
/// successor names the undecided condition and its polarity, bounded by the
/// same item limit as every other fact list.
pub(super) fn describe_undecided_statement_successors(
    transitions: &[crate::surface::CertifiedStatementTransition],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let item_limit = diagnostic_item_limit();
    let mut lines = Vec::new();
    for (index, transition) in transitions.iter().take(item_limit).enumerate() {
        let distinguishing = transition
            .path_facts
            .iter()
            .filter(|fact| {
                !transitions
                    .iter()
                    .all(|other| other.path_facts.contains(fact))
            })
            .take(item_limit)
            .map(|fact| format!("`{}`", describe_stated_fact(fact, parameter_binding)))
            .collect::<Vec<_>>();
        if distinguishing.is_empty() {
            continue;
        }
        lines.push(format!(
            "  successor {}: {}",
            index + 1,
            distinguishing.join(", ")
        ));
    }
    if lines.is_empty() {
        return String::new();
    }
    format!("undecided condition:\n{}\n", lines.join("\n"))
}

/// `outcomes` splits a call into its returning and its throwing edge, so it
/// is offered only where the two successors are exactly those: `one_throws`
/// says one of them is a `Throw`. Two successors that both continue are an
/// undecided branch inside an inlined callee, which the case-split guidance
/// above already answers; `outcomes` has no arm for either of them.
pub(super) fn describe_multiple_statement_successors_guidance(
    statement: &ProgramStatement,
    successor_count: usize,
    one_throws: bool,
) -> String {
    if successor_count != 2
        || !one_throws
        || !matches!(
            statement,
            ProgramStatement::Call { .. }
                | ProgramStatement::CallConstruct { .. }
                | ProgramStatement::CallResult { .. }
        )
    {
        return String::new();
    }
    r#"
`step()` cannot choose between the two successors of this call. Use `outcomes` at this point:
outcomes {
    returned => { step(); }
    threw => { step(); }
}
The `step()` in each arm advances the selected path; add the remaining
`step()`, `step_until(function.exit)`, and `solve()` tactics inside that arm until all
contract claims are closed.
"#
    .to_string()
}

/// The pure facts relevant to `goal`: those sharing a variable or structural read with it,
/// directly or through a chain of facts that share these atoms (`i <= j` and
/// `j < 1000` both bear on a goal about `i`), in their original order. A
/// conjunction is listed as its conjuncts, each judged on its own, so a
/// `requires` that joins a relevant bound with an unrelated one lists the
/// bound alone and spells it as the condition it is.
///
/// A fact over none of the goal's atoms cannot have been the missing
/// premise of a closure that failed on it, so listing it only pushes the
/// relevant ones past the item limit. The walk is over a atom-to-fact
/// index, so it reads each fact's atoms once.
pub(super) fn pure_facts_relevant_to(
    goal: &Proposition,
    facts: &[Proposition],
) -> Vec<Proposition> {
    use std::collections::{BTreeMap, BTreeSet};
    let atoms_of = |proposition: &Proposition| {
        let mut collector =
            crate::kernel::proof::term_rewrite::IntegerSubstitutionVariableCollector::uncharged();
        collector.collect_read_terms();
        collector.collect(proposition);
        let mut variables = BTreeSet::new();
        collector.extend_into(&mut variables);
        variables
            .into_iter()
            .map(MachineTerm::Variable)
            .chain(collector.take_read_terms())
            .collect::<BTreeSet<_>>()
    };
    let mut conjuncts = Vec::new();
    let mut pending_facts = facts.iter().rev().collect::<Vec<_>>();
    while let Some(fact) = pending_facts.pop() {
        match fact {
            Proposition::And(left, right) => {
                pending_facts.push(right);
                pending_facts.push(left);
            }
            other => conjuncts.push(other),
        }
    }
    let facts = conjuncts;
    let fact_atoms = facts.iter().map(|fact| atoms_of(fact)).collect::<Vec<_>>();
    let mut facts_by_atom = BTreeMap::<MachineTerm, Vec<usize>>::new();
    for (index, variables) in fact_atoms.iter().enumerate() {
        for variable in variables {
            facts_by_atom
                .entry(variable.clone())
                .or_default()
                .push(index);
        }
    }
    let mut reached = atoms_of(goal);
    let mut pending = reached.iter().cloned().collect::<Vec<_>>();
    let mut included = BTreeSet::new();
    while let Some(variable) = pending.pop() {
        for index in facts_by_atom.get(&variable).into_iter().flatten() {
            if included.insert(*index) {
                for next in &fact_atoms[*index] {
                    if reached.insert(next.clone()) {
                        pending.push(next.clone());
                    }
                }
            }
        }
    }
    included
        .into_iter()
        .map(|index| facts[index].clone())
        .collect()
}

/// The header of the proof context an unclosed goal lists: the path's case
/// and the facts bearing on that goal (`pure_facts_relevant_to`). Unlike the whole-context
/// `proof context:` other refusals carry, the command line shows it.
pub(crate) const GOAL_PROOF_CONTEXT_HEADER: &str = "proof context for the goal:";

/// The proof context of an unclosed goal: the case this path is (`case_facts`,
/// the conditions its branches and case splits assumed), the pure facts
/// bearing on `goal` (every fact when the goal has no kernel form), and the
/// held resources, each list bounded by the diagnostic item limit.
pub(super) fn describe_goal_proof_context(
    goal: Option<&Proposition>,
    pure_facts: &[Proposition],
    case_facts: &[Proposition],
    resource_facts: &[ResourceFact],
    result: Option<&ProgramValue>,
    labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels,
) -> String {
    // The returned value's checked type decides how a constant beside it
    // prints, even when the value has no source name.
    if let Some(result) = result {
        labels.source_result(result);
    }
    let mut relevant = match goal {
        Some(goal) => pure_facts_relevant_to(goal, pure_facts),
        None => pure_facts.to_vec(),
    };
    relevant.retain(|fact| !case_facts.contains(fact));
    // A case condition often shares no term with the goal -- `u == 0` false
    // after a split on whether a store wrote the cell a load reads -- yet it
    // says which case the claim fails in, so it gets its own line.
    let case = if case_facts.is_empty() {
        String::new()
    } else {
        format!(
            "\n  case: {}",
            describe_context_facts_labeled(case_facts, &[], labels)
        )
    };
    // One label set for the whole context, so a `<state A>` on the case
    // line is the same memory as one among the pure facts.
    let pure = describe_context_facts_labeled(&relevant, &[], labels);
    let resources = crate::surface::proof_diagnostics::render::render_resource_facts_labeled(
        resource_facts,
        labels,
    );
    format!(
        "{GOAL_PROOF_CONTEXT_HEADER}{case}\n  pure facts: {pure}\n  resource facts: {resources}{}",
        labels.trace_legend()
    )
}

pub(super) fn describe_proof_context(
    pure_facts: &[Proposition],
    resource_facts: &[ResourceFact],
    parameter_binding: ParameterBinding<'_>,
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
) -> String {
    // One label set, so a placeholder in a resource's hidden record is the
    // value the pure facts give the same name.
    let mut labels =
        crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(parameter_binding);
    let pure = describe_context_facts_labeled(pure_facts, execution_pure_facts, &mut labels);
    let resources = crate::surface::proof_diagnostics::render::render_resource_facts_labeled(
        resource_facts,
        &mut labels,
    );
    format!(
        "proof context:\n  pure facts: {pure}\n  resource facts: {resources}{}",
        labels.trace_legend()
    )
}

/// A loop head the kernel could not build, spelled over the head state's
/// locals.
pub(super) fn describe_loop_head_refusal(refusal: &crate::kernel::LoopHeadRefusal) -> String {
    let (proposition, context, state) = match refusal {
        crate::kernel::LoopHeadRefusal::Message(message) => return message.clone(),
        crate::kernel::LoopHeadRefusal::UnheldResource { fact, state } => {
            let (parameters, arguments) = local_naming_tables(state);
            return format!(
                "loop declares a resource the enclosing function does not hold: `{}`",
                render_resource_fact_diagnostic(
                    fact,
                    ParameterBinding::new(&parameters, &arguments)
                )
            );
        }
        crate::kernel::LoopHeadRefusal::MissingPrerequisite {
            proposition,
            context,
            state,
        } => (proposition, context, state),
    };
    let fact = describe_stated_fact_over_locals(proposition, state);
    let context = context
        .as_ref()
        .map(|context| format!(" ({context})"))
        .unwrap_or_default();
    format!("missing loop-head prerequisite{context}: `{fact}`")
}

/// One contract claim clause as its source wrote it: the proposition of an
/// `ensures`, or the `owns`/`produces` resource clause, with its guard.
pub(super) fn describe_ensure_clause(clause: &EnsureClause) -> String {
    match clause.ensure() {
        Ensure::Proposition(proposition) => describe_click_proposition(proposition),
        Ensure::Resource(resource) => {
            let verb = if clause.borrowed() {
                "owns"
            } else {
                "produces"
            };
            // A memory resource's own spelling already starts with its
            // access verb; the clause's verb replaces it.
            let described = crate::surface::validation::describe_resource_clause(resource);
            let described = described
                .strip_prefix("owns ")
                .or_else(|| described.strip_prefix("views "))
                .unwrap_or(&described);
            let spelling = format!("{verb} {described}");
            clause.condition().map_or(spelling.clone(), |guard| {
                format!("if {} {{ {spelling}; }}", describe_click_proposition(guard))
            })
        }
    }
}

/// The contract claims certification did not establish, each named by its
/// claim label and spelled as the source clause wrote it, bounded by the
/// diagnostic item limit.
pub(super) fn describe_unverified_contract_claims(
    function_block: &FunctionBlock,
    keys: &[crate::kernel::FunctionContractClaimKey],
) -> String {
    use crate::kernel::FunctionContractClaimKey;
    let function_name = function_block.signature().name();
    let describe_clause = |label: String, clause: &EnsureClause| {
        format!("{label} `{}`", describe_ensure_clause(clause))
    };
    let item_limit = diagnostic_item_limit();
    let mut described = keys
        .iter()
        .take(item_limit)
        .map(|key| match key {
            FunctionContractClaimKey::BodySafety => format!("{function_name} body safety"),
            FunctionContractClaimKey::Effect(index) => {
                format!("{function_name} effect clause {index}")
            }
            FunctionContractClaimKey::Ensure(index) => {
                let label = function_block.ensure_claim_label(*index);
                match function_block.ensures().get(*index) {
                    Some(clause) => describe_clause(label, clause),
                    None => label,
                }
            }
            FunctionContractClaimKey::ExceptionalEnsure(index) => {
                let label = function_block.exceptional_ensure_claim_label(*index);
                match function_block.exceptional_ensures().get(*index) {
                    Some(clause) => describe_clause(label, clause),
                    None => label,
                }
            }
        })
        .collect::<Vec<_>>();
    if keys.len() > item_limit {
        described.push(format!("… {} more omitted", keys.len() - item_limit));
    }
    described.join(", ")
}

/// A fact as a proof would state it, spelled over `state`'s locals: the
/// kernel variables a step or a loop head minted for them read as the
/// locals' names.
pub(super) fn describe_stated_fact_over_locals(
    fact: &Proposition,
    state: &ExecutionState,
) -> String {
    let (parameters, arguments) = local_naming_tables(state);
    describe_stated_fact(fact, ParameterBinding::new(&parameters, &arguments))
}

/// The naming tables of `state`'s locals: the kernel variables a step or a
/// loop head minted for them read as the locals' names.
pub(super) fn local_naming_tables(
    state: &ExecutionState,
) -> (
    Vec<crate::languages::interface::ImportedParameter>,
    Vec<ProgramExpression>,
) {
    let mut values = state
        .locals()
        .object_values()
        .filter(|(name, _)| !name.starts_with("__rust_"))
        .map(|(name, value)| {
            (
                crate::kernel::program_local_source_name(name).to_string(),
                value.clone().into_native(),
            )
        })
        .collect::<BTreeMap<_, _>>();
    // The results of the running statement's call steps, each spelled by
    // its call: `statement(0).call(f, 0).result`.
    if let Some(results) = &state.step_results {
        values.extend(results.iter().filter_map(|(call, value)| {
            Some((
                describe_contract_expression(&step_result_expression(*call)?),
                value.native().into_owned(),
            ))
        }));
    }
    value_naming_tables(&values)
}

/// The result of step `step`, as the statements as written name it: a call
/// step's `<call>.result`, or `at(<assignment>.entry, x)` for the value an
/// assignment step replaced in `x`.
pub(in crate::surface) fn step_result_expression(step: u32) -> Option<ContractExpression> {
    let layout = spelling_layout()?;
    let region = layout.step_region(step)?;
    match layout.prior_step_local(step) {
        Some(local) => {
            let steps = layout.source_path_spelling(region, ProgramPointKind::Entry)?;
            Some(ContractExpression::At {
                selector: crate::surface::ProgramPointSelector::ProgramPoint(
                    crate::surface::ProgramPointRef {
                        region: CodeRegionRef::Path(steps),
                        kind: ProgramPointKind::Entry,
                    },
                ),
                expression: Box::new(ContractExpression::ProgramExpression(
                    ProgramExpression::Variable(
                        crate::kernel::program_local_source_name(local).to_string(),
                    ),
                )),
            })
        }
        None => {
            let steps = layout.source_path_spelling(region, ProgramPointKind::Exit)?;
            Some(ContractExpression::RegionResult(CodeRegionRef::Path(steps)))
        }
    }
}

/// Name current locals with their source declarations, when available.
/// Layouts describe the local's type; its address still comes from `state`,
/// so reassigning a pointer never reuses its function-entry address.
/// A pointer without a source declaration is named in explicit byte units:
/// compatible kernel pointer types cannot establish a nominal struct type.
pub(super) fn local_naming_tables_with_source(
    state: &ExecutionState,
    function: Option<&crate::languages::interface::ImportedFunction>,
) -> (
    Vec<crate::languages::interface::ImportedParameter>,
    Vec<ProgramExpression>,
) {
    let (mut parameters, arguments) = local_naming_tables(state);
    let source_parameters = function
        .into_iter()
        .flat_map(|function| function.parameters())
        .map(|parameter| (parameter.name(), parameter))
        .collect::<std::collections::BTreeMap<_, _>>();
    for parameter in &mut parameters {
        if let Some(source) = source_parameters.get(parameter.name()) {
            *parameter = (**source).clone();
        } else if let Some((name, layout)) = function.and_then(|function| {
            let name = function.local_struct_pointers().get(parameter.name())?;
            Some((name, function.structs().get(name)?))
        }) {
            *parameter = parameter
                .clone()
                .with_pointee_struct_layout(name.clone(), layout.clone());
        } else if parameter.interface_type().is_pointer() {
            // Only the rendered cast matters here; the byte signedness is
            // never read.
            *parameter = crate::languages::interface::ImportedParameter::new(
                InterfaceType::CharPointer(syntax::PlainChar::Unsigned),
                format!("((char *){})", parameter.name()),
                None,
            );
        }
    }
    (parameters, arguments)
}

/// A runtime error spelled over `state`'s locals, so an address a loop head
/// minted a variable for reads as the index the source wrote.
pub(super) fn describe_runtime_error_over_locals(
    error: &crate::kernel::RuntimeError,
    state: &ExecutionState,
) -> String {
    let (parameters, arguments) = local_naming_tables(state);
    describe_runtime_error(error, ParameterBinding::new(&parameters, &arguments))
}

pub(super) fn describe_missing_proof_obligations(
    obligations: &[ProofObligation],
    pure_facts: &[Proposition],
    resource_facts: &[ResourceFact],
    parameter_binding: ParameterBinding<'_>,
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
) -> String {
    let item_limit = diagnostic_item_limit();
    let mut required = obligations
        .iter()
        .take(item_limit)
        .map(|obligation| match obligation.context() {
            Some(context) => format!(
                "{context}: {}",
                describe_pure_fact(obligation.proposition(), parameter_binding)
            ),
            None => describe_pure_fact(obligation.proposition(), parameter_binding),
        })
        .collect::<Vec<_>>();
    if obligations.len() > item_limit {
        required.push(format!("… {} more omitted", obligations.len() - item_limit));
    }

    let label = if required.len() == 1 {
        "missing pure fact"
    } else {
        "missing pure facts"
    };
    format!(
        "{label}: [{}]\n  {}",
        required.join(", "),
        describe_available_facts(
            pure_facts,
            resource_facts,
            parameter_binding,
            execution_pure_facts
        )
    )
}

/// A required condition the available facts decide against. It is refuted,
/// not merely underived: no smaller step or listed premise supplies it. The
/// sentence names the condition and the condition facts about its
/// variables, the ones a reader compares it to: for the `uint8` upper bound
/// of a returned `int32` known to be `300`, "the facts refute `x <= 255`:
/// [x == 300]".
pub(super) fn describe_refuted_condition(
    required: &Proposition,
    pure_facts: &[Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let variables = crate::kernel::proposition_variables(required);
    let about = pure_facts
        .iter()
        .filter(|fact| {
            matches!(fact, Proposition::ConditionIs(_, _))
                && (variables.is_empty()
                    || !crate::kernel::proposition_variables(fact).is_disjoint(&variables))
        })
        .cloned()
        .collect::<Vec<_>>();
    format!(
        "the facts refute `{}`: {}",
        describe_stated_fact(required, parameter_binding),
        describe_bounded_list(&about, |fact| describe_stated_fact(fact, parameter_binding)),
    )
}

/// [`describe_refuted_condition`] for an obligation a path owes, under the
/// obligation's own context when it has one: "uint8 narrowing upper bound:
/// the facts refute `x <= 255`: [x == 300]".
pub(super) fn describe_refuted_proof_obligation(
    obligation: &ProofObligation,
    pure_facts: &[Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let refutation =
        describe_refuted_condition(obligation.proposition(), pure_facts, parameter_binding);
    match obligation.context() {
        Some(context) => format!("{context}: {refutation}"),
        None => refutation,
    }
}

/// Where in `statement` its undefined behavior `kind` arises, as the line
/// "\n  operation: `a + b`" that precedes the C statement line, or nothing
/// when no single operation can be named.
pub(in crate::surface) fn describe_undefined_behavior_site(
    state: &ExecutionState,
    statement: &ProgramStatement,
    assumptions: &crate::kernel::PureFactContext,
    kind: &crate::kernel::UndefinedBehavior,
) -> String {
    describe_located_undefined_behavior(crate::kernel::locate_undefined_behavior(
        state,
        statement,
        assumptions,
        kind,
    ))
}

/// [`describe_undefined_behavior_site`] for a branch or loop condition.
pub(in crate::surface) fn describe_undefined_behavior_condition_site(
    state: &ExecutionState,
    condition: &ProgramExpression,
    assumptions: &crate::kernel::PureFactContext,
    kind: &crate::kernel::UndefinedBehavior,
) -> String {
    describe_located_undefined_behavior(crate::kernel::locate_undefined_behavior_in_condition(
        state,
        condition,
        assumptions,
        kind,
    ))
}

fn describe_located_undefined_behavior(
    site: Option<crate::kernel::UndefinedBehaviorSite>,
) -> String {
    let (prefix, expression) = match site {
        Some(crate::kernel::UndefinedBehaviorSite::Expression(expression)) => ("", expression),
        Some(crate::kernel::UndefinedBehaviorSite::Store(pointer)) => {
            ("the store through ", pointer)
        }
        None => return String::new(),
    };
    let spelling = describe_program_expression(&expression);
    // A read the printer can only spell as a kernel load (an aggregate field
    // at a byte offset) is not something the reader wrote; the C statement
    // line already names the source.
    if spelling.contains("load_") || spelling.contains("byte_offset(") {
        return String::new();
    }
    format!(
        "\n  operation: {prefix}`{}`",
        without_enclosing_parentheses(&spelling)
    )
}

/// `spelling` without one pair of parentheses around the whole of it:
/// `(a + b)` is `a + b`, while `(a) + (b)` is unchanged.
fn without_enclosing_parentheses(spelling: &str) -> &str {
    let Some(inner) = spelling
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
    else {
        return spelling;
    };
    let mut depth = 0usize;
    for character in inner.chars() {
        match character {
            '(' => depth += 1,
            ')' if depth == 0 => return spelling,
            ')' => depth -= 1,
            _ => {}
        }
    }
    inner
}

pub(super) fn describe_function_outcome(
    outcome: &FunctionOutcome,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    match outcome {
        FunctionOutcome::Return { value, .. } => {
            format!(
                "returned {}",
                describe_program_value(&value.native(), parameter_binding)
            )
        }
        FunctionOutcome::Throw { value, .. } => {
            format!(
                "threw {}",
                describe_program_value(&value.native(), parameter_binding)
            )
        }
        FunctionOutcome::VerificationDiverges => "has no verified return frontier".to_string(),
        FunctionOutcome::UndefinedBehavior(kind) => {
            format!("undefined behavior: {}", kind.description())
        }
        FunctionOutcome::RuntimeError(error) => format!(
            "C operation could not be verified: {}",
            describe_runtime_error(error, parameter_binding)
        ),
    }
}

pub(super) fn describe_runtime_error(
    error: &crate::kernel::RuntimeError,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    match error {
        crate::kernel::RuntimeError::UnboundVariable(name) => {
            format!("unbound variable `{name}`")
        }
        crate::kernel::RuntimeError::UnknownFunction(name)
            if crate::languages::c::thread_runtime::is_publication_operation(name) =>
        {
            format!(
                "`{name}` is declared by Click's `<stdatomic.h>` projection, but only the modeled-pthread thread runtime models C11 atomic operations"
            )
        }
        crate::kernel::RuntimeError::UnknownFunction(name) => {
            format!(
                "unknown function `{name}`: no verified source defines it and the sidecar declares no contract for it; describe an implementation outside the verified sources with an `extern` contract in the sidecar (docs/reference/language/c.md#external-function-contracts)"
            )
        }
        crate::kernel::RuntimeError::TypeMismatch => "type mismatch".to_string(),
        crate::kernel::RuntimeError::HeapAllocationSize => {
            crate::kernel::RuntimeError::HEAP_ALLOCATION_SIZE_MESSAGE.to_string()
        }
        crate::kernel::RuntimeError::HeapAllocationSizeAboveInt32 => {
            crate::kernel::RuntimeError::HEAP_ALLOCATION_SIZE_ABOVE_INT32_MESSAGE.to_string()
        }
        crate::kernel::RuntimeError::WideRangeRespellingMayWrap(no_wrap) => {
            describe_wide_range_no_wrap(no_wrap, parameter_binding)
        }
        crate::kernel::RuntimeError::LoadTypeMismatch {
            pointer,
            value_type,
            stored,
        } => {
            let found = match stored {
                Some(stored) => {
                    format!("found {}", describe_program_value(stored, parameter_binding))
                }
                None => "did not fit the cell's value".to_string(),
            };
            format!(
                "a {}-byte load at `{}` {found}",
                value_type.byte_width(),
                describe_pointer(pointer, parameter_binding)
            )
        }
        crate::kernel::RuntimeError::PointerConversion(message)
        | crate::kernel::RuntimeError::EnumVariant(message) => message.clone(),
        crate::kernel::RuntimeError::IndeterminatePointeeType => {
            "pointer operation has no known pointee type".to_string()
        }
        crate::kernel::RuntimeError::WrongArity { expected, actual } => {
            format!("wrong argument count: expected {expected}, got {actual}")
        }
        crate::kernel::RuntimeError::MissingReturn => "missing return".to_string(),
        crate::kernel::RuntimeError::MutexStorageScopeEnd { local, mutex, may_alias } => {
            let live = format!("mutex_live({})", describe_mutex_pointer(mutex, parameter_binding));
            if *may_alias {
                format!("Click cannot yet prove that {live} lies outside local storage `{local}`; its storage must outlive this scope")
            } else {
                format!("Cannot end local storage `{local}` while {live} remains initialized; call pthread_mutex_destroy before leaving its scope")
            }
        }
        crate::kernel::RuntimeError::MutexStorageInUse { mutex, .. } => {
            let subject = if matches!(mutex.block, crate::kernel::PointerBlock::Heap(_)) {
                "a mutex in this allocation".to_string()
            } else {
                format!("mutex {}", describe_mutex_pointer(mutex, parameter_binding))
            };
            format!("Cannot release allocation storage while {subject} remains initialized; call pthread_mutex_destroy before releasing its storage")
        }
        crate::kernel::RuntimeError::MutexStorageSeparationRequired { allocation, storage } =>
            format!("Requires {}; initialized mutex storage must remain live",
                describe_pure_fact(&Proposition::ResourceSeparate {
                    left: Box::new(Resource::Memory(*allocation.clone())),
                    right: Box::new(Resource::Memory(*storage.clone())),
                }, parameter_binding)),
        crate::kernel::RuntimeError::MutexStorageWrite { write, storage } =>
            format!("Requires {}; initialized mutex storage is reserved until pthread_mutex_destroy",
                describe_pure_fact(&Proposition::ResourceSeparate {
                    left: Box::new(Resource::Memory(*write.clone())),
                    right: Box::new(Resource::Memory(*storage.clone())),
                }, parameter_binding)),
        crate::kernel::RuntimeError::MissingMutexStorageAlignment { mutex, alignment } =>
            format!("Requires aligned({}, {alignment})", describe_mutex_pointer(mutex, parameter_binding)),
        crate::kernel::RuntimeError::UnsupportedMutexStorageRetirement =>
            "Click does not yet support freeing or reallocating storage in a preserving guard contract; checked mutex lifetime authority is required".into(),
        crate::kernel::RuntimeError::MissingMutexGuard { mutex } => format!(
            "Requires owns mutex_guard({})",
            describe_mutex_pointer(mutex, parameter_binding)
        ),
        crate::kernel::RuntimeError::MissingMutexLive { mutex } => format!(
            "Requires owns mutex_live({})",
            describe_mutex_pointer(mutex, parameter_binding)
        ),
        crate::kernel::RuntimeError::MissingMutexUse { mutex } => format!(
            "Requires owns mutex_use({})",
            describe_mutex_pointer(mutex, parameter_binding)
        ),
        crate::kernel::RuntimeError::MissingMutexInvariant { resource, supplied } => {
            let spell = |fact: &ResourceFact| render_resource_fact_diagnostic(fact, parameter_binding);
            match supplied {
                Some(supplied) => format!(
                    "Requires {}; the selected state is {}",
                    spell(resource),
                    spell(supplied)
                ),
                None => format!("Requires {}", spell(resource)),
            }
        }
        crate::kernel::RuntimeError::MissingResource { resource } => {
            let fact = render_resource_fact_diagnostic(resource, parameter_binding);
            if matches!(resource.resource(), Resource::MutexGuard(_) | Resource::MutexLive(_) | Resource::MutexUse(_)) {
                format!("Requires {fact}")
            } else {
                format!("missing resource fact `{fact}`")
            }
        }
        crate::kernel::RuntimeError::UnestablishedAssemblyFact { assembled, fact, source } => {
            use crate::surface::proof_diagnostics::render::{MemoryStateLabels, render_proposition_labeled};
            let mut labels = MemoryStateLabels::naming(parameter_binding);
            let requirement = match source.as_deref() {
                Some(source) => describe_assembly_body_fact_source(source, &mut labels),
                None => render_proposition_labeled(fact, &mut labels),
            };
            format!(
                "assembling `{}` from the caller's bytes requires an exact body fact: missing pure fact: {}{}",
                render_resource_fact_diagnostic(assembled, parameter_binding),
                requirement,
                labels.trace_legend()
            )
        }
        crate::kernel::RuntimeError::UnbackedReturnedView { view } => format!(
            "{}: `{}`",
            crate::kernel::RuntimeError::UNBACKED_RETURNED_VIEW,
            render_resource_fact_diagnostic(view, parameter_binding)
        ),
        crate::kernel::RuntimeError::MissingVerifiedFunctionRule(name) => format!(
            "cannot execute call to `{name}`: the sidecar states no contract for it; state one, as a function this sidecar verifies or as an `extern` declaration"
        ),
        crate::kernel::RuntimeError::UnsupportedOpaqueFunctionContract(name) => format!(
            "cannot execute call to `{name}` opaquely: its contract refers to an internal program point that is unavailable at the call site"
        ),
        crate::kernel::RuntimeError::AbstractFunctionPointerCall(name) => {
            if let Some(source) = super::proof::callback_source_name(name) {
                format!("cannot verify call: no contract fact for the function pointer `{source}` with this call signature")
            } else {
                format!(
                    "cannot verify call through function pointer `{name}`: no matching named contract is available for this value"
                )
            }
        }
        crate::kernel::RuntimeError::ContractResourceDiagnostic { reason, held, required, memory } => {
            use crate::surface::proof_diagnostics::render::{MemoryStateLabels, render_resource_fact_labeled};
            let mut labels = MemoryStateLabels::naming(parameter_binding);
            let mut message = format!("function contract could not be applied: {reason}");
            if let Some(memory) = memory {
                message.push_str(&format!(
                    "\n  arguments read in: {}",
                    labels.state_phrase(memory)
                ));
            }
            if let Some(held) = held {
                message.push_str(&format!("\n  held: {}", render_resource_fact_labeled(held, &mut labels)));
            }
            message.push_str(&format!("\n  required: {}", render_resource_fact_labeled(required, &mut labels)));
            message.push_str(&labels.trace_legend());
            message
        }
        crate::kernel::RuntimeError::PendingCallObligations(pending) => {
            use crate::surface::proof_diagnostics::render::{MemoryStateLabels, render_proposition_labeled};
            let mut labels = MemoryStateLabels::naming(parameter_binding);
            let mut message = "call cannot finish with unresolved proof obligations:".to_string();
            for obligation in pending.iter() {
                if let Some(context) = obligation.context() {
                    message.push_str(&format!("\n  context: {context}"));
                }
                if let Some(source) = obligation.call_requirement_site() {
                    message.push_str(&format!("\n  callee: {}", source.callee));
                    if let Some(ordinal) = source.source_requirement_ordinal {
                        message.push_str(&format!("; source contract input clause {}", ordinal + 1));
                    }
                }
                message.push_str(&format!("\n  pending goal: {}", render_proposition_labeled(obligation.proposition(), &mut labels)));
            }
            message.push_str(&labels.trace_legend());
            message
        }
        crate::kernel::RuntimeError::FunctionContract(message)
        | crate::kernel::RuntimeError::UnsuppliedResourceValue(message) => {
            format!(
                "function contract could not be applied: {}",
                name_string_literal_storage(message)
            )
        }
        crate::kernel::RuntimeError::UninitializedMutex { mutex } => format!(
            "could not prove that mutex `{}` was initialized on this path",
            describe_pointer(mutex, parameter_binding)
        ),
        crate::kernel::RuntimeError::UnsupportedConcurrentMutex => {
            "Click cannot yet verify pthread workers sharing an initialized mutex".to_string()
        }
        crate::kernel::RuntimeError::InvalidFree(reason) => match reason {
            crate::kernel::InvalidFree::InteriorPointer => {
                "cannot free an interior pointer; free requires the allocation base".to_string()
            }
            crate::kernel::InvalidFree::NonHeapPointer => {
                "cannot free a pointer that is not a live heap allocation".to_string()
            }
            crate::kernel::InvalidFree::DoubleFree => {
                "cannot free an allocation whose lifetime has already ended".to_string()
            }
        },
        crate::kernel::RuntimeError::UnresolvedAllocationOutcome => {
            "malloc result was neither refined by a null check nor returned".to_string()
        }
        crate::kernel::RuntimeError::LiveAllocationLeak {
            allocation,
            resource,
        } => {
            let mut message = format!(
                "live allocation obligation was neither returned nor freed: `{}`",
                render_resource_fact_diagnostic(allocation, parameter_binding)
            );
            if let Some(resource) = resource {
                message.push_str("; held by ");
                message.push_str(&render_resource_fact_diagnostic(resource, parameter_binding));
            }
            message
        }
        crate::kernel::RuntimeError::StaleResourceAfterFree { resource } => format!(
            "resource would remain usable after its allocation is freed: `{}`",
            render_resource_fact_diagnostic(resource, parameter_binding)
        ),
        crate::kernel::RuntimeError::DuplicateResource { resource } => format!(
            "duplicate resource fact `{}`",
            render_resource_fact_diagnostic(resource, parameter_binding)
        ),
        crate::kernel::RuntimeError::OverlappingOwnedMemoryResources { left, right } => format!(
            "overlapping owned memory resource facts `owns {}` and `owns {}`",
            describe_memory_range(left, parameter_binding),
            describe_memory_range(right, parameter_binding)
        ),
        crate::kernel::RuntimeError::ProducedCompositeOverlapsHeldResource {
            produced,
            piece,
            held,
        } => format!(
            "produced composite `{}` overlaps a resource the caller already holds: \
             its body `{}` overlaps `{}`",
            render_resource_diagnostic(produced.resource(), parameter_binding),
            render_resource_fact_diagnostic(piece, parameter_binding),
            render_resource_fact_diagnostic(held, parameter_binding)
        ),
        crate::kernel::RuntimeError::LoanRefusal(diagnostic) => {
            describe_loan_refusal(diagnostic, parameter_binding)
        }
    }
}

/// Kernel `RuntimeError` includes ordinary proof refusals, so its name is not
/// a surface error category. Only explicitly marked verifier limitations are
/// reported as internal errors.
pub(super) fn runtime_refusal_kind(error: &crate::kernel::RuntimeError) -> ClickErrorKind {
    match error {
        crate::kernel::RuntimeError::UnsupportedConcurrentMutex
        | crate::kernel::RuntimeError::UnsupportedMutexStorageRetirement
        | crate::kernel::RuntimeError::MutexStorageScopeEnd {
            may_alias: true, ..
        } => ClickErrorKind::Internal,
        _ => ClickErrorKind::Proof,
    }
}

/// The D13 shape for a refusal that is a conflict between two named things:
/// which loan refused, where that loan came from, what it protects, and what
/// the refused operation attempted. Both halves are bounded facts from the
/// refusal subject; nothing here reads the ledger or the resource frame.
fn describe_loan_conflict(
    diagnostic: &crate::kernel::LoanRefusalDiagnostic,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let subject = diagnostic.subject();
    let conflicting = subject.conflicting_resource_fact()?;
    let conflicting = render_resource_fact_diagnostic(conflicting, parameter_binding);
    if diagnostic.operation() == crate::kernel::LoanRefusalOperation::Entry {
        let viewed = subject.resource_fact()?;
        // This message follows the proof's own sentence about the contract
        // input, so it names the two clauses directly and adds no prefix.
        return Some(format!(
            "the contract's `views` clause overlaps its own `owns` clause: `{}` is already supported by `{conflicting}`; \
             a view must name authority the caller lends, not authority this contract owns",
            render_resource_fact_diagnostic(viewed, parameter_binding)
        ));
    }
    let attempted = subject.memory_range()?;
    let origin = match subject.origin()? {
        crate::kernel::LoanOriginKind::LocalStorage => "a view of local storage",
        crate::kernel::LoanOriginKind::ContractInputView => "a contract input view",
        crate::kernel::LoanOriginKind::LentOwner => "an owner lent for a call",
        crate::kernel::LoanOriginKind::Reborrow => "a reborrow of a live loan",
    };
    let loan = subject
        .loan_id()
        .map_or_else(String::new, |(arena, ordinal)| {
            format!(" (loan {arena}:{ordinal})")
        });
    Some(format!(
        "stable-view memory access conflicts with an active loan: the attempted range `{}` overlaps `{conflicting}`, lent as {origin}{loan}",
        describe_memory_range(attempted, parameter_binding)
    ))
}

pub(in crate::surface) fn describe_loan_refusal(
    diagnostic: &crate::kernel::LoanRefusalDiagnostic,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    if let Some(conflict) = describe_loan_conflict(diagnostic, parameter_binding) {
        return conflict;
    }
    let category = match diagnostic.category() {
        crate::kernel::LoanRefusalCategory::ProvenOverlap => {
            "a required resource overlaps a live borrowed footprint"
        }
        crate::kernel::LoanRefusalCategory::SeparationUnproved => {
            "the verifier could not prove the requested ranges separate"
        }
        crate::kernel::LoanRefusalCategory::WrongHolder => {
            "the loan evidence names the wrong participant"
        }
        crate::kernel::LoanRefusalCategory::WrongArena => {
            "the loan evidence belongs to a different authority arena"
        }
        crate::kernel::LoanRefusalCategory::WrongScope => "the loan evidence names the wrong scope",
        crate::kernel::LoanRefusalCategory::ActiveDependency => {
            "an active loan dependency blocks this operation"
        }
        crate::kernel::LoanRefusalCategory::StalePredecessor => {
            "the loan evidence uses a stale predecessor state"
        }
        crate::kernel::LoanRefusalCategory::Recovery => {
            "loan recovery evidence is inconsistent or already consumed"
        }
        crate::kernel::LoanRefusalCategory::Lifetime => {
            "the loan scope has an incompatible lifetime state"
        }
        crate::kernel::LoanRefusalCategory::Unsupported => {
            "this resource shape is outside stable-view support"
        }
        crate::kernel::LoanRefusalCategory::Missing => {
            "the required loan backing or binding is missing"
        }
        crate::kernel::LoanRefusalCategory::InvalidEvidence => "the loan evidence is invalid",
    };
    let subject = diagnostic.subject();
    let subject = if let Some(resource) = subject.resource_fact() {
        format!(
            "; selected resource `{}`",
            render_resource_fact_diagnostic(resource, parameter_binding)
        )
    } else if let Some(range) = subject.memory_range() {
        format!(
            "; selected range `{}`",
            describe_memory_range(range, parameter_binding)
        )
    } else {
        String::new()
    };
    let ids = {
        let subject = diagnostic.subject();
        let mut ids = Vec::new();
        if let Some((arena, ordinal)) = subject.loan_id() {
            ids.push(format!("loan {arena}:{ordinal}"));
        }
        if let Some((arena, ordinal)) = subject.scope_id() {
            ids.push(format!("scope {arena}:{ordinal}"));
        }
        if let Some((arena, ordinal)) = subject.share_id() {
            ids.push(format!("share {arena}:{ordinal}"));
        }
        if let Some((arena, ordinal)) = subject.support_id() {
            ids.push(format!("support {arena}:{ordinal}"));
        }
        if let Some(clause) = diagnostic.source_clause() {
            ids.push(format!("clause {clause}"));
        }
        if let Some(step) = diagnostic.source_step() {
            ids.push(format!("step {step}"));
        }
        if ids.is_empty() {
            String::new()
        } else {
            format!(" ({})", ids.join(", "))
        }
    };
    format!(
        "stable-view {} refused during {}{}{}",
        category,
        match diagnostic.operation() {
            crate::kernel::LoanRefusalOperation::Validate => "validation",
            crate::kernel::LoanRefusalOperation::Plan => "planning",
            crate::kernel::LoanRefusalOperation::Entry => "entry transition",
            crate::kernel::LoanRefusalOperation::Recovery => "recovery",
            crate::kernel::LoanRefusalOperation::Transition => "transition",
            crate::kernel::LoanRefusalOperation::MemoryAccess => "memory access",
        },
        subject,
        ids,
    )
}

/// One iterated guarded-ownership fact, spelled as the clause it came from:
/// the bounded index, the guard, and the element range at that index, plus
/// the indices currently taken out.
pub(in crate::surface) fn describe_iterated_memory(
    iterated: &crate::kernel::IteratedMemory,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let index = MachineTerm::Variable(crate::kernel::Variable(u64::MAX - 7));
    // Iterated ownership's element_range constructs signed int32 bounds.
    let element = iterated.element_range(&index);
    let spelled_index = describe_bitvector_with_context(&index, parameter_binding);
    let element = format!(
        "{}[{}..{}]",
        describe_pointer(element.base(), parameter_binding),
        describe_bitvector_with_context(element.start(), parameter_binding),
        describe_bitvector_with_context(element.end(), parameter_binding)
    )
    .replace(&spelled_index, "k");
    let guard_base = describe_pointer(iterated.guard().base(), parameter_binding);
    let mut text = format!(
        "forall k in {}..{} where {}[k] {} {}: {} (the iterated clause of `{}`)",
        describe_bitvector_with_context(iterated.lower(), parameter_binding),
        describe_bitvector_with_context(iterated.upper(), parameter_binding),
        guard_base,
        if iterated.guard().holds_when_equal() {
            "=="
        } else {
            "!="
        },
        describe_bitvector_with_context(iterated.guard().value(), parameter_binding),
        element,
        iterated.owner()
    );
    if !iterated.holes().is_empty() {
        text.push_str(&format!(
            ", with index {} taken out",
            iterated
                .holes()
                .iter()
                .map(|hole| describe_bitvector_with_context(hole, parameter_binding))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    text
}

pub(super) fn describe_resource_subject(resource: &ResourceSubject) -> String {
    match resource {
        ResourceSubject::Emp => "separation::emp".into(),
        ResourceSubject::Star(a, b) => format!(
            "({} * {})",
            describe_resource_subject(a),
            describe_resource_subject(b)
        ),
        ResourceSubject::Footprint(region) => {
            format!("{}.footprint", describe_code_region_ref(region))
        }
        ResourceSubject::Instance {
            name,
            at: Some(selector),
            ..
        } => format!("at({}, {name})", describe_program_point_selector(selector)),
        ResourceSubject::Parameter { name, .. } | ResourceSubject::Instance { name, .. } => {
            name.clone()
        }
        ResourceSubject::Captured { source, .. } => describe_resource_subject(source),
        ResourceSubject::Memory(segment) => {
            format!("memory({})", describe_contract_segment(segment))
        }
        ResourceSubject::SavedMemory { base, start, end } => {
            let start = describe_contract_expression(start);
            let bounds = match end {
                Some(end) => format!("{start}..{}", describe_contract_expression(end)),
                None => start,
            };
            format!("memory({}[{bounds}])", describe_contract_expression(base))
        }
        ResourceSubject::Declared {
            name, arguments, ..
        } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

/// Recover whole structs or contiguous field slots from byte coordinates.
fn describe_layout_place_range(
    layout: &crate::languages::interface::RecordLayout,
    name: &str,
    low: u64,
    high: u64,
) -> Option<String> {
    let size = u64::from(layout.size_bytes());
    if size == 0 || low >= high {
        return None;
    }
    if low.is_multiple_of(size) && high.is_multiple_of(size) {
        return Some(if low == 0 && high == size {
            describe_pointee_place(name)
        } else if high - low == size {
            format!("{name}[{}]", low / size)
        } else {
            format!("{name}[{}..{}]", low / size, high / size)
        });
    }
    let index = low / size;
    if (high - 1) / size != index {
        return None;
    }
    let (low, high) = (low % size, high - index * size);
    let member = |field: &str| {
        if index == 0 {
            describe_field_place(name, field)
        } else {
            format!("{name}[{index}].{field}")
        }
    };
    let mut fields = layout.fields().iter().collect::<Vec<_>>();
    fields.sort_by_key(|(_, field)| field.offset_bytes());
    for (position, (field_name, field)) in fields.iter().enumerate() {
        let field_low = u64::from(field.offset_bytes());
        let slot_high = fields
            .get(position + 1)
            .map_or(size, |(_, next)| u64::from(next.offset_bytes()));
        if low == field_low
            && (high == slot_high
                || high == field_low + u64::from(field.byte_width())
                || (field.interface_type().is_pointer() && low < high && high <= slot_high))
        {
            return Some(member(field_name));
        }
        // A single scalar array element keeps its field/index spelling even
        // when the range base has folded the index into a byte offset.
        if !field.interface_type().is_pointer()
            && field.struct_name().is_none()
            && field.array_shape().is_none_or(|shape| shape.len() == 1)
            && let Some(width) =
                scalar_element_width(field.interface_type()).map(|width| width as u64)
            && low >= field_low
            && high <= field_low + u64::from(field.byte_width())
            && high - low == width
            && (low - field_low).is_multiple_of(width)
        {
            return Some(format!(
                "{}[{}]",
                member(field_name),
                (low - field_low) / width
            ));
        }
    }
    // Leaf slots preserve dotted names for a partial embedded aggregate.
    let mut leaves = layout.leaf_field_offsets().collect::<Vec<_>>();
    leaves.sort_by_key(|(_, offset)| *offset);
    let mut places = Vec::new();
    let mut cursor = low;
    for (position, (field, offset)) in leaves.iter().enumerate() {
        let start = u64::from(*offset);
        let end = leaves
            .get(position + 1)
            .map_or(size, |(_, next)| u64::from(*next));
        if start == cursor && end <= high {
            places.push(member(field));
            cursor = end;
        }
    }
    if cursor != high || places.is_empty() {
        return None;
    }
    Some(if places.len() == 1 {
        places.remove(0)
    } else {
        let limit = diagnostic_item_limit();
        let mut shown = places.iter().take(limit).cloned().collect::<Vec<_>>();
        if places.len() > limit {
            shown.push(format!("… {} more omitted", places.len() - limit));
        }
        format!("{{{}}}", shown.join(", "))
    })
}

fn describe_struct_place_range(
    range: &MemoryRange,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let start = u64::from(range.constant_start()?);
    let end = u64::from(range.constant_end()?);
    let width = u64::from(range.element_width());
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        if parameter.is_struct_value()
            || parameter
                .interface_type()
                .pointee_type()
                .is_some_and(|ty| ty.is_pointer())
        {
            continue;
        }
        let Some(layout) = parameter
            .pointee_struct_layout()
            .or_else(|| parameter.struct_layout())
        else {
            continue;
        };
        if let Some(offset) = diagnostic_pointer_element_index_from_base(range.base(), base, 1)
            .and_then(|offset| offset.as_const())
            && let Some(place) = describe_layout_place_range(
                layout,
                parameter.name(),
                u64::from(offset) + start * width,
                u64::from(offset) + end * width,
            )
        {
            return Some(place);
        }
        // A recursive struct pointer field has the same known layout as its
        // parent. Do not infer that layout for pointers to another type.
        if let Some(field_name) =
            describe_parameter_struct_field_pointer(range.base(), parameter, base.pointer())
            && let Some((_, field)) = layout
                .fields()
                .iter()
                .find(|(name, _)| field_name == describe_field_place(parameter.name(), name))
            && field.struct_name().is_some()
            && field.struct_name() == parameter.struct_name()
            && let Some(place) =
                describe_layout_place_range(layout, &field_name, start * width, end * width)
        {
            return Some(place);
        }
    }
    None
}

/// A range inside one scalar array field of a struct, spelled from the
/// field: `p->a[i]`, `p->a[0..4]` or `h->in->a[i]`, for bounds the lowering
/// wrote as byte offsets from the struct. Display only.
fn describe_struct_array_field_range(
    range: &MemoryRange,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let (base, layout, start, end) = struct_byte_bounds(range, parameter_binding)?;
    let (field, start, end) = scalar_array_field_indices(&layout, &start, &end)?;
    let place = describe_field_place(&base, field);
    if is_one_element(&start, &end) {
        return Some(format!(
            "{place}[{}]",
            describe_bitvector_with_context(&start, parameter_binding)
        ));
    }
    Some(format!(
        "{place}[{}..{}]",
        describe_bitvector_with_context(&start, parameter_binding),
        describe_bitvector_with_context(&end, parameter_binding)
    ))
}

/// The spelling of the pointer whose struct `range` lies in, that struct's
/// layout, and the range's bounds as byte offsets from the pointer: a
/// pointer parameter, or a pointer field some load read.
fn struct_byte_bounds(
    range: &MemoryRange,
    parameter_binding: ParameterBinding<'_>,
) -> Option<(
    String,
    crate::languages::interface::RecordLayout,
    MachineTerm,
    MachineTerm,
)> {
    range.int32_bounds()?;
    let bounds = |offset: MachineTerm| {
        let bytes = |index: &MachineTerm| {
            Some(bitvector32_add(
                offset.clone(),
                rescale_range_index(index, range.element_width(), 1)?,
            ))
        };
        Some((bytes(range.start())?, bytes(range.end())?))
    };
    if let Some((parameter, layout, offset)) = parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .find_map(|(parameter, argument)| {
            let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
                return None;
            };
            if parameter.is_struct_value()
                || parameter
                    .interface_type()
                    .pointee_type()
                    .is_some_and(|ty| ty.is_pointer())
            {
                return None;
            }
            let layout = parameter
                .pointee_struct_layout()
                .or_else(|| parameter.struct_layout())?;
            let offset = pointer_offset_bytes(&range.base().offset_from_base(base.pointer())?)?;
            Some((parameter, layout, offset))
        })
    {
        let (start, end) = bounds(offset)?;
        return Some((parameter.name().to_string(), layout.clone(), start, end));
    }
    let (address, offset) = loaded_pointer_split(range.base())?;
    let layout =
        object_fields::ambient_struct_layout(&pointee_struct_at(&address, parameter_binding)?)?;
    let base = describe_load_at(&address, parameter_binding);
    if !is_place_spelling(&base) {
        return None;
    }
    let (start, end) = bounds(offset)?;
    Some((base, layout, start, end))
}

/// A pointer offset as a byte count: `i * 4 + 8` for `Int32Scaled(i, 4) +
/// 8`. Display only; a 64-bit scaled index is not narrowed.
fn pointer_offset_bytes(offset: &PointerOffsetTerm) -> Option<MachineTerm> {
    match offset {
        PointerOffsetTerm::Constant(bytes) => {
            Some(MachineTerm::constant(i32::try_from(*bytes).ok()? as u32))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } => Some(match byte_width {
            1 => value.structural_value().clone(),
            width => super::lowering::bitvector32_multiply(
                value.structural_value().clone(),
                MachineTerm::constant(i32::try_from(*width).ok()? as u32),
            ),
        }),
        PointerOffsetTerm::Add(left, right) => Some(bitvector32_add(
            pointer_offset_bytes(left)?,
            pointer_offset_bytes(right)?,
        )),
        PointerOffsetTerm::Int64Scaled { .. } | PointerOffsetTerm::Variable(_) => None,
    }
}

/// The scalar array field of `layout` holding the byte range `start..end`,
/// with the range as element indices of that field. The field is the one
/// the constant part of `start` falls in; constant bounds must also lie
/// inside it. `None` when the bounds are not whole elements of the field.
fn scalar_array_field_indices<'a>(
    layout: &'a crate::languages::interface::RecordLayout,
    start: &MachineTerm,
    end: &MachineTerm,
) -> Option<(&'a str, MachineTerm, MachineTerm)> {
    let anchor = constant_addend(start)?;
    let (name, field) = layout.fields().iter().find(|(_, field)| {
        let low = i64::from(field.offset_bytes());
        !field.interface_type().is_pointer()
            && field.struct_name().is_none()
            && field.array_shape().is_none_or(|shape| shape.len() == 1)
            && scalar_element_width(field.interface_type()).is_some()
            && low <= anchor
            && anchor < low + i64::from(field.byte_width())
    })?;
    let width = u32::try_from(scalar_element_width(field.interface_type())?).ok()?;
    let offset = field.offset_bytes();
    let index = |bytes: &MachineTerm| {
        if offset.is_multiple_of(width) {
            subtract_constant(&exact_quotient(bytes, width)?, offset / width)
        } else {
            exact_quotient(&subtract_constant(bytes, offset)?, width)
        }
    };
    let (start, end) = (index(start)?, index(end)?);
    let length = field.byte_width() / width;
    if let (Some(low), Some(high)) = (start.as_const(), end.as_const())
        && !(low as i32 >= 0 && low < high && high <= length)
    {
        return None;
    }
    Some((name.as_str(), start, end))
}

/// The constant summand of a byte offset: `8` in `8 + i * 4`, `0` in
/// `i * 4`. Display only; it picks the field a symbolic offset starts in.
fn constant_addend(term: &MachineTerm) -> Option<i64> {
    if let Some(value) = term.as_const() {
        return Some(i64::from(value as i32));
    }
    match term {
        bits32_constant!(value) => Some(i64::from(constant_u32(*value) as i32)),
        binary_term!(Int32, Add, left, right) => {
            Some(constant_addend(left)? + constant_addend(right)?)
        }
        binary_term!(Int32, Subtract, left, right) => {
            Some(constant_addend(left)? - constant_addend(right)?)
        }
        binary_term!(Int32, Multiply, left, right) => match (left.as_const(), right.as_const()) {
            (_, Some(factor)) => Some(constant_addend(left)? * i64::from(factor as i32)),
            (Some(factor), _) => Some(i64::from(factor as i32) * constant_addend(right)?),
            _ => Some(0),
        },
        MachineTerm::Variable(_) => Some(0),
        _ => None,
    }
}

/// `term - amount`, folding the constant into a constant summand.
fn subtract_constant(term: &MachineTerm, amount: u32) -> Option<MachineTerm> {
    if amount == 0 {
        return Some(term.clone());
    }
    match term {
        bits32_constant!(value) => Some(MachineTerm::constant(
            constant_u32(*value).wrapping_sub(amount),
        )),
        binary_term!(Int32, Add, left, right) => {
            if let Some(left) = left.as_const() {
                return Some(bitvector32_add(
                    MachineTerm::constant(left.wrapping_sub(amount)),
                    right.as_ref().clone(),
                ));
            }
            if let Some(right) = right.as_const() {
                return Some(bitvector32_add(
                    left.as_ref().clone(),
                    MachineTerm::constant(right.wrapping_sub(amount)),
                ));
            }
            None
        }
        _ => None,
    }
}

/// `term / width` when the term is visibly a multiple of `width`: a
/// constant multiple, a product by such a constant, or a sum or difference
/// of those. Display only.
fn exact_quotient(term: &MachineTerm, width: u32) -> Option<MachineTerm> {
    if width == 1 {
        return Some(term.clone());
    }
    match term {
        bits32_constant!(value) => {
            let value = constant_u32(*value) as i32;
            (value % width as i32 == 0)
                .then(|| MachineTerm::constant((value / width as i32) as u32))
        }
        binary_term!(Int32, Multiply, left, right) => {
            let (factor, constant) = match (left.as_const(), right.as_const()) {
                (_, Some(constant)) => (left.as_ref(), constant),
                (Some(constant), _) => (right.as_ref(), constant),
                _ => return None,
            };
            if !constant.is_multiple_of(width) {
                return None;
            }
            Some(match constant / width {
                1 => factor.clone(),
                multiple => super::lowering::bitvector32_multiply(
                    factor.clone(),
                    MachineTerm::constant(multiple),
                ),
            })
        }
        binary_term!(Int32, Add, left, right) => Some(bitvector32_add(
            exact_quotient(left, width)?,
            exact_quotient(right, width)?,
        )),
        _ => None,
    }
}

pub(super) fn describe_memory_range(
    range: &MemoryRange,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    // A wide range is spelled from its base and its own 64-bit bounds.
    if let Some((start, end)) = range.wide_bounds() {
        return format!(
            "{}[{}..{}]",
            describe_pointer(range.base(), parameter_binding),
            describe_bitvector_with_context(start, parameter_binding),
            describe_bitvector_with_context(end, parameter_binding)
        );
    }
    if let Some(place) = describe_struct_place_range(range, parameter_binding) {
        return place;
    }
    if let Some(place) = describe_struct_array_field_range(range, parameter_binding) {
        return place;
    }
    if let Some(place) = object_fields::object_range_spelling(range) {
        return place;
    }
    // Elements behind a pointer field are spelled from the field:
    // `a->data[0..n]`.
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        if let Some(field) =
            describe_parameter_struct_field_pointer(range.base(), parameter, base.pointer())
        {
            let layout = parameter
                .pointee_struct_layout()
                .or_else(|| parameter.struct_layout());
            let slot = layout.and_then(|layout| {
                layout.fields().iter().find_map(|(name, slot)| {
                    (field == describe_field_place(parameter.name(), name)).then_some(slot)
                })
            });
            let width = slot
                .filter(|slot| slot.struct_name().is_none())
                .and_then(|slot| {
                    slot.interface_type()
                        .pointee_type()
                        .map(|pointee| diagnostic_c_type_byte_width(pointee, slot.byte_width()))
                })
                .and_then(|width| u32::try_from(width).ok())
                .unwrap_or(1);
            let start = rescale_range_index(range.start(), range.element_width(), width);
            let end = rescale_range_index(range.end(), range.element_width(), width);
            let (field, start, end) = match (start, end) {
                (Some(start), Some(end))
                    if slot.is_some_and(|slot| slot.struct_name().is_none()) =>
                {
                    (field, start, end)
                }
                _ => (
                    format!("((char *){field})"),
                    rescale_range_index(range.start(), range.element_width(), 1)
                        .expect("byte scale"),
                    rescale_range_index(range.end(), range.element_width(), 1).expect("byte scale"),
                ),
            };
            return format!(
                "{field}[{}..{}]",
                describe_bitvector_with_context(&start, parameter_binding),
                describe_bitvector_with_context(&end, parameter_binding)
            );
        }
    }
    if let Some(description) = describe_loaded_pointer_range(range, parameter_binding) {
        return description;
    }
    if let Some(description) = describe_parameter_relative_range(range, parameter_binding) {
        return description;
    }
    if let Some(description) = describe_indexed_base_range(range, parameter_binding) {
        return description;
    }
    // A range over a named object starts at the object itself (`g[0..4]`),
    // not at a pointer to it.
    let base = match named_object_block(&range.base().block, parameter_binding) {
        Some(name) if range.base().offset == PointerOffsetTerm::Constant(0) => name,
        _ => {
            let cell = describe_pointer(range.base(), parameter_binding);
            // One element at an address spelled as a member or a byte offset
            // is that cell; `p->data[2][0..1]` would read as a second index.
            // A bare name or an elided address keeps its range.
            let compound = cell.starts_with("(char *)")
                || cell.contains("->")
                || cell.contains("].")
                || cell.ends_with(']');
            let one_element = range.constant_start() == Some(0) && range.constant_end() == Some(1);
            if compound && one_element {
                return cell;
            }
            // One element at a named object's address is that object, as a
            // clause writes it: `second`, not `&second[0..1]`.
            if one_element
                && let Some(name) = cell.strip_prefix('&')
                && name
                    .chars()
                    .all(|character| character.is_alphanumeric() || "_:".contains(character))
            {
                return name.to_string();
            }
            cell
        }
    };
    format!(
        "{}[{}..{}]",
        base,
        describe_bitvector_with_context(range.start(), parameter_binding),
        describe_bitvector_with_context(range.end(), parameter_binding)
    )
}

/// A range whose base is another pointer advanced by a scaled index, the
/// address of `p[i]` for an index `i` of the range's element width, spelled
/// from that pointer: `s->data[s->len]` for the one element at the address a
/// read through a loaded pointer forms, rather than an unnamed base. Only a
/// base the describer can name takes part.
fn describe_indexed_base_range(
    range: &MemoryRange,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let width = i64::from(range.element_width());
    let PointerOffsetTerm::Add(rest, last) = &range.base().offset else {
        return None;
    };
    let index = match last.as_ref() {
        PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        }
        | PointerOffsetTerm::Int32Scaled { value, byte_width }
            if *byte_width == width =>
        {
            value.structural_value()
        }
        _ => return None,
    };
    let root = Pointer {
        block: range.base().block.clone(),
        offset: rest.as_ref().clone(),
    };
    let base = describe_pointer(&root, parameter_binding);
    if base.contains("the pointer value at this program point") || base.contains('…') {
        return None;
    }
    let index = describe_bitvector_with_context(index, parameter_binding);
    let bounds = range.int32_bounds()?;
    match (bounds.0.as_const(), bounds.1.as_const()) {
        (Some(0), Some(1)) => Some(format!("{base}[{index}]")),
        (Some(start), Some(end)) => Some(format!("{base}[({index} + {start})..({index} + {end})]")),
        _ => None,
    }
}

/// The source name of the object a block holds: a local, global or static
/// by its declared name, and the null block as `NULL`. `None` for blocks the
/// verifier introduced (heap allocations, temporaries, symbolic pointers),
/// which no source text names.
fn named_object_block(
    block: &PointerBlock,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    if matches!(block, PointerBlock::Concrete(name) if name == "null") {
        return Some("NULL".to_string());
    }
    describe_memory_block(block, parameter_binding)
}

pub(super) fn describe_parameter_relative_range(
    range: &MemoryRange,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let (parameter, base_index) = parameter_relative_base(range, parameter_binding)?;
    let (start, end) = parameter_relative_endpoints(&base_index, range);
    let from = range.element_width();
    let to = u32::try_from(diagnostic_parameter_element_width(parameter)).ok()?;
    let (name, start, end) = match (
        rescale_range_index(&start, from, to),
        rescale_range_index(&end, from, to),
    ) {
        (Some(start), Some(end)) => (parameter.name().to_string(), start, end),
        _ => (
            format!("((char *){})", parameter.name()),
            rescale_range_index(&start, from, 1)?,
            rescale_range_index(&end, from, 1)?,
        ),
    };
    if let (Some(low), Some(high)) = (start.as_const(), end.as_const())
        && low.checked_add(1) == Some(high)
    {
        // A whole element behind a reference parameter is its referent.
        // An explicit byte slice keeps its exact extent and cast spelling.
        if low == 0
            && name == parameter.name()
            && parameter.is_reference()
            && let Some(referent) = syntax::referent_of_carrier(parameter.name())
        {
            return Some(referent.to_string());
        }
        return Some(format!("{}[{low}]", name));
    }
    // One element at a symbolic index is that element: `bytes[index]`.
    if range_end_is_next_element(&start, &end) {
        return Some(format!(
            "{}[{}]",
            name,
            describe_bitvector_with_context(&start, parameter_binding)
        ));
    }
    Some(format!(
        "{}[{}..{}]",
        name,
        describe_bitvector_with_context(&start, parameter_binding),
        describe_bitvector_with_context(&end, parameter_binding)
    ))
}

/// Whether `start..end` is one element: constants one apart, or `end`
/// written as `start + 1`.
fn is_one_element(start: &MachineTerm, end: &MachineTerm) -> bool {
    match (start.as_const(), end.as_const()) {
        (Some(start), Some(end)) => start.checked_add(1) == Some(end),
        _ => range_end_is_next_element(start, end),
    }
}

/// Whether `end` is written as `start + 1`, so the range is one element.
fn range_end_is_next_element(start: &MachineTerm, end: &MachineTerm) -> bool {
    let one = |term: &MachineTerm| term.as_const() == Some(1) || term.uint64_as_const() == Some(1);
    match end {
        binary_term!(Int32, Add, left, right)
        | MachineTerm::Binary {
            format: MachineIntegerType::Int64 | MachineIntegerType::UInt64,
            op: MachineBinaryOp::Add,
            left,
            right,
        } => (left.as_ref() == start && one(right)) || (right.as_ref() == start && one(left)),
        _ => false,
    }
}

/// The parameter a range is spelled against, with the element index of the
/// range's base from that parameter's base.
///
/// Every external pointer parameter shares one block, so any of them can name
/// a range as a symbolic offset from its own base: `b[0..1]` is also
/// `a[(b - a)..(b - a) + 1]`. Prefer the parameter the range sits at a
/// constant offset from, and fall back to the first symbolic one only when no
/// parameter does.
fn parameter_relative_base<'a>(
    range: &MemoryRange,
    parameter_binding: ParameterBinding<'a>,
) -> Option<(
    &'a crate::languages::interface::ImportedParameter,
    MachineTerm,
)> {
    let mut symbolic = None;
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        let Some(base_index) = diagnostic_pointer_element_index_from_base(
            range.base(),
            base,
            i64::from(range.element_width()),
        ) else {
            continue;
        };
        if base_index.as_const().is_some() {
            return Some((parameter, base_index));
        }
        // A pointer a load read is no symbolic offset from a parameter.
        if loaded_pointer_split(range.base()).is_none() {
            symbolic.get_or_insert((parameter, base_index));
        }
    }
    symbolic
}

fn rescale_range_index(index: &MachineTerm, from: u32, to: u32) -> Option<MachineTerm> {
    if to == 0 {
        return None;
    }
    if from.is_multiple_of(to) {
        return Some(super::lowering::bitvector32_multiply(
            index.clone(),
            MachineTerm::constant(from / to),
        ));
    }
    let bytes = i64::from(index.as_const()? as i32) * i64::from(from);
    (bytes % i64::from(to) == 0).then(|| MachineTerm::constant((bytes / i64::from(to)) as u32))
}

fn parameter_relative_endpoints(
    base_index: &MachineTerm,
    range: &MemoryRange,
) -> (MachineTerm, MachineTerm) {
    // A wide range is shown by its own bounds: they are 64-bit terms, and
    // a 32-bit parameter offset is not added to them. Display only.
    if let Some((start, end)) = range.wide_bounds() {
        return (start.clone(), end.clone());
    }
    (
        bitvector32_add(base_index.clone(), range.start().clone()),
        bitvector32_add(base_index.clone(), range.end().clone()),
    )
}

/// A call refused because assembling a viewed composite from the caller's
/// owned pieces is a fold whose body fact is unproved: the instance, the
/// missing fact and the available facts, as a refused `fold` reports them.
/// `None` for every other runtime error.
pub(super) fn describe_unestablished_assembly_fact(
    error: &crate::kernel::RuntimeError,
    pure_facts: &[Proposition],
    resource_facts: &[ResourceFact],
    parameter_binding: ParameterBinding<'_>,
    execution_pure_facts: &(impl ExecutionFactSource + ?Sized),
) -> Option<String> {
    let crate::kernel::RuntimeError::UnestablishedAssemblyFact {
        assembled,
        fact,
        source,
    } = error
    else {
        return None;
    };
    let missing = match source.as_deref() {
        Some(source) => {
            let mut labels = crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(
                parameter_binding,
            );
            let requirement = describe_assembly_body_fact_source(source, &mut labels);
            describe_missing_fact_context(
                &requirement,
                pure_facts,
                resource_facts,
                execution_pure_facts,
                &mut labels,
            )
        }
        None => describe_missing_pure_fact(
            fact,
            pure_facts,
            resource_facts,
            parameter_binding,
            execution_pure_facts,
        ),
    };
    Some(format!(
        "assembling `{}` from the caller's bytes requires an exact body fact: {}",
        render_resource_fact_diagnostic(assembled, parameter_binding),
        missing,
    ))
}

fn describe_assembly_body_fact_source(
    source: &crate::kernel::ResourceBodyFactSource,
    labels: &mut crate::surface::proof_diagnostics::render::MemoryStateLabels,
) -> String {
    let bindings = source
        .bindings
        .iter()
        .filter_map(|(name, value)| {
            let value = crate::surface::proof_diagnostics::render::render_program_value_labeled(
                value, labels,
            );
            (value != *name).then(|| format!("{name} = {value}"))
        })
        .collect::<Vec<_>>();
    if bindings.is_empty() {
        format!("`{}`", source.spelling)
    } else {
        format!("`{}` (with {})", source.spelling, bindings.join(", "))
    }
}

/// A note for a missing memory range that a held range over the same base
/// would cover if its bounds reached. The verdict compared the endpoints;
/// say which comparisons were not established, so `owns b[0..n]` against
/// `b[0..1]` reads as `1 <= n` (the held range may be empty) and against
/// `b[1..2]` as `2 <= n`, rather than as a resource the proof never held.
/// Both ranges are spelled against the parameter they index when one names
/// them, so a range whose base pointer already carries an offset is compared
/// with the held range at the same scale.
pub(super) fn describe_missing_range_end_note(
    error: &crate::kernel::RuntimeError,
    resource_facts: &[ResourceFact],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let crate::kernel::RuntimeError::MissingResource { resource } = error else {
        return String::new();
    };
    let Some(required) = resource
        .memory_own_range()
        .or_else(|| resource.memory_view_range())
    else {
        return String::new();
    };
    // When earlier requirements of the same call were reserved before this
    // one found no owner, what was compared is the caller's context after
    // those reservations, not before them: two requirements naming one cell
    // are refused although the caller's whole range covers each of them.
    let reservation = crate::kernel::owned_reservation_miss_for(resource);
    let (resource_facts, reserved_prefix) = match &reservation {
        Some(miss) => (
            miss.remaining.as_slice(),
            format!(
                "after reserving {} for an earlier requirement of this call, ",
                describe_bounded_list(&miss.reserved, |fact| format!(
                    "`{}`",
                    render_resource_fact_diagnostic(fact, parameter_binding)
                ))
            ),
        ),
        None => (resource_facts, String::new()),
    };
    let required_parameter = parameter_relative_base(required, parameter_binding);
    let byte_coordinates = required_parameter.as_ref().is_some_and(|(parameter, _)| {
        parameter.pointee_struct_layout().is_some()
            || parameter.struct_layout().is_some()
            || diagnostic_parameter_element_width(parameter) != i64::from(required.element_width())
    });
    // The scalar array field of the parameter's struct the required range
    // lies in, when it lies in one.
    let array_field = byte_coordinates
        .then(|| struct_byte_bounds(required, parameter_binding))
        .flatten()
        .and_then(|(_, layout, start, end)| {
            let field = scalar_array_field_indices(&layout, &start, &end)?
                .0
                .to_string();
            Some((layout, field))
        });
    // Endpoints of the held range and of the required one, on one scale.
    let comparable = |held: &MemoryRange| {
        // This repair describes signed arithmetic; native bounds need their own rule.
        if held.int32_bounds().is_none() || required.int32_bounds().is_none() {
            return None;
        }
        let held_index = if held.base() == required.base() {
            match &required_parameter {
                Some(_) => parameter_relative_base(held, parameter_binding)?.1,
                None => {
                    return Some((
                        held.start().clone(),
                        held.end().clone(),
                        required.start().clone(),
                        required.end().clone(),
                    ));
                }
            }
        } else {
            let (required_parameter, _) = required_parameter.as_ref()?;
            let (held_parameter, index) = parameter_relative_base(held, parameter_binding)?;
            if !std::ptr::eq(held_parameter, *required_parameter) {
                return None;
            }
            index
        };
        let (_, required_index) = required_parameter.as_ref()?;
        let (held_start, held_end) = parameter_relative_endpoints(&held_index, held);
        let (required_start, required_end) = parameter_relative_endpoints(required_index, required);
        let unit = if byte_coordinates {
            1
        } else {
            required.element_width()
        };
        let bounds = (
            rescale_range_index(&held_start, held.element_width(), unit)?,
            rescale_range_index(&held_end, held.element_width(), unit)?,
            rescale_range_index(&required_start, required.element_width(), unit)?,
            rescale_range_index(&required_end, required.element_width(), unit)?,
        );
        // Inside one array field the bounds compare as indices of that field,
        // as the clauses are written.
        let Some((layout, field)) = &array_field else {
            return Some(bounds);
        };
        let (held_field, held_start, held_end) =
            scalar_array_field_indices(layout, &bounds.0, &bounds.1)?;
        let (_, required_start, required_end) =
            scalar_array_field_indices(layout, &bounds.2, &bounds.3)?;
        (held_field == *field).then_some((held_start, held_end, required_start, required_end))
    };
    let coordinate_note = required_parameter
        .as_ref()
        .filter(|_| byte_coordinates && array_field.is_none())
        .map_or(String::new(), |(parameter, _)| {
            format!(" (byte offsets from `{}`)", parameter.name())
        });
    // A read-only range is not an ownership supplier even when its byte
    // footprint covers the store. Explain that concrete mode mismatch without
    // searching for a new proof or treating it as successful authorization.
    let access_note = if resource.is_own()
        && let Some(view) = resource_facts.iter().find(|fact| {
            let Some(held) = fact.memory_view_range() else {
                return false;
            };
            if held == required {
                return true;
            }
            comparable(held).is_some_and(|(hs, he, rs, re)| {
                match (hs.as_const(), he.as_const(), rs.as_const(), re.as_const()) {
                    (Some(hs), Some(he), Some(rs), Some(re)) => {
                        (hs as i32) <= rs as i32 && (re as i32) <= he as i32
                    }
                    _ => false,
                }
            })
        }) {
        format!(
            "\n  access check: {reserved_prefix}write ownership required; available `{}` covers the requested range but permits reading only",
            render_resource_fact_diagnostic(view, parameter_binding)
        )
    } else {
        String::new()
    };
    let candidates = resource_facts
        .iter()
        .filter_map(|fact| {
            let held = if resource.is_own() {
                fact.memory_own_range()
            } else {
                fact.memory_own_range().or_else(|| fact.memory_view_range())
            }?;
            let (held_start, held_end, required_start, required_end) = comparable(held)?;
            let mut sides = Vec::new();
            if held_start != required_start {
                sides.push((held_start, required_start));
            }
            if held_end != required_end {
                sides.push((required_end, held_end));
            }
            (!sides.is_empty()).then_some((fact, sides))
        })
        .collect::<Vec<_>>();
    // A held range that shares the needed start differs only in its end, the
    // closest miss; prefer it over one that differs on both sides.
    let Some((held_fact, sides)) = candidates
        .iter()
        .min_by_key(|(_, sides)| sides.len())
        .cloned()
    else {
        let range_note = match &reservation {
            Some(miss) => format!(
                "\n  note: {reserved_prefix}no remaining owner covers `{}`; remaining: {}",
                describe_memory_range(required, parameter_binding),
                describe_bounded_list(&miss.remaining, |fact| format!(
                    "`{}`",
                    render_resource_fact_diagnostic(fact, parameter_binding)
                ))
            ),
            None => String::new(),
        };
        return access_note + &range_note;
    };
    let decided = |lower: &MachineTerm, upper: &MachineTerm| {
        Some(lower.as_const()? as i32 <= upper.as_const()? as i32)
    };
    if sides
        .iter()
        .any(|(lower, upper)| decided(lower, upper) == Some(false))
    {
        let (lower, upper) = sides
            .iter()
            .find(|(lower, upper)| decided(lower, upper) == Some(false))
            .expect("found a refuted side above");
        return format!(
            "{access_note}\n  note: {reserved_prefix}held `{}` does not cover `{}`: `{} <= {}` is false{coordinate_note}",
            render_resource_fact_diagnostic(held_fact, parameter_binding),
            describe_memory_range(required, parameter_binding),
            describe_bitvector_with_context(lower, parameter_binding),
            describe_bitvector_with_context(upper, parameter_binding),
        );
    }
    let conditions = sides
        .iter()
        .filter(|(lower, upper)| decided(lower, upper).is_none())
        .map(|(lower, upper)| {
            format!(
                "`{} <= {}`",
                describe_bitvector_with_context(lower, parameter_binding),
                describe_bitvector_with_context(upper, parameter_binding),
            )
        })
        .collect::<Vec<_>>();
    if conditions.is_empty() {
        return access_note;
    }
    format!(
        "{access_note}\n  note: {reserved_prefix}held `{}` covers `{}` only when {}{coordinate_note}",
        render_resource_fact_diagnostic(held_fact, parameter_binding),
        describe_memory_range(required, parameter_binding),
        conditions.join(" and "),
    )
}

/// The state and pointer a still-unresolved comparison side loads from, if
/// that side is exactly one load. A resolved side is a value and reads
/// nothing.
/// The explanation for two evaluated sides that are reads of one address of
/// different kinds: a byte and a word, or a signed and an unsigned byte. They
/// are two values at any program point, so no step of the history explains
/// them apart, and a sentence about what changed in between would send the
/// reader after a store that is not the cause.
///
/// The two addresses are compared through `assumptions`, the proof context's
/// equality graph, when the caller has one: `(char *)q + i * 4` and `q[i]` are
/// spelled differently and are one address where `i * 4` does not wrap.
pub(in crate::surface) fn describe_load_kind_mismatch(
    left: &ProgramValue,
    right: &ProgramValue,
    parameter_binding: ParameterBinding<'_>,
    assumptions: Option<&crate::kernel::PureFactContext>,
) -> Option<String> {
    let (_, left_load) = unresolved_load(left)?;
    let (_, right_load) = unresolved_load(right)?;
    let left_kind = unresolved_load_kind(left)?;
    let right_kind = unresolved_load_kind(right)?;
    let same_address = left_load == right_load
        || assumptions.is_some_and(|facts| facts.addresses_known_equal(&left_load, &right_load));
    if !same_address || left_kind == right_kind {
        return None;
    }
    // Two spellings of one address may name it with different precision:
    // the byte offset `(char *)q + i * 4` names no element of `q`, while
    // `q[i]` does. Name it by the first spelling that names a whole cell.
    let cells = [&left_load, &right_load]
        .map(|load| describe_source_cell(load, parameter_binding).map(|cell| cell.text()));
    let named = match cells
        .iter()
        .flatten()
        .find(|text| !text.contains('…'))
        .or(cells[0].as_ref())
    {
        Some(text) => format!("`{text}`"),
        None => "one address".to_string(),
    };
    use crate::kernel::LoadKind;
    if matches!(
        (left_kind, right_kind),
        (LoadKind::Int8, LoadKind::UInt8) | (LoadKind::UInt8, LoadKind::Int8)
    ) {
        // One byte, one name: the signed read is the unsigned read's
        // two's-complement value, so the two agree exactly below 0x80.
        return Some(format!(
            "the two sides read {named} as different kinds of value, the left as {} and the right \
             as {}. They read the same byte, and its signed value is its unsigned value only \
             when the byte is below 0x80, so the two differ for every byte of 0x80 or more.",
            describe_load_kind(left_kind),
            describe_load_kind(right_kind),
        ));
    }
    Some(format!(
        "the two sides read {named} as different kinds of value, the left as {} and the right \
         as {}. A read's width and signedness are part of the value it names, so these are two \
         values at any point of the program.",
        describe_load_kind(left_kind),
        describe_load_kind(right_kind),
    ))
}

/// The kind of read a still-unresolved comparison side is, when that side is
/// exactly one load.
fn unresolved_load_kind(value: &ProgramValue) -> Option<crate::kernel::LoadKind> {
    if let ProgramValue::Int8(term) = value
        && let Some(unsigned) = term.signed_byte_operand()
    {
        return matches!(
            unresolved_load_kind(&ProgramValue::UInt8(unsigned.clone())),
            Some(crate::kernel::LoadKind::UInt8)
        )
        .then_some(crate::kernel::LoadKind::Int8);
    }
    let term = match value.numeric_value() {
        ProgramValue::Int8(term)
        | ProgramValue::Bool(term)
        | ProgramValue::Int16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term) => term,
        _ => return None,
    };
    match widened_word(term) {
        MachineTerm::MemoryLoad(_, _, kind) => Some(*kind),
        MachineTerm::Variable(variable) => {
            crate::kernel::registered_load_kind_for_variable(variable)
        }
        _ => None,
    }
}

/// A read's kind in the reader's words.
fn describe_load_kind(kind: crate::kernel::LoadKind) -> &'static str {
    use crate::kernel::LoadKind;
    match kind {
        LoadKind::Int8 => "a signed byte",
        LoadKind::UInt8 => "an unsigned byte",
        LoadKind::Int16 => "a signed two-byte integer",
        LoadKind::UInt16 => "an unsigned two-byte integer",
        LoadKind::Int32 | LoadKind::UInt32 => "a four-byte word",
        LoadKind::Bits64 => "an eight-byte word",
        LoadKind::Int128 => "a signed sixteen-byte integer",
        LoadKind::UInt128 => "an unsigned sixteen-byte integer",
        LoadKind::Float32 => "a `float32`",
        LoadKind::Float64 => "a `float64`",
    }
}

/// The word a narrow value widened into 32 bits has (rule K8, a relation): a promoted
/// read is still that read. Only the widening is read through; a σ keeps
/// its own node here, as a reinterpretation of the read.
fn widened_word(term: &MachineTerm) -> &MachineTerm {
    match term.narrow_widening32_operand() {
        Some((_, word)) => word,
        None => term,
    }
}

pub(super) fn unresolved_load(value: &ProgramValue) -> Option<(SharedMemory, Pointer)> {
    let term = match value.numeric_value() {
        // A signed byte read is the conversion of the byte's unsigned read,
        // so it reads that read's address.
        ProgramValue::Int8(term) => term.signed_byte_operand().unwrap_or(term),
        ProgramValue::Bool(term)
        | ProgramValue::Int16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term) => term,
        _ => return None,
    };
    let read = crate::kernel::scalar_read_observation(crate::kernel::MachineOperandView::Legacy(
        widened_word(term),
    ))?;
    Some((read.origin.unwrap_or(read.memory), read.pointer))
}

/// The model field a comparison side stands for, if that side is exactly one
/// model-field variable. A side that resolved to a value stands for nothing.
///
/// The registry the mint filled is the only route: the field value is stored
/// inside the instance fact, so the term carries no projection to read.
pub(super) fn unresolved_model_field(
    value: &ProgramValue,
) -> Option<crate::kernel::model_fields::ModelFieldOrigin> {
    let variable = crate::kernel::model_fields::algebraic_value_variable(
        &crate::kernel::AlgebraicValue::Program(value.clone()),
    )?;
    crate::kernel::model_fields::registered_model_field_origin(variable)
}

/// The explanation for one comparison side that is a model field: it reads the
/// outcome state's model, and the question is whether that is still the model
/// the earlier state held.
///
/// The two points are whole saved states, because a model field's version is
/// the value stored in the instance rather than a point on the memory history.
pub(super) fn describe_model_field_mismatch(
    value: &ProgramValue,
    here: &ExecutionState,
    there: &ExecutionState,
    since: &str,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let origin = unresolved_model_field(value)?;
    let explanation = resource_tracker::explain_at_states(
        resource_tracker::TrackedResource::ModelField {
            identity: origin.identity,
            children: &[],
            field_index: origin.field_index,
        },
        resource_tracker::StatePoint::at(here),
        resource_tracker::StatePoint::at(there),
    );
    describe_resource_version_mismatch(&explanation, since, &[], parameter_binding)
}

/// Names the write that stopped a comparison side from being carried across
/// the body: the step the resource tracker's walk stopped at, in the source
/// spelling, with what would settle it.
///
/// A parameter's memory and a file-scope array are separated by a resource
/// the contract holds or by a stated `separate`, never by their names, so a
/// contract that reads a range it declares no resource for is told which
/// write it has to rule out and how.
pub(super) fn describe_unseparated_write(
    value: &ProgramValue,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let (memory, load) = unresolved_load(value)?;
    let explanation = resource_tracker::explain_last_same(
        resource_tracker::TrackedResource::Cell {
            pointer: &load,
            bytes: crate::kernel::load_access_width_or_widest(&memory, &load),
        },
        &resource_tracker::VersionPoint::at(&memory),
    );
    describe_resource_version_mismatch(
        &explanation,
        "earlier in this function",
        &[],
        parameter_binding,
    )
    .map(|mismatch| format!("; {mismatch}"))
}

/// A `fold` field initializer that reads a model this state no longer holds.
///
/// `let c = fold(cell(p), { rank: c.rank })` after `unfold(c)` is the shape:
/// the `unfold` consumed the instance, so `c.rank` names no model at the
/// `fold`. The kernel reports only that the identity is absent — it has no
/// spelling for `c` — so the sentence is written here, where the reader's own
/// expression is at hand, and it prints the initializer that verifies.
///
/// Nothing is said unless the state really does not hold the field and the
/// entry state does: a repair is printed only where it works, and where
/// `old(..)` would name nothing either the text says so instead.
pub(super) fn describe_unheld_model_field_initializer(
    initializer: &ContractExpression,
    state: &ExecutionState,
    entry_state: &ExecutionState,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let access = unheld_model_field_access(initializer, state, false)?;
    // The instance identity a fold writes is the reader's binder, so the
    // registry's spelling is available here too; register it in case this
    // access is the first one lowered.
    crate::kernel::model_fields::register_instance_spelling(access.identity, &access.owner);
    let explanation = resource_tracker::explain_at_states(
        resource_tracker::TrackedResource::ModelField {
            identity: access.identity,
            children: &access.children,
            field_index: access.field_index,
        },
        resource_tracker::StatePoint::at(state),
        resource_tracker::StatePoint::at(entry_state),
    );
    describe_resource_version_mismatch(&explanation, "function entry", &[], parameter_binding)
}

/// The first model field in `expression` that `state` cannot resolve, skipping
/// the subtrees that resolve somewhere else: `old(..)` and `at(..)` read their
/// own state, so a field they name is not this state's to hold. A shape
/// this bounded walk does not enter contributes nothing, and then the caller
/// falls back to the kernel's own sentence rather than guessing.
fn unheld_model_field_access<'a>(
    expression: &'a ContractExpression,
    state: &ExecutionState,
    through_old: bool,
) -> Option<&'a ResourceFieldAccess> {
    let mut pending = vec![expression];
    while let Some(expression) = pending.pop() {
        match expression {
            ContractExpression::ResourceField(access) => {
                if state
                    .resource_instance_at_path(access.identity, &access.children)
                    .and_then(|instance| instance.fields().get(access.field_index))
                    .is_none()
                {
                    return Some(access);
                }
            }
            // A loop invariant reads `old(..)` at the loop's entry, which is
            // the state it is checked against, so there it is not a state
            // of its own.
            ContractExpression::Old(inner) if through_old => pending.push(inner),
            ContractExpression::Old(_) | ContractExpression::At { .. } => {}
            ContractExpression::Negate(inner)
            | ContractExpression::BitwiseNot(inner)
            | ContractExpression::Field { base: inner, .. }
            | ContractExpression::ArrayIndex { base: inner, .. } => pending.push(inner),
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right)
            | ContractExpression::Divide(left, right)
            | ContractExpression::Remainder(left, right)
            | ContractExpression::ShiftLeft(left, right)
            | ContractExpression::RustShiftLeft(left, right)
            | ContractExpression::ShiftRight(left, right)
            | ContractExpression::RustShiftRight(left, right)
            | ContractExpression::BitwiseAnd(left, right)
            | ContractExpression::BitwiseOr(left, right)
            | ContractExpression::BitwiseXor(left, right)
            | ContractExpression::Index(left, right)
            | ContractExpression::SequenceConcat(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            ContractExpression::AlgebraicConstructor { arguments, .. }
            | ContractExpression::Call { arguments, .. } => pending.extend(arguments),
            ContractExpression::SequenceLiteral(elements) => pending.extend(elements),
            // Every other shape either names no model field or reaches one
            // only through a form this bounded walk does not enter.
            _ => {}
        }
    }
    None
}

/// The refusal for a proposition that reads a field of a resource instance
/// `state` does not hold. Advice follows the checked consumption and field
/// type: an unfold pattern can bind only C fields, while an algebraic match
/// can retain constructor payloads before an instance is consumed.
///
/// `through_old` also reads fields under `old(..)`, for a loop invariant,
/// whose `old(..)` names the loop's entry state rather than the function's.
pub(in crate::surface) fn describe_consumed_instance_field_read(
    proposition: &ClickProposition,
    state: &ExecutionState,
    through_old: bool,
) -> Option<String> {
    let mut pending = vec![proposition];
    let mut expressions = Vec::new();
    while let Some(proposition) = pending.pop() {
        match proposition {
            ClickProposition::Comparison { left, right, .. } => {
                expressions.push(left);
                expressions.push(right);
            }
            ClickProposition::FloatClassification { expression, .. }
            | ClickProposition::Defined { expression } => expressions.push(expression),
            ClickProposition::Not(inner)
            | ClickProposition::ForAll { body: inner, .. }
            | ClickProposition::Exists { body: inner, .. } => pending.push(inner),
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            ClickProposition::RangeAll {
                start, end, body, ..
            }
            | ClickProposition::RangeAny {
                start, end, body, ..
            } => {
                expressions.push(start);
                expressions.push(end);
                pending.push(body);
            }
            ClickProposition::PredicateCall { arguments, .. } => expressions.extend(arguments),
            // A state proposition reads its own state.
            ClickProposition::At { .. }
            | ClickProposition::ChangesOnly { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::ResourceViewable { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. } => {}
        }
    }
    let access = expressions
        .into_iter()
        .find_map(|expression| unheld_model_field_access(expression, state, through_old))?;
    if !access.children.is_empty() {
        return None;
    }
    let owner = &access.owner;
    let field = &access.field;
    let cause = state.resources().instance_consumption(access.identity);
    let advice = match cause {
        Some(crate::kernel::InstanceConsumption::Unfold) => match &access.click_type {
            Some(ClickType::Program(_)) => format!(
                "`unfold({owner})` consumed it; name the field's folded value where the instance is \
                 unfolded with `let {{ {field}: name }} = unfold({owner});` and write `name` instead"
            ),
            Some(ClickType::Algebraic(_)) => format!(
                "`unfold({owner})` consumed it; an unfold pattern cannot bind an algebraic field. \
                 Match `{owner}.{field}` before the unfold and retain its constructor payloads \
                 in proof bindings; there is no unfold-pattern binding for the whole model"
            ),
            _ => format!(
                "`unfold({owner})` consumed it; no unfold-pattern binding exists for this field's \
                 logical type"
            ),
        },
        Some(crate::kernel::InstanceConsumption::FoldChild { parent, slot }) => {
            let parent = crate::kernel::model_fields::registered_instance_spelling(*parent);
            match parent {
                Some(parent) if matches!(access.click_type, Some(ClickType::Algebraic(_))) => {
                    format!(
                        "it was consumed as child `{slot}` when `{parent}` was folded. \
                     Where the held parent's model carries the child's model, match it before \
                     the loop and retain that payload in a proof binding; use that binding \
                     in the invariant. Otherwise retain the value before folding the parent"
                    )
                }
                Some(parent) => format!(
                    "it was consumed as child `{slot}` when `{parent}` was folded. \
                     Retain the field value before folding the parent; an unfold pattern at \
                     this point cannot bind a consumed child's field"
                ),
                None => format!(
                    "it was consumed as child `{slot}` of a folded parent. \
                     Retain the field value before that fold; no unfold-pattern binding can \
                     recover it at this point"
                ),
            }
        }
        None => "no checked fold or unfold of this instance is recorded here; \
                 no held field value is available to bind"
            .to_string(),
    };
    Some(format!(
        "`{owner}.{field}` reads a field of `{owner}`, which is not held here; {advice}"
    ))
}

/// Reads at different addresses in one state need an address or value
/// equality, not a framing condition. Materialization may expose this directly
/// by giving both reads their original memory identity.
pub(super) fn describe_read_address_mismatch(
    left: &ProgramValue,
    right: &ProgramValue,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let (left_memory, left_load) = unresolved_load(left)?;
    let (right_memory, right_load) = unresolved_load(right)?;
    if left_load == right_load || left_memory.read_identity() != right_memory.read_identity() {
        return None;
    }
    let left = describe_source_cell(&left_load, parameter_binding)?;
    let right = describe_source_cell(&right_load, parameter_binding)?;
    Some(format!(
        "`{}` and `{}` read the same recorded memory using different address expressions. \
         Establish the index/address relation or the equality of those values.",
        left.text(),
        right.text(),
    ))
}

/// The explanation for two evaluated sides that read one address at two
/// program points.
pub(super) fn describe_two_sided_version_mismatch(
    left: &ProgramValue,
    right: &ProgramValue,
    left_point: &str,
    right_point: &str,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let (left_memory, left_load) = unresolved_load(left)?;
    let (right_memory, right_load) = unresolved_load(right)?;
    if left_load != right_load {
        return None;
    }
    if let Some(mismatch) = describe_load_kind_mismatch(left, right, parameter_binding, None) {
        return Some(mismatch);
    }
    let explanation = resource_tracker::explain(
        resource_tracker::TrackedResource::Cell {
            pointer: &left_load,
            bytes: crate::kernel::load_access_width_or_widest(&left_memory, &left_load),
        },
        &resource_tracker::VersionPoint::at(&left_memory),
        &resource_tracker::VersionPoint::at(&right_memory),
    );
    // Both labels name real program points, so the sentence is written
    // against the earlier of the two: that is the one the value may have
    // changed *since*.
    let since = if explanation.there_is_earlier() {
        right_point
    } else {
        left_point
    };
    describe_resource_version_mismatch(&explanation, since, &[], parameter_binding)
}

/// The explanation for a goal and an available fact that spell alike and
/// differ only in which version they read, or for one proposition that reads
/// one resource at two program points.
/// `premise_point` names, as the reader would, the place the matching fact was
/// stated; the text says the resource may have changed since then.
pub(super) fn describe_proposition_version_mismatch(
    goal: &Proposition,
    premises: &[&Proposition],
    premise_point: &str,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    describe_proposition_version_mismatch_explained(
        goal,
        premises,
        premise_point,
        parameter_binding,
    )
    .map(|(message, _)| message)
}

/// [`describe_proposition_version_mismatch`] with the explanation it
/// describes, so a caller can add what its own path recorded about the
/// blocking step without walking the history again.
pub(super) fn describe_proposition_version_mismatch_explained(
    goal: &Proposition,
    premises: &[&Proposition],
    premise_point: &str,
    parameter_binding: ParameterBinding<'_>,
) -> Option<(String, resource_tracker::Explanation)> {
    let (explanation, internal) =
        proposition_version_explanation(goal, premises, parameter_binding)?;
    let message = describe_resource_version_mismatch(
        &explanation,
        if internal {
            "the memory state the other side reads"
        } else {
            premise_point
        },
        premises,
        parameter_binding,
    )?;
    Some((message, explanation))
}

/// The statement whose store dropped `cell`, and the index disequality the
/// implicit tail's store search spelled and could not prove before it.
/// `fact` is that search's own spelling; the cell is spelled as the history
/// explanation spells it, and is left unnamed where that has no spelling.
pub(in crate::surface) fn describe_store_separation_miss(
    statement: &str,
    cell: Option<&str>,
    fact: &str,
) -> String {
    let overwritten = cell
        .map(|cell| format!("`{cell}`"))
        .unwrap_or_else(|| "the cell this goal reads".to_string());
    format!(
        "{statement} may have overwritten {overwritten}; it is kept if you state \
         `have {fact} by {{ ... }};` before {statement}"
    )
}

/// `pointer`'s cell as the C locals of `state` spell it (`q[0]` through a
/// pointer local `q`), the way a memory-history explanation spells a cell
/// through the function's parameters.
pub(in crate::surface) fn describe_source_cell_at_state(
    pointer: &Pointer,
    state: &ExecutionState,
) -> Option<String> {
    let (parameters, arguments) = local_naming_tables(state);
    describe_source_cell(pointer, ParameterBinding::new(&parameters, &arguments))
        .map(|cell| cell.text())
}

/// Recover the bounded history comparison without discarding its exact addresses.
/// The terminal report can then use the same label map as its goal and facts.
pub(crate) fn proposition_version_explanation(
    goal: &Proposition,
    premises: &[&Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> Option<(resource_tracker::Explanation, bool)> {
    // A goal that reads no resource has no version to differ about. Deciding
    // that first keeps this diagnostic, and the tracker's walk, off the
    // failure path of every proof that never touches memory.
    if !resource_tracker::reads_any_resource(goal) {
        return None;
    }
    if let Some((resource, here, there)) = resource_tracker::internal_version_mismatch(goal) {
        let explanation = resource_tracker::explain(resource.as_resource(), &here, &there);
        return Some((explanation, true));
    }
    // The structural question — do these two read the same resources at
    // different points — is asked first, so only a premise that answers it
    // is rendered and compared as text.
    let (resource, here, there) = premises
        .iter()
        .filter(|premise| **premise != goal)
        .find_map(|premise| {
            let mismatch = resource_tracker::version_mismatch(goal, premise)?;
            // Compare shapes without their construction legends. Each side
            // gets fresh local labels; differing state derivations belong
            // to the explanation, not this diagnostic shape comparison.
            let shape = |fact: &Proposition| {
                // The typed notation with fresh labels spells two reads of
                // one place alike whatever memory each reads, which is the
                // shape this compares.
                let _typed = crate::surface::proof_diagnostics::render::TypedNotationScope::enter();
                let mut labels =
                    crate::surface::proof_diagnostics::render::MemoryStateLabels::naming(
                        parameter_binding,
                    );
                crate::surface::proof_diagnostics::render::render_proposition_labeled(
                    fact,
                    &mut labels,
                )
            };
            (shape(premise) == shape(goal)).then_some(mismatch)
        })?;
    let explanation = resource_tracker::explain(resource.as_resource(), &here, &there);
    Some((explanation, false))
}

/// One user-grade explanation of "these two same-looking terms read different
/// versions of a resource", used by every refusal whose real cause is that,
/// so the wording is identical wherever it is met.
///
/// `since` names, in the reader's own terms, the earlier of the two points
/// the question was about: "function entry", "the start of this iteration", a
/// `mark` label, or the place a fact was stated. The text picks the case that
/// applies, spells the resource and the blocking step with the caller's names,
/// and prints the concrete clause that would settle *that* case — an index
/// inequality for two indexes into one array, a filled-in `separate(..)` for
/// two objects nothing separates. A repair is printed only where it is known
/// to work; where none does, the text says what is missing instead. It prints
/// no memory contents: the structured report labels the blocking state and
/// both addresses separately. Later steps are recorded memory transitions.
pub(super) fn describe_resource_version_mismatch(
    explanation: &resource_tracker::Explanation,
    since: &str,
    stated: &[&Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let (at, stop) = explanation.outcome.blocking_step()?;
    if stop.reason == resource_tracker::StopReason::HistoryEnds {
        return Some(format!(
            "the recorded execution does not connect {since} to here."
        ));
    }
    let mut message = match &explanation.resource {
        resource_tracker::OwnedResource::Block(block) => {
            describe_block_fact_stop(block, &stop.change, parameter_binding)
        }
        resource_tracker::OwnedResource::Cell { pointer, bytes } => describe_cell_version_stop(
            pointer,
            AccessWidths {
                read: *bytes,
                store: recorded_store_byte_width(at),
            },
            stop,
            since,
            stated,
            parameter_binding,
        ),
        // No term names a memory footprint, so no goal or premise a refusal
        // compares reads one. There is nothing to say rather than something
        // vague to say.
        resource_tracker::OwnedResource::Ranges(_) | resource_tracker::OwnedResource::AnyMemory => {
            return None;
        }
        resource_tracker::OwnedResource::ModelField {
            identity,
            children,
            field_index,
        } => describe_model_field_version_stop(*identity, children, *field_index, stop, since)?,
    };
    if explanation.crossed_after > 0 {
        message.push_str(" The subsequent recorded memory transitions preserve this resource.");
    }
    if !matches!(
        explanation.resource,
        resource_tracker::OwnedResource::ModelField { .. }
    ) {
        message.push_str("\n  supplemental history explanation: This diagnostic checks recorded memory history without using the proof context's equality and ownership facts.");
    }
    Some(message)
}

/// One model field, and the step that replaced the model it belongs to.
///
/// The field is spelled from the registry the mint filled, so this says
/// `c.rank`; where either half of that name is unknown there is nothing to say,
/// because a half-spelled field would read like source the reader could search
/// for.
fn describe_model_field_version_stop(
    identity: Variable,
    children: &[String],
    field_index: usize,
    stop: &resource_tracker::Stop,
    since: &str,
) -> Option<String> {
    let field = crate::kernel::model_fields::instance_field_spelling(identity, field_index)?;
    // A parent-qualified path is not what the registry names, so it has no
    // spelling of its own and this says nothing rather than the parent's.
    if !children.is_empty() {
        return None;
    }
    let owner = crate::kernel::model_fields::registered_instance_spelling(identity)?;
    let promise = format!("`ensures {field} == old({field})`");
    Some(match &stop.change {
        // A value only this state has lost can still be named where it was
        // held. One neither point holds can be named nowhere, and then the
        // text says what is missing instead of a repair that would not work.
        resource_tracker::Change::NotHeld {
            missing_there: false,
            ..
        } => format!(
            "`{field}` names no model here: `{owner}` was consumed since {since}, so this state \
             holds no field to read. Name the value it had there, `old({field})`."
        ),
        resource_tracker::Change::NotHeld { .. } => format!(
            "`{field}` names no model here, and none at {since} either: nothing holds `{owner}` at \
             either point, so `old({field})` names nothing to fall back on."
        ),
        resource_tracker::Change::ModelReplaced { by } => {
            let cause = match by {
                Some(crate::kernel::model_fields::ModelMint::CallReturn { callee }) => format!(
                    "the call to `{callee}` returned ownership of `{owner}` with a new model, and \
                     `{callee}` promises nothing about this field. If it keeps the field, state \
                     {promise} on `{callee}`."
                ),
                Some(crate::kernel::model_fields::ModelMint::Produced { callee }) => format!(
                    "the call to `{callee}` produced `{owner}`, so its model is fresh here. Only \
                     an {promise} on `{callee}` relates it to an earlier one."
                ),
                Some(crate::kernel::model_fields::ModelMint::LoopHead) => format!(
                    "the loop owns `{owner}`, and a loop head is an arbitrary visit, so it gives \
                     `{owner}` a fresh model. If the body keeps the field, carry it through as \
                     `invariant {field} == old({field});`."
                ),
                Some(crate::kernel::model_fields::ModelMint::Join) => format!(
                    "a join's `ensuring` names `{owner}`, and its arms may leave it with \
                     different models, so the join gives `{owner}` a fresh one. State what the \
                     arms agree on as a `fact` in that `ensuring`."
                ),
                Some(crate::kernel::model_fields::ModelMint::Refinement) => format!(
                    "contract/implementation refinement gave `{owner}` an arbitrary model, so only \
                     what both sides state relates the two."
                ),
                // The entry model is the old version, never the replacement,
                // so it is not a cause; `replacing_change` skips it.
                Some(crate::kernel::model_fields::ModelMint::ContractEntry) | None => format!(
                    "the two states store different models for `{owner}`, and no step here says \
                     which replaced which. State {promise} wherever the model is replaced."
                ),
            };
            format!("`{field}` may have changed since {since}: {cause}")
        }
        // A model field's answer is never a memory step: `same_at_states` is
        // the only route to one, and it produces the two arms above.
        _ => return None,
    })
}

/// A fact about a whole array. The block walk crosses only a step the kernel
/// proves leaves the object alone, and it reads no stated separation at all,
/// so this case has no `separate(..)` to offer and says so rather than
/// sending the reader to write one.
fn describe_block_fact_stop(
    block: &PointerBlock,
    change: &resource_tracker::Change,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let named = describe_memory_block(block, parameter_binding)
        .map(|name| format!("`{name}`"))
        .unwrap_or_else(|| "this array".to_string());
    format!(
        "a fact about {named} as a whole does not carry across {}. Only a step the kernel proves \
         leaves the whole object alone carries one, and a stated `separate(...)` is not read here.",
        describe_step(change, parameter_binding)
    )
}

/// The two access widths a separation question is really about, carried to
/// the renderer beside the two addresses.
///
/// Separation is a question about bytes, not addresses
/// (`docs/internals/resource-tracker.md`, "The byte question, which is not one
/// of them"), so a refusal that names only the addresses names half of what
/// was compared. `read` is the width the resource was asked about with, and
/// may be the widest scalar where the load recorded none — over-stating it can
/// only withhold a repair, never invent one. `store` is exact where it is
/// present: it is read off the recorded edge, which carries the value.
#[derive(Clone, Copy)]
struct AccessWidths {
    read: u32,
    store: Option<u32>,
}

/// How many bytes the blocking step wrote.
///
/// `Change::Store` keeps the address and drops the width, and the width is
/// the whole byte question, so it is read back off the recorded edge the walk
/// stopped below — the same edge the tracker classified. `None` for every
/// other step, and for a point that records no edge at all.
fn recorded_store_byte_width(at: Option<&resource_tracker::VersionPoint>) -> Option<u32> {
    match at?.shared_memory().derivation()?.as_ref() {
        crate::kernel::MemoryDerivation::Store { value, .. } => {
            Some(value.program_type().byte_width())
        }
        _ => None,
    }
}

/// One cell, and the step that ended the stretch its version was known over.
fn describe_cell_version_stop(
    pointer: &Pointer,
    widths: AccessWidths,
    stop: &resource_tracker::Stop,
    since: &str,
    stated: &[&Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let cell = describe_source_cell_of_width(pointer, Some(widths.read), parameter_binding);
    // Without the C names — a pure theorem has none — the address has no
    // source spelling, so the sentence says "this read" rather than repeating
    // a verifier-owned one.
    let named = match &cell {
        Some(cell) => format!("`{}`", cell.text()),
        None => "this read".to_string(),
    };
    if let resource_tracker::Change::CellsSeeded { pointer: recorded } = &stop.change {
        let recorded = describe_source_cell(recorded, parameter_binding)
            .map(|cell| format!("`{}`", cell.text()))
            .unwrap_or_else(|| "another cell".to_string());
        return format!(
            "{named} is not yet related to {recorded}, whose range contents were recorded. \
             The recording alone does not identify a source write. Establish the index/address \
             relation or preservation needed to compare these reads."
        );
    }
    let certain = stop.reason == resource_tracker::StopReason::Affected;
    let changed = if certain {
        "changed"
    } else {
        "may have changed"
    };
    format!(
        "{named} {changed} since {since}: {}",
        describe_cell_cause(
            cell.as_ref(),
            widths,
            stop,
            certain,
            stated,
            parameter_binding
        )
    )
}

/// Why this cell's chain broke, and the clause that would mend it.
fn describe_cell_cause(
    cell: Option<&SourceCell>,
    widths: AccessWidths,
    stop: &resource_tracker::Stop,
    certain: bool,
    stated: &[&Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    match &stop.change {
        resource_tracker::Change::Store { pointer } => {
            describe_store_cause(cell, pointer, widths, certain, stated, parameter_binding)
        }
        resource_tracker::Change::CellsSeeded { .. } => {
            "range contents were recorded; establish the index/address relation or preservation needed \
             to compare these reads."
                .to_string()
        }
        resource_tracker::Change::Call { ranges } => {
            describe_havoc_cause("the call in between", cell, ranges, parameter_binding)
        }
        resource_tracker::Change::Loop {
            ranges: Some(ranges),
        } => describe_havoc_cause("the loop in between", cell, ranges, parameter_binding),
        resource_tracker::Change::Loop { ranges: None } => {
            "the loop in between may have written it. The loop declares no write set, so nothing \
             can be shown separate from it: carry the fact through it as an invariant instead."
                .to_string()
        }
        resource_tracker::Change::Free { allocation } => {
            match describe_memory_block(&allocation.block, parameter_binding) {
                Some(freed) => format!(
                    "the allocation at `{freed}` was released in between, and nothing shows it \
                     separate from this cell."
                ),
                None => {
                    "an allocation was released in between, and nothing shows it separate from \
                     this cell."
                        .to_string()
                }
            }
        }
        resource_tracker::Change::ContractRetirement { allocation } => {
            match describe_memory_block(&allocation.block, parameter_binding) {
                Some(retired) => format!(
                    "the contract in between may have released the allocation at `{retired}`."
                ),
                None => "the contract in between may have released this allocation.".to_string(),
            }
        }
        resource_tracker::Change::Allocation { .. } => {
            "an allocation in between made this storage live.".to_string()
        }
        resource_tracker::Change::AllocationPending => {
            "an allocation in between has no resolved address yet.".to_string()
        }
        resource_tracker::Change::ContractAllocationClaims => {
            "a contract's allocation claims moved in between.".to_string()
        }
        resource_tracker::Change::Declaration { .. } => {
            "a declaration in between added storage to the state.".to_string()
        }
        resource_tracker::Change::LifetimeEnd { .. } => {
            "a local's lifetime ended in between.".to_string()
        }
        resource_tracker::Change::ObjectInitializationRecorded => {
            "a step in between recorded initialized bytes.".to_string()
        }
        resource_tracker::Change::BranchJoin => "branch memory join".into(),
        resource_tracker::Change::CellObserved => {
            "a step in between cached a read observation.".to_string()
        }
        resource_tracker::Change::CellsForgotten => {
            "a step in between dropped the cell values it had cached.".to_string()
        }
        resource_tracker::Change::BeginningOfHistory => {
            "the recorded execution reaches no further back.".to_string()
        }
        // A cell's change is always a recorded memory step, so the two
        // saved-state changes are unreachable for this resource; saying that
        // plainly beats inventing a cause.
        resource_tracker::Change::ModelReplaced { .. } | resource_tracker::Change::NotHeld { .. } => {
            "no recorded step in between names this cell.".to_string()
        }
    }
}

/// A store, and the fact that would tell it apart from this cell: an index
/// inequality when both address one array, a filled-in `separate(..)` when
/// they address two objects. Both are printed with the reader's own terms,
/// and only when the terms are the reader's — an index the lowering owns is
/// spelled `a[…]`, and no inequality is proposed over a name nobody wrote.
///
/// An index inequality is offered only where the indexes really are the
/// undecided part. A store wider than the array's element reaches past the
/// element it names, so differing indexes do not separate it from the
/// neighbour it covers, and asking for `i != j` there sends the reader to
/// state a premise that will not close the goal. That case is answered by
/// [`describe_wide_store_byte_reach`] instead.
fn describe_store_cause(
    cell: Option<&SourceCell>,
    written: &Pointer,
    widths: AccessWidths,
    certain: bool,
    stated: &[&Proposition],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let store = describe_source_cell_of_width(written, widths.store, parameter_binding);
    if certain {
        return match &store {
            Some(store) => format!("the store to `{}` wrote it.", store.text()),
            None => "a store in between wrote it.".to_string(),
        };
    }
    let (Some(cell), Some(store)) = (cell, &store) else {
        // A read through a pointer the function received rather than an object
        // it names has no source spelling, so only one side can be printed.
        // Printing the store is still the whole content of the answer: it is
        // the step the reader has to separate their read from.
        return match &store {
            Some(store) => format!(
                "the memory-history check could not establish that the store to `{}` is separate \
                 from this read.",
                store.text()
            ),
            None => "the memory-history check could not establish that an intervening store is separate \
                     from this read."
                .to_string(),
        };
    };
    if matches!(cell.index, CellIndex::StructMember)
        || matches!(store.index, CellIndex::StructMember)
    {
        // A field is a cell place, not a pointer base with an unknown array
        // index. In particular, two members of one struct array must not be
        // described as unrelated pointer parameters that need separating.
        return format!(
            "the store to `{}` may have written `{}`. Establish that the two accesses touch separate bytes.",
            store.text(),
            cell.text(),
        );
    }
    if cell.object == store.object {
        return describe_same_object_store_cause(cell, store, widths, stated);
    }
    let repair = match (cell.element_range(), store.element_range()) {
        (Some(read), Some(written)) => format!(" {}", spelled_separation_repair(&read, &written)),
        _ => format!(
            " If they are separate, require a `separate(memory({}[…]), memory({}[…]))` between \
             them.",
            cell.object, store.object
        ),
    };
    format!(
        "the store to `{}` may have written it, because `{}` may point into `{}`.{repair}",
        store.text(),
        cell.object,
        store.object
    )
}

/// A read and a store that address one object, where the only thing that can
/// tell them apart is where they sit inside it.
///
/// The byte question is asked before the address one: a store the reader
/// cannot separate by index at all must not be answered with an index
/// inequality. Where the store fits inside the element it names, the indexes
/// really are the undecided part and the inequality is the answer.
fn describe_same_object_store_cause(
    cell: &SourceCell,
    store: &SourceCell,
    widths: AccessWidths,
    stated: &[&Proposition],
) -> String {
    match (cell.named_index(), store.named_index()) {
        (Some(read), Some(written)) if read != written => {
            if let Some(byte_reach) =
                describe_wide_store_byte_reach(cell, store, read, written, widths)
            {
                return byte_reach;
            }
            if let (Some(read_term), Some(written_term)) = (&cell.index_term, &store.index_term)
                && states_terms_differ(stated, read_term, written_term)
            {
                return format!(
                    "the store to `{}` may have written it. `{read} != {written}` is already \
                     available, so stating it again will not help.",
                    store.text()
                );
            }
            format!(
                "the store to `{}` may have written it. If `{read}` and `{written}` differ, state \
                 `{read} != {written}`.",
                store.text()
            )
        }
        (Some(read), _) => format!(
            "the store to `{}` may have written it. The memory-history check did not establish that its index differs from \
             `{read}`.",
            store.text()
        ),
        _ => format!(
            "the store to `{}` may have written it, and the memory-history check did not establish that the indexes differ.",
            store.text()
        ),
    }
}

/// Whether a fact states that two index terms differ, as `i != j` lowers:
/// their equality is false. Operand order is not significant.
fn states_terms_differ(stated: &[&Proposition], left: &MachineTerm, right: &MachineTerm) -> bool {
    stated.iter().any(|fact| {
        let Proposition::ConditionIs(condition, false) = fact else {
            return false;
        };
        matches!(
            condition.as_bitvector_comparison(),
            Some((
                crate::kernel::BitvectorComparisonOp::Compare(
                    _,
                    crate::kernel::CompareRelation::Equal
                ),
                a,
                b,
            )) if (a == left && b == right) || (a == right && b == left)
        )
    })
}

/// Exact named cell for a diagnostic. Never offer a verifier-owned index as
/// a source expression.
pub(in crate::surface) fn diagnostic_source_cell(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let cell = describe_source_cell(pointer, parameter_binding)?;
    (!cell.object.starts_with("__rust_") && !matches!(cell.index, CellIndex::Unnamed))
        .then(|| cell.text())
}

pub(in crate::surface) fn diagnostic_model_load_cell(
    pointer: &Pointer,
    kind: crate::kernel::LoadKind,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    if let Some((cell, value_type)) = cpp_model::describe_model_field_at(pointer, parameter_binding)
        && crate::kernel::LoadKind::of_type(value_type).is_some_and(|read| read.reads_word_of(kind))
    {
        return Some(cell);
    }
    None
}

/// A scalar read from a by-value parameter's input object. Its carrier is
/// byte-typed, so its field layout, rather than its pointee type, determines
/// which source place the read names.
pub(in crate::surface) fn diagnostic_aggregate_parameter_load_cell(
    pointer: &Pointer,
    kind: crate::kernel::LoadKind,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        if !parameter.is_struct_value() {
            continue;
        }
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        let Some(offset) = diagnostic_pointer_element_index_from_base(pointer, base.pointer(), 1)
            .and_then(|offset| offset.as_const())
        else {
            continue;
        };
        let Some(layout) = parameter.struct_layout() else {
            continue;
        };
        let mut fields = layout.typed_leaf_fields().filter(|(_, at, ty)| {
            *at == offset
                && crate::kernel::LoadKind::of_type(ty.to_kernel_type())
                    .is_some_and(|read| read.reads_word_of(kind))
        });
        if let (Some((field, _, _)), None) = (fields.next(), fields.next()) {
            return Some(format!("{}.{field}", parameter.name()));
        }
    }
    None
}

pub(in crate::surface) fn diagnostic_source_load_cell(
    pointer: &Pointer,
    kind: crate::kernel::LoadKind,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    // A read of exactly one scalar field of a struct-typed global or local
    // is that field, `g.b`.
    if let (PointerOffsetTerm::Constant(offset), PointerBlock::Concrete(block)) =
        (&pointer.offset, &pointer.block)
        && let Ok(offset) = u32::try_from(*offset)
        && let Some(field) = object_fields::object_field_spelling(block, offset, kind.byte_width())
    {
        return Some(field);
    }
    let cell = describe_source_cell(pointer, parameter_binding)?;
    (cell.element_bytes == Some(kind.byte_width()) && !matches!(cell.index, CellIndex::Unnamed))
        .then(|| cell.text())
}

/// A pointer-valued field at exactly this address. Keep the field's type
/// check here: the internal pointer-read registry uses a scalar carrier whose
/// load kind alone does not describe the source C type.
pub(in crate::surface) fn diagnostic_source_pointer_cell(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    base_point: Option<&str>,
) -> Option<String> {
    if let Some((cell, value_type)) = cpp_model::describe_model_field_at(pointer, parameter_binding)
        && value_type.is_pointer()
    {
        return Some(base_point.map_or(cell.clone(), |point| format!("at({point}, {cell})")));
    }
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        let Some(layout) = parameter
            .pointee_struct_layout()
            .or_else(|| parameter.struct_layout())
        else {
            continue;
        };
        let mut fields = layout.fields().iter().filter(|(_, field)| {
            let expected = base.pointer().offset_by_bytes(field.offset_bytes());
            expected.block == pointer.block
                && crate::kernel::offsets_have_same_canonical_form(
                    &expected.offset,
                    &pointer.offset,
                )
        });
        if let (Some((name, field)), None) = (fields.next(), fields.next())
            && field.interface_type().is_pointer()
        {
            let base = base_point.map_or_else(
                || parameter.name().to_string(),
                |point| format!("at({point}, {})", parameter.name()),
            );
            return Some(describe_field_place(&base, name));
        }
    }
    None
}

/// The source spelling [`describe_source_cell`] gives an address, for the
/// surface tests.
#[cfg(test)]
pub(in crate::surface) fn source_cell_text_for_tests(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    describe_source_cell(pointer, parameter_binding).map(|cell| cell.text())
}

/// [`describe_same_object_store_cause`] driven from the surface tests with
/// the plain data the byte question is asked with: one object, the two
/// element spellings, and the three widths. The renderer's own types stay
/// private; this is the shape a test can state a case in.
#[cfg(test)]
pub(in crate::surface) fn store_cause_between_indexes_for_tests(
    object: &str,
    read_index: &str,
    written_index: &str,
    element_bytes: Option<u32>,
    read_bytes: u32,
    store_bytes: Option<u32>,
) -> String {
    store_cause_between_indexes_with_facts_for_tests(
        object,
        (read_index, None),
        (written_index, None),
        element_bytes,
        read_bytes,
        store_bytes,
        &[],
    )
}

/// [`store_cause_between_indexes_for_tests`] with each index's kernel term
/// and the facts the refusal may consult.
#[cfg(test)]
pub(in crate::surface) fn store_cause_between_indexes_with_facts_for_tests(
    object: &str,
    read_index: (&str, Option<MachineTerm>),
    written_index: (&str, Option<MachineTerm>),
    element_bytes: Option<u32>,
    read_bytes: u32,
    store_bytes: Option<u32>,
    stated: &[&Proposition],
) -> String {
    let spelled = |(index, index_term): (&str, Option<MachineTerm>)| SourceCell {
        object: object.to_string(),
        index: CellIndex::Named(index.to_string()),
        element_bytes,
        index_term,
    };
    describe_same_object_store_cause(
        &spelled(read_index),
        &spelled(written_index),
        AccessWidths {
            read: read_bytes,
            store: store_bytes,
        },
        stated,
    )
}

/// The refusal for a store whose *bytes* reach this cell, as opposed to one
/// whose *address* is merely undecided. `None` where the store fits inside
/// the element it names, which is the case the index inequality answers.
///
/// A store wider than the array's element covers the element it names and the
/// ones above it, so `i != j` leaves `i == j + 1` open and states a premise
/// that does not close the goal. What does separate them is the rule
/// `one_element_gap_separates_bytes` runs
/// (`src/kernel/reasoning/memory_resolution.rs`): an address ladder
/// establishes a gap of one element, a bare disequality leaves the direction
/// open so both accesses must fit in it, and a strict order fixes the
/// direction so only the *lower* access must — the upper one extends away
/// from the gap. So the repair is the strict order that puts the read below
/// the store, and it is printed only where the read fits in one element,
/// because that is the only case the rule clears. Where the read is wider
/// than an element too — including where its width is the widest-scalar
/// fallback rather than a recorded one — no order is offered and the text
/// says what an order would have to establish.
fn describe_wide_store_byte_reach(
    cell: &SourceCell,
    store: &SourceCell,
    read_index: &str,
    written_index: &str,
    widths: AccessWidths,
) -> Option<String> {
    let element = cell.element_bytes.filter(|bytes| *bytes > 0)?;
    // One object is one element width; comparing the two spellings is cheap
    // insurance against a pair that reached here through different bases.
    if store.element_bytes != cell.element_bytes {
        return None;
    }
    let store_bytes = widths.store?;
    if store_bytes <= element {
        return None;
    }
    let spanned = store_bytes.div_ceil(element);
    let cause = format!(
        "the store to `{}` writes {store_bytes} bytes where `{}` has {element}-byte elements, so \
         it covers the {spanned} elements from `{}` up and `{read_index} != {written_index}` \
         rules out only the first of them.",
        store.text(),
        store.object,
        store.text()
    );
    Some(if widths.read <= element {
        format!(
            "{cause} State `{read_index} < {written_index}`, which puts `{}` below every byte the \
             store writes.",
            cell.text()
        )
    } else {
        format!(
            "{cause} Only a stated order between the indexes can separate them, and it has to put \
             an access of at most {element} bytes below the other."
        )
    })
}

/// A call or a loop, which declares the ranges it may write. The repair is a
/// separation from that write set, and it is spelled out when the step
/// declares exactly one range and the cell has a source spelling.
fn describe_havoc_cause(
    step: &str,
    cell: Option<&SourceCell>,
    ranges: &[MemoryRange],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let spelled = ranges
        .iter()
        .map(|range| describe_source_range(range, parameter_binding))
        .collect::<Option<Vec<_>>>()
        .filter(|spelled| !spelled.is_empty());
    let Some(spelled) = spelled else {
        return format!(
            "{step} may have written it, and the ranges it may write are not shown separate from \
             it."
        );
    };
    let cell_range = cell.and_then(SourceCell::element_range);
    if let ([written], Some(read)) = (spelled.as_slice(), cell_range.as_ref()) {
        return format!(
            "{step} may write `{written}`, which is not shown separate from it. {}",
            spelled_separation_repair(read, written)
        );
    }
    format!(
        "{step} may write {}, and none of them is shown separate from it.",
        bounded_range_list(&spelled)
    )
}

/// The repair for two objects nothing separates, when both ranges have a
/// source spelling: the `separate(..)` to state, and the `views` clause that
/// says the same thing without one.
///
/// A contract's transferred clauses and its borrowed `views` clauses denote
/// disjoint memory at entry
/// (`kernel::contract_entry_partition_facts`,
/// `docs/internals/resource-tracker.md`, "The entry partition"), so a
/// function that already transfers the written range separates it from every
/// range it lends by declaring the read as a `views` clause. Both halves are
/// printed only where they verify the situation they are printed for, which
/// is why the second one names its condition rather than asserting it: this
/// renderer sees two addresses, not the contract's clause list, and the
/// entry partition does not reach a range transferred only inside a folded
/// composite. Every range that reaches here is spelled through a parameter
/// or a file-scope declaration — `SourceCell::element_range` yields nothing
/// for a local — so both clauses are ones the reader can write.
fn spelled_separation_repair(read: &str, written: &str) -> String {
    format!(
        "If they are separate, require `separate(memory({read}), memory({written}))`; where the \
         contract already transfers `{written}` with `owns` or `consumes`, declaring \
         `views {read}` says the same."
    )
}

/// At most three written ranges, so a wide write set stays one short clause.
fn bounded_range_list(ranges: &[String]) -> String {
    const SHOWN: usize = 3;
    let listed = ranges
        .iter()
        .take(SHOWN)
        .map(|range| format!("`{range}`"))
        .collect::<Vec<_>>()
        .join(", ");
    match ranges.len().checked_sub(SHOWN) {
        Some(rest) if rest > 0 => format!("{listed} and {rest} more"),
        _ => listed,
    }
}

/// The recorded step the walk stopped at, as a noun phrase a sentence can be
/// built around. No recorded step carries a source span today, so it is
/// described rather than quoted; `docs/internals/resource-tracker.md` says
/// what a line number would take.
fn describe_step(
    change: &resource_tracker::Change,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    match change {
        resource_tracker::Change::Store { pointer } => {
            match describe_source_cell(pointer, parameter_binding) {
                Some(store) => format!("the store to `{}`", store.text()),
                None => "a store".to_string(),
            }
        }
        resource_tracker::Change::CellsSeeded { .. } => {
            "the recording of range contents".to_string()
        }
        resource_tracker::Change::Call { .. } => "the call".to_string(),
        resource_tracker::Change::Loop { .. } => "the loop".to_string(),
        resource_tracker::Change::Free { allocation } => {
            match describe_memory_block(&allocation.block, parameter_binding) {
                Some(freed) => format!("the release of `{freed}`"),
                None => "a released allocation".to_string(),
            }
        }
        resource_tracker::Change::ContractRetirement { allocation } => {
            match describe_memory_block(&allocation.block, parameter_binding) {
                Some(retired) => format!("the contract possibly releasing `{retired}`"),
                None => "a contract possibly releasing an allocation".to_string(),
            }
        }
        resource_tracker::Change::Allocation { .. } => "an allocation".to_string(),
        resource_tracker::Change::AllocationPending => {
            "an allocation with no resolved address".to_string()
        }
        resource_tracker::Change::ContractAllocationClaims => {
            "a contract's allocation claims moving".to_string()
        }
        resource_tracker::Change::Declaration { .. } => "a declaration".to_string(),
        resource_tracker::Change::LifetimeEnd { .. } => "a local's lifetime ending".to_string(),
        resource_tracker::Change::ObjectInitializationRecorded => {
            "a step recording initialized bytes".to_string()
        }
        resource_tracker::Change::BranchJoin => "branch memory join".into(),
        resource_tracker::Change::CellObserved => "a cached read observation".to_string(),
        resource_tracker::Change::CellsForgotten => {
            "a step that dropped its cached cell values".to_string()
        }
        resource_tracker::Change::BeginningOfHistory => {
            "the start of the recorded execution".to_string()
        }
        resource_tracker::Change::ModelReplaced { .. } => "a replaced model".to_string(),
        resource_tracker::Change::NotHeld { .. } => {
            "a resource this state does not hold".to_string()
        }
    }
}

/// Where an address sits inside the object that holds it.
enum CellIndex {
    /// The element index, spelled with the caller's own names.
    Named(String),
    /// The address is the object itself: a struct field, a declaration.
    Whole,
    /// A selected field of a struct or struct array.
    StructMember,
    /// The address is inside the object, at an index only the lowering has a
    /// name for. The reader is shown `a[…]` rather than a kernel variable.
    Unnamed,
}

/// An address as the source writes it, split into the object it names and the
/// element index inside it, so a repair can name either part: `a` and `m` for
/// `a[m]`, `g` and `0` for `g[0]`.
struct SourceCell {
    object: String,
    index: CellIndex,
    /// The width of one element of the object the index counts in, where the
    /// spelling came from a declared pointer or array type. `None` where the
    /// address was spelled through a block name rather than a typed base, and
    /// then no byte question is asked of it: a width nobody declared is not
    /// one a refusal may reason from.
    element_bytes: Option<u32>,
    /// The kernel term the index was spelled from, where it came from a
    /// typed base, so a refusal can ask whether the facts already relate it.
    index_term: Option<MachineTerm>,
}

impl SourceCell {
    fn text(&self) -> String {
        match &self.index {
            CellIndex::Named(index) => format!("{}[{index}]", self.object),
            CellIndex::Whole | CellIndex::StructMember => self.object.clone(),
            CellIndex::Unnamed => format!("{}[…]", self.object),
        }
    }

    fn named_index(&self) -> Option<&str> {
        match &self.index {
            CellIndex::Named(index) => Some(index),
            CellIndex::Whole | CellIndex::StructMember | CellIndex::Unnamed => None,
        }
    }

    /// The one-element range holding exactly this cell, as `memory(..)` takes
    /// it: `a[0]` is `a[0..1]` and `a[m]` is `a[m..m + 1]`. Only a literal or
    /// a plain name is pasted in; a compound index would need a parenthesised
    /// form this has not been shown to get right, and a repair that has not
    /// been shown to work is not offered.
    fn element_range(&self) -> Option<String> {
        let CellIndex::Named(index) = &self.index else {
            return None;
        };
        if let Ok(start) = index.parse::<i64>() {
            // A negative element index is not a range `separate` would take,
            // and a clause that would not parse is not a repair.
            return start
                .checked_add(1)
                .filter(|_| start >= 0)
                .map(|end| format!("{}[{start}..{end}]", self.object));
        }
        let plain = !index.is_empty()
            && index.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            && !index.starts_with(|c: char| c.is_ascii_digit());
        plain.then(|| format!("{}[{index}..{index} + 1]", self.object))
    }
}

/// An address as the source writes it — `a[m]`, `g[0]`, `p->next` — or
/// nothing when the C names this diagnostic was given recover none. Unlike
/// [`describe_pointer`], the index is spelled with the caller's own names,
/// and a name that could only be a verifier-owned one is refused instead of
/// shown.
fn describe_source_cell(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
) -> Option<SourceCell> {
    describe_source_cell_of_width(pointer, None, parameter_binding)
}

/// [`describe_source_cell`] for an access of `width` bytes, when the width is
/// known: a constant offset into a struct-typed global is then the field
/// that occupies exactly those bytes, where exactly one does.
fn describe_source_cell_of_width(
    pointer: &Pointer,
    width: Option<u32>,
    parameter_binding: ParameterBinding<'_>,
) -> Option<SourceCell> {
    // Two parameters can point into one block, and then every one of them
    // can express the address -- `b[j]` is also `a[(b - a) + j]`. The
    // shortest spelling is the one written through the parameter the address
    // actually belongs to, and picking it is deterministic.
    //
    // When no candidate's index has a source spelling, every candidate reads
    // `name[…]` and the text no longer shows which base the address belongs
    // to. The raw index still does: through its own base the index is the
    // bare element offset, through another it also carries the difference of
    // the two bases. So among unnamed candidates the index with fewer
    // variables wins, and only then the shorter text.
    let mut best: Option<(SourceCell, usize)> = None;
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        if let Some(field) =
            describe_parameter_struct_field_pointer(pointer, parameter, base.pointer())
        {
            return Some(SourceCell {
                object: field,
                index: CellIndex::Whole,
                element_bytes: None,
                index_term: None,
            });
        }
        if let Some(member) =
            describe_parameter_struct_member(pointer, parameter, base.pointer(), parameter_binding)
        {
            return Some(SourceCell {
                object: member,
                index: CellIndex::StructMember,
                element_bytes: None,
                index_term: None,
            });
        }
        let element_width = diagnostic_parameter_element_width(parameter);
        let Some(index) = diagnostic_pointer_element_index_from_base(pointer, base, element_width)
        else {
            continue;
        };
        let spelled = SourceCell {
            object: parameter.name().to_string(),
            index: if bitvector_is_source_spelled(&index, parameter_binding) {
                CellIndex::Named(describe_bitvector_with_context(&index, parameter_binding))
            } else {
                CellIndex::Unnamed
            },
            element_bytes: u32::try_from(element_width).ok(),
            index_term: Some(index.clone()),
        };
        let mut index_variables = std::collections::BTreeSet::new();
        crate::kernel::collect_bitvector_variables(&index, &mut index_variables);
        let weight = index_variables.len();
        if best.as_ref().is_none_or(|(best, best_weight)| {
            prefer_source_cell(&spelled, weight, best, *best_weight)
        }) {
            best = Some((spelled, weight));
        }
    }
    if let Some((best, _)) = best {
        return Some(best);
    }
    let declared = describe_memory_block(&pointer.block, parameter_binding)?;
    if let (Some(width), PointerOffsetTerm::Constant(offset), PointerBlock::Concrete(block)) =
        (width, &pointer.offset, &pointer.block)
        && let Ok(offset) = u32::try_from(*offset)
        && let Some(field) = object_fields::object_field_spelling(block, offset, width)
    {
        return Some(SourceCell {
            object: field,
            index: CellIndex::StructMember,
            element_bytes: None,
            index_term: None,
        });
    }
    match &pointer.offset {
        // A local's block holds one declared object, and the name the reader
        // wrote for it *is* the address: `q`, not `q[0]`, which would read as a
        // store through `q` rather than to it. A local array's element zero
        // loses its index this way, which costs an index-inequality repair the
        // reader could not have used anyway -- the array is one object, so the
        // two spellings name the same storage either way.
        PointerOffsetTerm::Constant(0) if pointer.block.is_local_block() => Some(SourceCell {
            object: declared,
            index: CellIndex::Whole,
            element_bytes: None,
            index_term: None,
        }),
        PointerOffsetTerm::Constant(0) => Some(SourceCell {
            object: declared,
            index: CellIndex::Named("0".to_string()),
            element_bytes: None,
            index_term: None,
        }),
        PointerOffsetTerm::Constant(_) => Some(SourceCell {
            object: format!("{declared}+{}", describe_pointer_offset(&pointer.offset)),
            index: CellIndex::Whole,
            element_bytes: None,
            index_term: None,
        }),
        // Any other offset is a term the lowering owns; the object is still
        // the reader's, so it is named and the index is not.
        _ => Some(SourceCell {
            object: declared,
            index: CellIndex::Unnamed,
            element_bytes: None,
            index_term: None,
        }),
    }
}

/// A spelling the reader can act on beats one they cannot. Among two unnamed
/// ones the raw index with fewer variables (`index_variables`) wins, since the
/// text is `name[…]` either way; then the shortest text. Deterministic either
/// way.
fn prefer_source_cell(
    candidate: &SourceCell,
    candidate_index_variables: usize,
    best: &SourceCell,
    best_index_variables: usize,
) -> bool {
    match (
        candidate.named_index().is_some(),
        best.named_index().is_some(),
    ) {
        (true, false) => true,
        (false, true) => false,
        (false, false) if candidate_index_variables != best_index_variables => {
            candidate_index_variables < best_index_variables
        }
        _ => candidate.text().len() < best.text().len(),
    }
}

/// A memory range as the source writes it, or nothing when its base or its
/// bounds have no spelling in the caller's own names.
fn describe_source_range(
    range: &MemoryRange,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    if let Some((_, base_index)) = parameter_relative_base(range, parameter_binding) {
        let (start, end) = parameter_relative_endpoints(&base_index, range);
        if bitvector_is_source_spelled(&start, parameter_binding)
            && bitvector_is_source_spelled(&end, parameter_binding)
        {
            return Some(describe_memory_range(range, parameter_binding));
        }
    }
    if range.base().offset != PointerOffsetTerm::Constant(0)
        || !bitvector_is_source_spelled(range.bound_terms().0, parameter_binding)
        || !bitvector_is_source_spelled(range.bound_terms().1, parameter_binding)
    {
        return None;
    }
    let declared = describe_memory_block(&range.base().block, parameter_binding)?;
    Some(format!(
        "{declared}[{}..{}]",
        describe_bitvector_with_context(range.bound_terms().0, parameter_binding),
        describe_bitvector_with_context(range.bound_terms().1, parameter_binding)
    ))
}

/// True when every variable in this term has one of the caller's own names. A
/// kernel variable — a loop counter, a lowering temporary — has none, and a
/// term that mentions one is not shown to the reader at all: a repair written
/// over a name nobody wrote is not a repair.
fn bitvector_is_source_spelled(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
) -> bool {
    let mut variables = std::collections::BTreeSet::new();
    crate::kernel::collect_bitvector_variables(term, &mut variables);
    variables.iter().all(|variable| {
        describe_parameter_bitvector(&MachineTerm::Variable(*variable), parameter_binding).is_some()
    })
}

/// The whole object a block names, spelled as the source declares it: a
/// parameter whose argument points into it, or a file-scope declaration.
pub(super) fn describe_memory_block(
    block: &PointerBlock,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        if let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument
            && &base.pointer().block == block
        {
            return Some(parameter.name().to_string());
        }
    }
    match block {
        // A block's spelling carries where the storage lives, which is the
        // verifier's business; the reader wrote only the name. `local:` covers
        // the re-declaration and call-frame forms too (`local:lifetime:2:q`,
        // `local:frame:3:__return`), whose last segment is that name.
        PointerBlock::Concrete(name) => Some(
            name.strip_prefix("global:")
                .or_else(|| {
                    name.rsplit(':').next().filter(|_| {
                        PointerBlock::is_static_name(name) || PointerBlock::is_local_name(name)
                    })
                })
                .unwrap_or(name)
                .to_string(),
        ),
        // Every other block is a verifier-owned lowering artifact; naming it
        // would tell the reader nothing they wrote.
        _ => None,
    }
}

/// Spell mutex storage as an address, including a field at offset zero, rather
/// than rendering the containing object or an array-element value.
pub(in crate::surface) fn describe_mutex_pointer(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        let Some(layout) = parameter
            .pointee_struct_layout()
            .or_else(|| parameter.struct_layout())
        else {
            continue;
        };
        let Some(offset) = diagnostic_pointer_element_index_from_base(pointer, base, 1)
            .and_then(|offset| offset.as_const())
        else {
            continue;
        };
        if let Some((name, _)) = layout
            .fields()
            .iter()
            .find(|(_, field)| field.offset_bytes() == offset)
        {
            let selector = if parameter.is_struct_value() {
                "."
            } else {
                "->"
            };
            return format!("&{}{selector}{name}", parameter.name());
        }
    }
    describe_pointer(pointer, parameter_binding)
}

/// The element width of a parameter that points to (or is) an array of one
/// scalar type, the only shape a byte count can be read back as an element
/// count for.
fn scalar_element_width(interface_type: InterfaceType) -> Option<i64> {
    match interface_type {
        InterfaceType::CharPointer(_)
        | InterfaceType::CharArray(_, _)
        | InterfaceType::Int8Pointer
        | InterfaceType::Int8Array(_)
        | InterfaceType::UInt8Pointer
        | InterfaceType::UInt8Array(_) => Some(1),
        InterfaceType::Int16Pointer
        | InterfaceType::Int16Array(_)
        | InterfaceType::UInt16Pointer
        | InterfaceType::UInt16Array(_) => Some(2),
        InterfaceType::Int32Pointer
        | InterfaceType::Int32Array(_)
        | InterfaceType::UInt32Pointer
        | InterfaceType::UInt32Array(_)
        | InterfaceType::Float32Pointer
        | InterfaceType::Float32Array(_) => Some(4),
        InterfaceType::Int64Pointer(_)
        | InterfaceType::Int64Array(_, _)
        | InterfaceType::UInt64Pointer(_)
        | InterfaceType::UInt64Array(_, _)
        | InterfaceType::Float64Pointer
        | InterfaceType::Float64Array(_) => Some(8),
        InterfaceType::Int128Pointer
        | InterfaceType::UInt128Pointer
        | InterfaceType::Int128Array(_)
        | InterfaceType::UInt128Array(_) => Some(16),
        _ => None,
    }
}

thread_local! {
    /// How many addresses are being spelled inside one another's indices.
    static NESTED_ADDRESS_SPELLINGS: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
}

/// An index inside an address spelling. It is named through the tables,
/// so a local reads as its name and a loaded value as the cell it was
/// loaded from. Naming a load spells its address, whose own index can be a
/// load again, and one address can be reached from itself that way; past a
/// small nesting the index is spelled without the tables, which ends it.
fn describe_address_index(index: &MachineTerm, parameter_binding: ParameterBinding<'_>) -> String {
    const NESTING_LIMIT: u32 = 2;
    let depth = NESTED_ADDRESS_SPELLINGS.with(std::cell::Cell::get);
    if depth >= NESTING_LIMIT {
        return describe_bitvector(index);
    }
    struct Leave(u32);
    impl Drop for Leave {
        fn drop(&mut self) {
            NESTED_ADDRESS_SPELLINGS.with(|nested| nested.set(self.0));
        }
    }
    NESTED_ADDRESS_SPELLINGS.with(|nested| nested.set(depth + 1));
    let _leave = Leave(depth);
    describe_bitvector_with_context(index, parameter_binding)
}

pub(in crate::surface) fn describe_pointer(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    // Two parameters can point into one block, and then every one of them can
    // express the address -- `b[j]` is also `a[(b - a) + j]`. As in
    // [`describe_source_cell`], the shortest spelling is the one written
    // through the parameter the address actually belongs to, and picking it is
    // deterministic.
    // A pointer a load read is the place it was read from.
    if let Some(read) = pointer.as_loaded_value()
        && read.displacement == PointerOffsetTerm::Constant(0)
    {
        let place = describe_load_at(&read.defining_address, parameter_binding);
        if is_place_spelling(&place) {
            return place;
        }
    }
    let mut best: Option<String> = None;
    let mut byte_offset: Option<String> = None;
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        if let Some(field) =
            describe_parameter_struct_field_pointer(pointer, parameter, base.pointer())
        {
            return field;
        }
        if let Some(index) = diagnostic_pointer_element_index_from_base(
            pointer,
            base,
            diagnostic_parameter_element_width(parameter),
        ) {
            let spelled = if index == MachineTerm::constant(0) {
                parameter.name().to_string()
            } else {
                format!(
                    "{}[{}]",
                    parameter.name(),
                    describe_address_index(&index, parameter_binding)
                )
            };
            if best.as_ref().is_none_or(|best| spelled.len() < best.len()) {
                best = Some(spelled);
            }
        } else if let Some(member) =
            describe_parameter_struct_member(pointer, parameter, base.pointer(), parameter_binding)
        {
            if best.as_ref().is_none_or(|best| member.len() < best.len()) {
                best = Some(member);
            }
        } else if let Some(bytes) = pointer.offset_from_base(base.pointer()) {
            // An address inside the parameter's object that is no whole
            // element of it -- a byte of a wider cell, say -- is still a
            // byte offset from the parameter, as a named object's is below.
            let spelled = format!(
                "(char *){} + {}",
                parameter.name(),
                describe_pointer_offset(&bytes)
            );
            if byte_offset
                .as_ref()
                .is_none_or(|best: &String| spelled.len() < best.len())
            {
                byte_offset = Some(spelled);
            }
        }
    }
    if let Some(best) = best.or(byte_offset) {
        return best;
    }
    // A by-value aggregate parameter is two objects: the callee's copy,
    // which the tables name, and the argument it was copied from, which a
    // claim about the parameter reads. The second is the caller's.
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(copy)) = argument else {
            continue;
        };
        let Some(source) = crate::kernel::registered_aggregate_argument_source(&copy.block) else {
            continue;
        };
        // A pointer the argument holds in a field is that field's value,
        // the same in the copy and in the argument it was copied from.
        if let Some(field) = describe_parameter_struct_field_pointer(pointer, parameter, &source) {
            return field.replacen("->", ".", 1);
        }
        let name = format!("the caller's {}", parameter.name());
        if let Some(member) =
            describe_struct_member_from(pointer, parameter, &source, &name, ".", parameter_binding)
        {
            return member;
        }
        if *pointer == source {
            return name;
        }
    }
    match &pointer.block {
        // External argument blocks are verifier-owned lowering artifacts. Do
        // not expose their block names or offsets in user-facing diagnostics.
        PointerBlock::ExternalArgument => "the pointer value at this program point".to_string(),
        // A named object (a local, global or static, or the object a
        // parameter points into) is spelled by the name the source gave it,
        // never by the block's internal spelling (`local:frame:3:x@0`).
        PointerBlock::Concrete(name)
            if name == "null" && pointer.offset == PointerOffsetTerm::Constant(0) =>
        {
            "NULL".to_string()
        }
        block => match named_object_block(block, parameter_binding) {
            Some(name) if pointer.offset == PointerOffsetTerm::Constant(0) => format!("&{name}"),
            Some(name) => format!(
                "(char *)&{name} + {}",
                describe_pointer_offset_with_context(&pointer.offset, parameter_binding)
            ),
            // Heap, temporary and symbolic blocks have no source name.
            None => "…".to_string(),
        },
    }
}

/// Reconstructs the source spelling of a pointer loaded from a pointer-to-
/// struct parameter.  Field accesses are lowered to a memory load followed by
/// a pointer offset, so the kernel no longer carries the original `p->field`
/// AST node in the resource fact.  The parameter's parsed layout is the
/// source-level metadata needed to recover that spelling without printing the
/// lowered block, load, or version terms.
fn describe_parameter_struct_field_pointer(
    pointer: &Pointer,
    parameter: &crate::languages::interface::ImportedParameter,
    base: &Pointer,
) -> Option<String> {
    let layout = parameter
        .pointee_struct_layout()
        .or_else(|| parameter.struct_layout())?;
    // The value a load of the field read, or its storage-relative encoding.
    let (loaded_at, byte_width) = match pointer.as_loaded_value() {
        Some(read) if read.displacement == PointerOffsetTerm::Constant(0) => {
            (read.defining_address, None)
        }
        Some(_) => return None,
        None => {
            let PointerOffsetTerm::Int32Scaled { value, byte_width } = &pointer.offset else {
                return None;
            };
            let loaded_at = match value.structural_value() {
                MachineTerm::MemoryLoad(_, loaded_at, _) => loaded_at.as_ref().clone(),
                MachineTerm::Variable(variable) => {
                    crate::kernel::registered_load_for_variable(variable)?.1
                }
                _ => return None,
            };
            if pointer.block != base.block {
                return None;
            }
            (loaded_at, Some(*byte_width))
        }
    };
    layout.fields().iter().find_map(|(name, field)| {
        let field_type = field.interface_type();
        let pointee_type = field_type.pointee_type()?;
        let pointee_width = diagnostic_c_type_byte_width(pointee_type, field.byte_width());
        if byte_width.is_some_and(|byte_width| pointee_width != byte_width) {
            return None;
        }
        let field_offset = diagnostic_pointer_element_index_from_base(&loaded_at, base, 1)?;
        (field_offset == MachineTerm::constant(field.offset_bytes()))
            .then(|| describe_field_place(parameter.name(), name))
    })
}

/// An address inside the struct a parameter points to, spelled through the
/// parameter: `p->field` for a member of `*p`, `p[i].field` for a member of
/// element `i`, and `p->field[k]` for an element of an array member.
///
/// The address is the parameter's own plus at most one index scaled by the
/// struct's size plus a constant inside the struct. Anything else has no
/// member spelling here.
///
/// The index is spelled by [`describe_address_index`].
fn describe_parameter_struct_member(
    pointer: &Pointer,
    parameter: &crate::languages::interface::ImportedParameter,
    base: &Pointer,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    describe_struct_member_from(
        pointer,
        parameter,
        base,
        parameter.name(),
        "->",
        parameter_binding,
    )
}

/// [`describe_parameter_struct_member`] against an object spelled `name`
/// whose members are selected with `select` (`->` through a pointer, `.` on
/// a value).
fn describe_struct_member_from(
    pointer: &Pointer,
    parameter: &crate::languages::interface::ImportedParameter,
    base: &Pointer,
    name: &str,
    select: &str,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let layout = parameter
        .pointee_struct_layout()
        .or_else(|| parameter.struct_layout())?;
    let size = i64::from(layout.size_bytes());
    if size == 0 {
        return None;
    }
    let mut constant = 0i64;
    let mut element: Option<&MachineTerm> = None;
    let rest = pointer.offset_from_base(base)?;
    let mut pending = vec![&rest];
    while let Some(term) = pending.pop() {
        match term {
            PointerOffsetTerm::Add(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            PointerOffsetTerm::Constant(bytes) => constant = constant.checked_add(*bytes)?,
            PointerOffsetTerm::Int32Scaled { value, byte_width }
            | PointerOffsetTerm::Int64Scaled {
                value, byte_width, ..
            } if *byte_width == size && element.is_none() => {
                element = Some(value.structural_value())
            }
            _ => return None,
        }
    }
    // A constant past the first struct selects a later element.
    let (whole, inside) = (constant.div_euclid(size), constant.rem_euclid(size));
    let selected = match (element, whole) {
        (None, 0) => None,
        (None, whole) => Some(whole.to_string()),
        (Some(index), 0) => Some(describe_address_index(index, parameter_binding)),
        (Some(index), whole) => Some(format!(
            "{} + {whole}",
            describe_address_index(index, parameter_binding)
        )),
    };
    let fields = layout.fields();
    let (field_name, field) = fields
        .iter()
        .filter(|(_, field)| i64::from(field.offset_bytes()) <= inside)
        .max_by_key(|(_, field)| field.offset_bytes())?;
    let within = inside - i64::from(field.offset_bytes());
    let member = match &selected {
        Some(index) => format!("{name}[{index}].{field_name}"),
        None => format!("{name}{select}{field_name}"),
    };
    if within == 0 {
        return Some(member);
    }
    let width = scalar_element_width(field.interface_type())
        .or_else(|| field.array_element_width().map(i64::from))?;
    (within % width == 0).then(|| format!("{member}[{}]", within / width))
}

fn diagnostic_c_type_byte_width(interface_type: InterfaceType, pointer_width: u32) -> i64 {
    match interface_type {
        InterfaceType::Bool | InterfaceType::Char(_) | InterfaceType::UInt8 => 1,
        InterfaceType::Int8 => 1,
        InterfaceType::Int16 | InterfaceType::UInt16 => 2,
        InterfaceType::Int32 | InterfaceType::UInt32 => 4,
        InterfaceType::Int64(_) | InterfaceType::UInt64(_) => 8,
        _ if interface_type.is_pointer() => i64::from(pointer_width),
        _ => i64::from(pointer_width),
    }
}

pub(super) fn diagnostic_parameter_element_width(
    parameter: &crate::languages::interface::ImportedParameter,
) -> i64 {
    if let Some(width) = parameter.array_element_width() {
        return i64::from(width);
    }
    if let Some(pointee) = parameter
        .interface_type()
        .pointee_type()
        .filter(|ty| ty.is_pointer())
    {
        return i64::from(pointee.to_kernel_type().byte_width());
    }
    if let Some(layout) = parameter.pointee_struct_layout() {
        return i64::from(layout.size_bytes());
    }
    if !parameter.is_struct_value()
        && parameter
            .interface_type()
            .pointee_type()
            .is_some_and(|pointee| !pointee.is_pointer())
        && let Some(layout) = parameter.struct_layout()
    {
        return i64::from(layout.size_bytes());
    }
    // A pointer to (or array of) one scalar type is indexed by that scalar's
    // width, whatever the pointer itself occupies.
    if let Some(width) = scalar_element_width(parameter.interface_type()) {
        return width;
    }
    match parameter.interface_type() {
        InterfaceType::Int128
        | InterfaceType::UInt128
        | InterfaceType::Int128Array(_)
        | InterfaceType::UInt128Array(_) => 16,
        InterfaceType::Parameter(_) => 0,
        InterfaceType::Void => 0,
        InterfaceType::Bool => 1,
        InterfaceType::VoidPointer
        | InterfaceType::VoidPointerPointer
        | InterfaceType::ParameterPointer(_) => 8,
        InterfaceType::CharPointer(_)
        | InterfaceType::CharArray(_, _)
        | InterfaceType::UInt8Pointer
        | InterfaceType::UInt8Array(_) => 1,
        InterfaceType::Int8 | InterfaceType::Int8Array(_) => 1,
        InterfaceType::Int16
        | InterfaceType::UInt16
        | InterfaceType::Int16Array(_)
        | InterfaceType::UInt16Array(_) => 2,
        InterfaceType::Int32
        | InterfaceType::Char(_)
        | InterfaceType::UInt8
        | InterfaceType::UInt32
        | InterfaceType::Int32Pointer
        | InterfaceType::UInt32Pointer
        | InterfaceType::Int32Array(_)
        | InterfaceType::UInt32Array(_) => 4,
        InterfaceType::Int64(_)
        | InterfaceType::UInt64(_)
        | InterfaceType::Int64Array(_, _)
        | InterfaceType::UInt64Array(_, _) => 8,
        InterfaceType::Float32 | InterfaceType::Float32Array(_) => 4,
        InterfaceType::Float64 | InterfaceType::Float64Array(_) => 8,
        InterfaceType::Int8Pointer | InterfaceType::Int8PointerPointer => 8,
        InterfaceType::Int16Pointer
        | InterfaceType::UInt16Pointer
        | InterfaceType::Int128Pointer
        | InterfaceType::Int64Pointer(_)
        | InterfaceType::UInt128Pointer
        | InterfaceType::UInt64Pointer(_)
        | InterfaceType::Int16PointerPointer
        | InterfaceType::UInt16PointerPointer
        | InterfaceType::Int32PointerPointer
        | InterfaceType::CharPointerPointer(_)
        | InterfaceType::UInt8PointerPointer
        | InterfaceType::UInt32PointerPointer
        | InterfaceType::Int128PointerPointer
        | InterfaceType::Int64PointerPointer(_)
        | InterfaceType::UInt128PointerPointer
        | InterfaceType::UInt64PointerPointer(_)
        | InterfaceType::Float32Pointer
        | InterfaceType::Float64Pointer
        | InterfaceType::Float32PointerPointer
        | InterfaceType::Float64PointerPointer => 8,
        InterfaceType::FunctionPointer(_) => 8,
        InterfaceType::PointerArray(_, _, _) => 8,
    }
}

pub(super) fn diagnostic_pointer_element_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    byte_width: i64,
) -> Option<MachineTerm> {
    if pointer.block != base.block {
        return None;
    }

    if pointer.offset == base.offset {
        return Some(MachineTerm::constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return diagnostic_element_index_from_pointer_offset(&pointer.offset, byte_width);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &base.offset => {
            diagnostic_element_index_from_pointer_offset(right, byte_width)
        }
        PointerOffsetTerm::Add(left, right) if right.as_ref() == &base.offset => {
            diagnostic_element_index_from_pointer_offset(left, byte_width)
        }
        _ => {
            // Name the element as the kernel does: the base's own summands
            // cancel exactly, so `((a + k) + 1) - a` prints as `k + 1`.
            if pointer.offset_from_base(base).is_some()
                && let Ok(width) = u32::try_from(byte_width)
                && let Some(index) = pointer.element_index_from_base_with_width(base, width)
            {
                return Some(index);
            }
            if let (Some(pointer_index), Some(base_index)) = (
                diagnostic_element_index_from_pointer_offset(&pointer.offset, byte_width),
                diagnostic_element_index_from_pointer_offset(&base.offset, byte_width),
            ) {
                Some(bitvector32_subtract(pointer_index, base_index))
            } else {
                None
            }
        }
    }
}

pub(super) fn diagnostic_element_index_from_pointer_offset(
    offset: &PointerOffsetTerm,
    byte_width: i64,
) -> Option<MachineTerm> {
    match offset {
        PointerOffsetTerm::Constant(offset) if offset % byte_width == 0 => {
            let index = offset / byte_width;
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(MachineTerm::constant((index as i32) as u32))
        }
        PointerOffsetTerm::Int32Scaled {
            value,
            byte_width: actual_width,
        } if *actual_width == byte_width => Some(value.structural_value().clone()),
        // An index widened to 64 bits before scaling (a `uint32` index, or
        // an `int32` one on a wide address) is still the index the source
        // wrote. The widening decides the address, not the element's name.
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width: actual_width,
            ..
        } if *actual_width == byte_width => Some(match value.structural_value() {
            // These widenings keep the value, so the element is named by
            // the narrow index, as a signed 32-bit index names it.
            cast_term!(Int64From32, narrow)
            | cast_term!(UInt64From32, narrow)
            | cast_term!(Int64FromUInt32, narrow) => narrow.as_ref().clone(),
            wide => wide.clone(),
        }),
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            diagnostic_element_index_from_pointer_offset(right, byte_width)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            diagnostic_element_index_from_pointer_offset(left, byte_width)
        }
        PointerOffsetTerm::Add(left, right) => Some(bitvector32_add(
            diagnostic_element_index_from_pointer_offset(left, byte_width)?,
            diagnostic_element_index_from_pointer_offset(right, byte_width)?,
        )),
        _ => None,
    }
}

/// Spell IEEE bits without host float formatting or NaN canonicalization.
pub(in crate::surface) fn exact_float_literal_spelling(value: &ProgramValue) -> Option<String> {
    use crate::kernel::MachineIntegerType;
    match value {
        ProgramValue::Float32(MachineTerm::Constant {
            format: MachineIntegerType::Int32,
            bits,
        }) if *bits <= u128::from(u32::MAX) => Some(format!("float32_from_bits(0x{bits:08x})")),
        ProgramValue::Float32(MachineTerm::Constant {
            format: MachineIntegerType::UInt32,
            bits,
        }) if *bits <= u128::from(u32::MAX) => Some(format!("float32_from_bits(0x{bits:08x}u32)")),
        ProgramValue::Float64(MachineTerm::Constant {
            format: MachineIntegerType::UInt64,
            bits,
        }) if *bits <= u128::from(u64::MAX) => Some(format!("float64_from_bits(0x{bits:016x}u64)")),
        _ => None,
    }
}

/// A value of a narrow or unsigned type as a refusal spells it. A literal
/// takes its type suffix (`5u32`), which is how the source writes one. A
/// name or a compound expression is already a typed source term, and a
/// suffix glued to it (`xu32`) would read as a different identifier.
fn typed_literal_spelling(spelled: String, suffix: &str) -> String {
    let magnitude = spelled.strip_prefix('-').unwrap_or(&spelled);
    let literal = magnitude.starts_with(|first: char| first.is_ascii_digit())
        && magnitude.parse::<f64>().is_ok();
    if literal {
        format!("{spelled}{suffix}")
    } else {
        spelled
    }
}

/// A wide range held in one element width and required in another: name
/// the range whose endpoint is the product and the product's no-wrap
/// condition, `range p[0u64..n] of 8-byte elements needs n * 8 to not wrap
/// (n * 8 <= UINT64_MAX)`.
fn describe_wide_range_no_wrap(
    no_wrap: &crate::kernel::WideRangeNoWrap,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let range = render_resource_fact_diagnostic(&no_wrap.range, parameter_binding);
    let range = range.strip_prefix("owns ").unwrap_or(&range);
    let width = no_wrap
        .range
        .memory_range()
        .map_or(0, crate::kernel::MemoryRange::element_width);
    let product = format!(
        "{} * {}",
        describe_program_value(
            &ProgramValue::UInt64(no_wrap.count.clone()),
            parameter_binding
        ),
        no_wrap.factor
    );
    let elements = if width == 1 {
        "bytes".to_string()
    } else {
        format!("{width}-byte elements")
    };
    format!(
        "range `{range}` of {elements} needs `{product}` to not wrap (`{product} <= UINT64_MAX`): \
         a wide range stands for one of another element width only where that product is \
         decided, for example by a bound on the count"
    )
}

pub(super) fn describe_program_value(
    value: &ProgramValue,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Parameter(term) => format!("{term:?}"),
        ProgramValue::Void => "void".to_string(),
        ProgramValue::Bool(value) if value.bool_constant_value() == Some(false) => {
            "false".to_string()
        }
        ProgramValue::Bool(value) if value.bool_constant_value() == Some(true) => {
            "true".to_string()
        }
        ProgramValue::Int128(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "i128",
        ),
        ProgramValue::UInt128(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "u128",
        ),
        ProgramValue::Bool(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "bool",
        ),
        ProgramValue::Int8(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "i8",
        ),
        ProgramValue::Int16(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "i16",
        ),
        ProgramValue::Int32(value) => describe_bitvector_with_context(value, parameter_binding),
        ProgramValue::UInt8(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "u8",
        ),
        ProgramValue::UInt32(bits32_constant!(value)) => {
            format!("{value}u32", value = constant_u32(*value))
        }
        ProgramValue::UInt32(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "u32",
        ),
        ProgramValue::UInt16(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "u16",
        ),
        // A 64-bit constant already carries its suffix.
        ProgramValue::Int64(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "i64",
        ),
        ProgramValue::UInt64(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "u64",
        ),
        value @ (ProgramValue::Float32(_) | ProgramValue::Float64(_))
            if exact_float_literal_spelling(value).is_some() =>
        {
            exact_float_literal_spelling(value).unwrap()
        }
        ProgramValue::Float32(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "f32",
        ),
        ProgramValue::Float64(value) => typed_literal_spelling(
            describe_bitvector_with_context(value, parameter_binding),
            "f64",
        ),
        ProgramValue::Pointer(pointer) => describe_pointer(pointer, parameter_binding),
    }
}

/// Whether a rendered pointer reads as one operand under a prefix `*`.
fn is_place_spelling(rendered: &str) -> bool {
    rendered
        .chars()
        .all(|character| character.is_alphanumeric() || "_:->.".contains(character))
}

pub(super) fn describe_contract_segment(segment: &ContractSegment) -> String {
    let base = describe_program_expression(&segment.base);
    let current = match &segment.surface {
        // A place written alone is recorded as one element at its address.
        ContractSegmentSurface::Range {
            base: ContractExpression::ProgramExpression(ProgramExpression::AddressOf(place)),
            start: ContractExpression::ProgramExpression(ProgramExpression::Value(start)),
            end: ContractExpression::ProgramExpression(ProgramExpression::Value(end)),
        } if *start == int32(0)
            && *end == int32(1)
            && !matches!(place.as_ref(), ProgramExpression::Variable(_)) =>
        {
            describe_program_expression(place)
        }
        ContractSegmentSurface::Range {
            base:
                ContractExpression::CUnary {
                    operand,
                    lowered: ProgramExpression::AddressOf(_),
                },
            start: ContractExpression::ProgramExpression(ProgramExpression::Value(start)),
            end: ContractExpression::ProgramExpression(ProgramExpression::Value(end)),
        } if *start == int32(0)
            && *end == int32(1)
            && !matches!(
                operand.as_ref(),
                ContractExpression::Binding(_)
                    | ContractExpression::CBinding(_)
                    | ContractExpression::ProgramExpression(ProgramExpression::Variable(_))
            ) =>
        {
            describe_contract_expression(operand)
        }
        ContractSegmentSurface::Range { base, start, end }
        | ContractSegmentSurface::StructRange {
            base, start, end, ..
        } => {
            let rendered_base = describe_contract_expression(base);
            let (start, end) = (
                describe_contract_expression(start),
                describe_contract_expression(end),
            );
            // The same place once its base is an address value.
            match rendered_base.strip_prefix('&') {
                Some(_) => format!("({rendered_base})[{start}..{end}]"),
                _ => format!("{rendered_base}[{start}..{end}]"),
            }
        }
        ContractSegmentSurface::Field {
            base: surface_base,
            name,
            ..
        } => match surface_base {
            Some(surface_base) => {
                describe_field_place(&describe_contract_expression(surface_base), name)
            }
            None => describe_field_place(&base, name),
        },
        ContractSegmentSurface::ObjectPlace { name, .. } => name.clone(),
        // The object at a named object's address is that object.
        ContractSegmentSurface::Object(_)
            if base.strip_prefix('&').is_some_and(is_place_spelling) =>
        {
            base[1..].to_string()
        }
        ContractSegmentSurface::Object(_) if is_place_spelling(&base) => format!("*{base}"),
        ContractSegmentSurface::Object(_) => format!("*({base})"),
    };
    let current = match segment.state {
        ContractSegmentState::Current => current,
        ContractSegmentState::Old => format!("old({current})"),
    };
    if segment.uninitialized {
        format!("uninitialized({current})")
    } else {
        current
    }
}

/// A string literal's storage reads as "a string literal": its block name
/// is one the lowering generated, not one the source has.
fn name_string_literal_storage(message: &str) -> String {
    let Some(start) = message.find("`string:") else {
        return message.to_string();
    };
    let Some(length) = message[start + 1..].find('`') else {
        return message.to_string();
    };
    let end = start + 1 + length;
    if !message[start..end].contains("__click_string_literal") {
        return message.to_string();
    }
    format!(
        "{}a string literal{}",
        &message[..start],
        &message[end + 1..]
    )
}

pub(in crate::surface) fn describe_callback_source(expression: &syntax::CExpression) -> String {
    match expression {
        syntax::CExpression::Field {
            pointer,
            source: Some(source),
            ..
        } => {
            // Member lowering narrows the field after adding its offset.
            // Neither operation belongs in the source-level field spelling.
            let mut base = pointer.as_ref();
            while let syntax::CExpression::Subobject { pointer, .. } = base {
                base = pointer;
            }
            if let syntax::CExpression::PointerOffsetBytes { pointer, .. } = base {
                base = pointer;
            }
            match base {
                syntax::CExpression::AddressOf(object) => {
                    format!(
                        "{}.{}",
                        describe_callback_source(object),
                        source.field_name()
                    )
                }
                pointer => format!(
                    "{}->{}",
                    describe_callback_source(pointer),
                    source.field_name()
                ),
            }
        }
        expression => describe_program_expression(&expression.to_kernel_expression()),
    }
}

thread_local! {
    static REFERENCE_RESULT_SOURCE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Kernel reference results carry addresses. Function-directed proof printing
/// must spell that carrier as `&result`, and a load through it as `result`.
pub(super) struct ReferenceResultSourceScope(bool);

/// Whether `result` is spelled as a reference result's carrier here.
pub(crate) fn reference_result_source() -> bool {
    REFERENCE_RESULT_SOURCE.with(std::cell::Cell::get)
}

impl ReferenceResultSourceScope {
    pub(super) fn enter(reference: bool) -> Self {
        Self(REFERENCE_RESULT_SOURCE.with(|slot| slot.replace(reference)))
    }
}

impl Drop for ReferenceResultSourceScope {
    fn drop(&mut self) {
        REFERENCE_RESULT_SOURCE.with(|slot| slot.set(self.0));
    }
}

/// Click's cast, `operand as target`, from their spellings. A pointer
/// target is parenthesized, `p as (uint8 *)`. `as` binds tighter than every
/// binary operator and looser than every unary one, so an operand that is
/// not a unary expression, or a chain of casts, is parenthesized; a caller
/// that puts the cast under a unary operator parenthesizes the cast.
pub(in crate::surface) fn click_cast(operand: &str, target: &str) -> String {
    let target = click_cast_target(target);
    if spells_cast_operand(operand) {
        format!("{operand} as {target}")
    } else {
        format!("({operand}) as {target}")
    }
}

/// A cast target as Click source writes it: an integer bare, a pointer
/// parenthesized with a space before its `*`, `(uint8 *)`.
pub(in crate::surface) fn click_cast_target(target: &str) -> String {
    let Some(star) = target.find('*') else {
        return target.to_string();
    };
    let (pointee, stars) = target.split_at(star);
    format!("({} {stars})", pointee.trim_end())
}

/// Whether `text` reads as the operand of an `as` cast without parentheses:
/// a unary expression (no space outside brackets), optionally followed by
/// casts of it, `x as int32 as uint64`.
pub(in crate::surface) fn spells_cast_operand(text: &str) -> bool {
    let mut depth = 0i32;
    let mut quoted = false;
    let bytes = text.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        let byte = bytes[index];
        match byte {
            b'"' => quoted = !quoted,
            _ if quoted => {}
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b' ' if depth == 0 => {
                // Only a cast may follow at the top level: ` as T`.
                let rest = &text[index..];
                let Some(target) = rest.strip_prefix(" as ") else {
                    return false;
                };
                let end = if target.starts_with('(') {
                    let mut nesting = 0i32;
                    target
                        .char_indices()
                        .find_map(|(at, ch)| {
                            match ch {
                                '(' => nesting += 1,
                                ')' => nesting -= 1,
                                _ => {}
                            }
                            (nesting == 0).then_some(at + 1)
                        })
                        .unwrap_or(target.len())
                } else {
                    target.find(' ').unwrap_or(target.len())
                };
                index += 4 + end;
                continue;
            }
            _ => {}
        }
        index += 1;
    }
    !text.is_empty()
}

/// The path step that names an operator of kind `kind`.
pub(in crate::surface) fn operator_step_name(kind: crate::kernel::OperatorKind) -> &'static str {
    match kind {
        crate::kernel::OperatorKind::And => "and",
        crate::kernel::OperatorKind::Or => "or",
        crate::kernel::OperatorKind::Ternary => "ternary",
    }
}

/// The operator `kind` as a reader names it.
pub(in crate::surface) fn describe_operator_kind(
    kind: crate::kernel::OperatorKind,
) -> &'static str {
    match kind {
        crate::kernel::OperatorKind::And => "`&&`",
        crate::kernel::OperatorKind::Or => "`||`",
        crate::kernel::OperatorKind::Ternary => "the ternary operator",
    }
}

pub(super) fn describe_program_expression(expression: &ProgramExpression) -> String {
    match expression {
        ProgramExpression::Value(value) => {
            describe_program_value(value, ParameterBinding::default())
        }
        ProgramExpression::Variable(name)
            if name == "result" && REFERENCE_RESULT_SOURCE.with(std::cell::Cell::get) =>
        {
            "&result".into()
        }
        ProgramExpression::Variable(name) => {
            rust_variable_spelling(name).unwrap_or_else(|| name.clone())
        }
        ProgramExpression::FunctionAddress(name) => format!("&{name}"),
        ProgramExpression::StepResult {
            origin: crate::kernel::StepOrigin::Call(function_name),
            ..
        } => format!("{}(…)", describe_called_function(function_name)),
        ProgramExpression::StepResult {
            origin: crate::kernel::StepOrigin::Prior(local),
            ..
        } => format!(
            "{} (before its update)",
            rust_variable_spelling(local).unwrap_or_else(|| local.clone())
        ),
        ProgramExpression::StepResult {
            origin: crate::kernel::StepOrigin::Operator(kind),
            ..
        } => format!("the value of {}", describe_operator_kind(*kind)),
        ProgramExpression::StepResult {
            origin: crate::kernel::StepOrigin::Value(what),
            ..
        } => format!("the value of {what}"),
        ProgramExpression::Cast {
            expression,
            target_type,
            pointee_struct,
            ..
        } => {
            // The contract parser accepts the null pointer constant directly;
            // a C header's `(void *)0` must not expose the kernel type name.
            if target_type.is_pointer()
                && matches!(
                    expression.as_ref(),
                    ProgramExpression::Value(ProgramValue::Int32(int32_constant!(0)))
                )
            {
                return "0".into();
            }
            if let Some(struct_name) = pointee_struct {
                return format!(
                    "({})",
                    click_cast(
                        &describe_program_expression(expression),
                        &format!("struct {struct_name} *")
                    )
                );
            }
            if rust_spelling()
                && let Some(spelling) = rust_scalar_spelling(target_type)
            {
                return format!(
                    "({} as {spelling})",
                    describe_program_expression(expression)
                );
            }
            let spelling = crate::kernel::program_type_spelling(*target_type);
            // Contract expressions use the `expression as type` cast syntax.
            // Wrap the complete cast so it remains a single term when it is
            // embedded in a generated comparison or another proposition.
            format!(
                "({})",
                click_cast(&describe_program_expression(expression), spelling)
            )
        }
        ProgramExpression::FloatNegate(expression) => {
            format!("-{}", describe_program_expression(expression))
        }
        ProgramExpression::EnumConstruct {
            enum_type,
            variant,
            fields,
        } => {
            let name = format!("{}::{variant}", enum_type.name());
            if fields.is_empty() {
                name
            } else {
                format!(
                    "{name}({})",
                    fields
                        .iter()
                        .map(describe_program_expression)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
        ProgramExpression::EnumField {
            value,
            variant,
            index,
        } => format!(
            "({} as {variant}).{index}",
            describe_program_expression(value)
        ),
        ProgramExpression::EnumIs { value, variant } => {
            format!("{} is {variant}", describe_program_expression(value))
        }
        ProgramExpression::FloatClassification {
            expression,
            classification,
        } => format!(
            "is{classification:?}({})",
            describe_program_expression(expression)
        ),
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => format!(
            "{} ? {} : {}",
            describe_program_expression(condition),
            describe_program_expression(then_branch),
            describe_program_expression(else_branch)
        ),
        ProgramExpression::AddressOf(target) => format!("&{}", describe_program_expression(target)),
        ProgramExpression::CheckedObjectAddress(target) => {
            format!(
                "address of live object `{}`",
                describe_program_expression(target)
            )
        }
        ProgramExpression::PointerOffsetBytes { pointer, bytes } => {
            format!(
                "byte_offset({}, {bytes})",
                describe_program_expression(pointer)
            )
        }
        ProgramExpression::Subobject { pointer, .. } => describe_program_expression(pointer),
        ProgramExpression::LessThan(left, right) => {
            describe_binary_program_expression(left, "<", right)
        }
        ProgramExpression::LessEqual(left, right) => {
            describe_binary_program_expression(left, "<=", right)
        }
        ProgramExpression::GreaterThan(left, right) => {
            describe_binary_program_expression(left, ">", right)
        }
        ProgramExpression::GreaterEqual(left, right) => {
            describe_binary_program_expression(left, ">=", right)
        }
        ProgramExpression::Equal(left, right) => {
            describe_binary_program_expression(left, "==", right)
        }
        ProgramExpression::NotEqual(left, right) => {
            describe_binary_program_expression(left, "!=", right)
        }
        ProgramExpression::Not(expression) => {
            format!("!{}", describe_program_expression(expression))
        }
        ProgramExpression::And(left, right) => {
            describe_binary_program_expression(left, "&&", right)
        }
        ProgramExpression::Or(left, right) => describe_binary_program_expression(left, "||", right),
        ProgramExpression::Add(left, right) => describe_binary_program_expression(left, "+", right),
        ProgramExpression::Subtract(left, right) => {
            describe_binary_program_expression(left, "-", right)
        }
        ProgramExpression::Multiply(left, right) => {
            describe_binary_program_expression(left, "*", right)
        }
        ProgramExpression::Divide(left, right) => {
            describe_binary_program_expression(left, "/", right)
        }
        ProgramExpression::Remainder(left, right) => {
            describe_binary_program_expression(left, "%", right)
        }
        ProgramExpression::ShiftLeft(left, right) => {
            describe_binary_program_expression(left, "<<", right)
        }
        ProgramExpression::RustShiftLeft(left, right) => {
            describe_binary_program_expression(left, "<<", right)
        }
        ProgramExpression::ShiftRight(left, right) => {
            describe_binary_program_expression(left, ">>", right)
        }
        ProgramExpression::RustShiftRight(left, right) => {
            describe_binary_program_expression(left, ">>", right)
        }
        ProgramExpression::BitwiseAnd(left, right) => {
            describe_binary_program_expression(left, "&", right)
        }
        ProgramExpression::BitwiseOr(left, right) => {
            describe_binary_program_expression(left, "|", right)
        }
        ProgramExpression::BitwiseXor(left, right) => {
            describe_binary_program_expression(left, "^", right)
        }
        ProgramExpression::BitwiseNot(expression) => {
            format!("~{}", describe_program_expression(expression))
        }
        // A load through `&name` keeps its address form. Whether it reads a
        // scalar referent whole or the first field of a struct referent
        // depends on a type this printer does not have.
        ProgramExpression::Load(pointer) => format!("*{}", describe_program_expression(pointer)),
        ProgramExpression::TypedLoad {
            pointer,
            value_type,
            volatile,
            pointee_constant,
            ..
        } => {
            if !*volatile
                && let Some(place) =
                    describe_read_through_parameter(pointer, *value_type, *pointee_constant)
            {
                return place;
            }
            let name = match value_type {
                ProgramType::Int128 => "load_int128",
                ProgramType::UInt128 => "load_uint128",
                ProgramType::Parameter(_) => "load_parameter",
                ProgramType::ParameterPointer(_) => "load_parameter_pointer",
                ProgramType::Void => "load_void",
                ProgramType::Bool => "load_bool",
                ProgramType::VoidPointer => "load_void_pointer",
                ProgramType::VoidPointerPointer => "load_void_pointer_pointer",
                ProgramType::Int8 => "load_int8",
                ProgramType::Int16 => "load_int16",
                ProgramType::Int32 => "load_int32",
                ProgramType::UInt8 => "load_uint8",
                ProgramType::UInt16 => "load_uint16",
                ProgramType::UInt32 => "load_uint32",
                ProgramType::Int64 => "load_int64",
                ProgramType::UInt64 => "load_uint64",
                ProgramType::Float32 => "load_float",
                ProgramType::Float64 => "load_double",
                ProgramType::Int8Pointer => "load_int8_pointer",
                ProgramType::Int16Pointer => "load_int16_pointer",
                ProgramType::UInt16Pointer => "load_uint16_pointer",
                ProgramType::Int32Pointer => "load_int32_pointer",
                ProgramType::UInt8Pointer => "load_uint8_pointer",
                ProgramType::UInt32Pointer => "load_uint32_pointer",
                ProgramType::Int64Pointer => "load_int64_pointer",
                ProgramType::Int128Pointer => "load_int128_pointer",
                ProgramType::UInt64Pointer => "load_uint64_pointer",
                ProgramType::UInt128Pointer => "load_uint128_pointer",
                ProgramType::Int8PointerPointer => "load_int8_pointer_pointer",
                ProgramType::Int16PointerPointer => "load_int16_pointer_pointer",
                ProgramType::UInt16PointerPointer => "load_uint16_pointer_pointer",
                ProgramType::Int32PointerPointer => "load_int32_pointer_pointer",
                ProgramType::UInt8PointerPointer => "load_uint8_pointer_pointer",
                ProgramType::UInt32PointerPointer => "load_uint32_pointer_pointer",
                ProgramType::Int64PointerPointer => "load_int64_pointer_pointer",
                ProgramType::Int128PointerPointer => "load_int128_pointer_pointer",
                ProgramType::UInt64PointerPointer => "load_uint64_pointer_pointer",
                ProgramType::UInt128PointerPointer => "load_uint128_pointer_pointer",
                ProgramType::Float32Pointer => "load_float_pointer",
                ProgramType::Float64Pointer => "load_double_pointer",
                ProgramType::Float32PointerPointer => "load_float_pointer_pointer",
                ProgramType::Float64PointerPointer => "load_double_pointer_pointer",
                ProgramType::FunctionPointer(_) => "load_function_pointer",
                ProgramType::Int8Array(_) => {
                    return format!("*{}", describe_program_expression(pointer));
                }
                ProgramType::Int32Array(_)
                | ProgramType::UInt8Array(_)
                | ProgramType::Int16Array(_)
                | ProgramType::UInt16Array(_)
                | ProgramType::UInt32Array(_)
                | ProgramType::Int128Array(_)
                | ProgramType::Int64Array(_)
                | ProgramType::UInt128Array(_)
                | ProgramType::UInt64Array(_)
                | ProgramType::Float32Array(_)
                | ProgramType::Float64Array(_) => {
                    return format!("*{}", describe_program_expression(pointer));
                }
                ProgramType::PointerArray(_, _) => {
                    return format!("*{}", describe_program_expression(pointer));
                }
            };
            format!("{name}({})", describe_program_expression(pointer))
        }
        ProgramExpression::Index(base, index) => {
            // A read through the checked address of a C++ reference's
            // object is the original lvalue. The read itself requires live
            // storage; diagnostic address prose is not source syntax.
            if let ProgramExpression::CheckedObjectAddress(object) = base.as_ref()
                && matches!(
                    index.as_ref(),
                    ProgramExpression::Value(ProgramValue::Int32(int32_constant!(0)))
                )
            {
                return describe_program_expression(object);
            }
            let (base, index) = (
                describe_program_expression(base),
                describe_program_expression(index),
            );
            match object_at_address(&base) {
                Some(object) if index == "0" => object.to_string(),
                // An element of a slice value reads through its data
                // pointer; Rust writes it `x[i]`.
                _ => match base.strip_suffix(".as_ptr()") {
                    Some(slice) => format!("{slice}[{index}]"),
                    None => format!("{base}[{index}]"),
                },
            }
        }
    }
}

/// A load at `pointer`, as a sidecar would write the value read. A load at
/// the address of a reference parameter's referent is the referent: `value`
/// for a scalar, and the field at its start for a struct, `box.first`. A
/// load at a constant offset from a struct pointer parameter where exactly
/// one field starts is that field, `s->len`. Any other load keeps the
/// explicit `load(...)` form.
/// A `kind` read of a field of the struct a loaded pointer points at:
/// `o->b->len`, where `o->b` is that load. The field's declared type must
/// be read with exactly this kind.
pub(in crate::surface) fn diagnostic_loaded_field_load_cell(
    pointer: &Pointer,
    kind: crate::kernel::LoadKind,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    pointer.as_loaded_value()?;
    let (address, offset) = loaded_pointer_base(pointer)?;
    let layout =
        object_fields::ambient_struct_layout(&pointee_struct_at(&address, parameter_binding)?)?;
    let mut fields = layout.fields().iter().filter(|(_, field)| {
        u64::from(field.offset_bytes()) == offset
            && crate::kernel::LoadKind::of_type(field.interface_type().to_kernel_type())
                .is_some_and(|read| read.reads_word_of(kind))
    });
    let (Some((name, _)), None) = (fields.next(), fields.next()) else {
        return None;
    };
    let base = describe_pointer(
        &Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Constant(0),
        },
        parameter_binding,
    );
    is_place_spelling(&base).then(|| describe_field_place(&base, name))
}

/// The place a load of `pointer` reads, when it has a source spelling.
pub(in crate::surface) fn diagnostic_load_place(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let place = describe_load_at(pointer, parameter_binding);
    is_place_spelling(&place).then_some(place)
}

fn describe_load_at(pointer: &Pointer, parameter_binding: ParameterBinding<'_>) -> String {
    if let Some(field) = describe_struct_field_load(pointer, parameter_binding) {
        return field;
    }
    let address = describe_pointer(pointer, parameter_binding);
    let referent = parameter_binding.parameters.iter().find_map(|parameter| {
        (parameter.is_reference() && parameter.name() == address)
            .then(|| syntax::referent_of_carrier(parameter.name()))
            .flatten()
            .map(|referent| (parameter, referent))
    });
    match referent {
        Some((parameter, referent)) => match parameter
            .pointee_struct_layout()
            .or_else(|| parameter.struct_layout())
        {
            None => referent.to_string(),
            Some(layout) => match layout.leaf_field_offsets().find(|(_, offset)| *offset == 0) {
                Some((field, _)) => format!("{referent}.{field}"),
                None => dereference_spelling(&address),
            },
        },
        None => dereference_spelling(&address),
    }
}

/// The place an address spelling reads: `x` for `&x`, the place itself for
/// a cell spelling such as `p[1]` or `the caller's s.f`, and `*p` or
/// `*(p + 1)` otherwise.
fn dereference_spelling(address: &str) -> String {
    if let Some(place) = address.strip_prefix('&')
        && is_place_spelling(place)
    {
        return place.to_string();
    }
    if address.starts_with("the caller's ") || address.ends_with(']') && is_cell_spelling(address) {
        return address.to_string();
    }
    if is_place_spelling(address) {
        format!("*{address}")
    } else {
        format!("*({address})")
    }
}

/// Whether a spelling is a name followed by index brackets, `p[i + 1]`.
fn is_cell_spelling(text: &str) -> bool {
    text.split_once('[')
        .is_some_and(|(base, _)| is_place_spelling(base) && !base.is_empty())
}

/// The field of a struct pointer parameter a load at `pointer` reads, when
/// `pointer` is a constant byte offset from the parameter and exactly one
/// field of its layout starts there. The load carries no width here, so a
/// nested struct or a union whose members share that offset stays a load.
fn describe_struct_field_load(
    pointer: &Pointer,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        if parameter.is_struct_value() || parameter.is_reference() {
            continue;
        }
        let Some(layout) = parameter
            .pointee_struct_layout()
            .or_else(|| parameter.struct_layout())
        else {
            continue;
        };
        let Some(offset) = diagnostic_pointer_element_index_from_base(pointer, base.pointer(), 1)
            .and_then(|offset| offset.as_const())
        else {
            continue;
        };
        let mut fields = layout
            .leaf_field_offsets()
            .filter(|(_, field_offset)| *field_offset == offset);
        if let (Some((field, _)), None) = (fields.next(), fields.next()) {
            return Some(describe_field_place(parameter.name(), field));
        }
    }
    // A field of a struct reached through a pointer some load read:
    // `o->b->data`, where `o->b` is that load.
    let (address, offset) = loaded_pointer_base(pointer)?;
    let layout =
        object_fields::ambient_struct_layout(&pointee_struct_at(&address, parameter_binding)?)?;
    let mut fields = layout
        .leaf_field_offsets()
        .filter(|(_, field_offset)| u64::from(*field_offset) == offset);
    let (Some((field, _)), None) = (fields.next(), fields.next()) else {
        return None;
    };
    let base = describe_load_at(&address, parameter_binding);
    is_place_spelling(&base).then(|| format!("{base}->{field}"))
}

/// `(a, c)` for the address `c` bytes past the pointer a load of `a` read.
fn loaded_pointer_base(address: &Pointer) -> Option<(Pointer, u64)> {
    let (loaded_from, bytes) = loaded_pointer_split(address)?;
    Some((loaded_from, u64::from(bytes.as_const()?)))
}

/// `(a, bytes)` for an address past the pointer a load of `a` read, with
/// the rest of its offset as a byte count, which may be symbolic.
fn loaded_pointer_split(address: &Pointer) -> Option<(Pointer, MachineTerm)> {
    if let Some(read) = address.as_loaded_value() {
        return Some((
            read.defining_address,
            pointer_offset_bytes(&read.displacement)?,
        ));
    }
    if address.block != PointerBlock::ExternalArgument {
        return None;
    }
    let mut summands = Vec::new();
    let mut pending = vec![&address.offset];
    while let Some(offset) = pending.pop() {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            summand => summands.push(summand),
        }
    }
    let loaded = |summand: &PointerOffsetTerm| match summand {
        PointerOffsetTerm::Int32Scaled { value, .. } => match value.structural_value() {
            MachineTerm::Variable(variable)
                if crate::kernel::is_load_variable(variable)
                    && crate::kernel::registered_load_for_variable(variable).is_some() =>
            {
                Some(*variable)
            }
            _ => None,
        },
        _ => None,
    };
    let mut variables = summands.iter().filter_map(|summand| loaded(summand));
    let (Some(variable), None) = (variables.next(), variables.next()) else {
        return None;
    };
    let mut bytes = MachineTerm::constant(0);
    for summand in summands.iter().filter(|summand| loaded(summand).is_none()) {
        bytes = bitvector32_add(bytes, pointer_offset_bytes(summand)?);
    }
    Some((
        crate::kernel::registered_load_for_variable(&variable)?.1,
        bytes,
    ))
}

/// The struct a pointer field at `address` points at, by name: a pointer
/// field of the struct a parameter points at, or of a struct reached
/// through such a field. Display only.
fn pointee_struct_at(address: &Pointer, parameter_binding: ParameterBinding<'_>) -> Option<String> {
    pointee_struct_at_depth(address, parameter_binding, 0)
}

fn pointee_struct_at_depth(
    address: &Pointer,
    parameter_binding: ParameterBinding<'_>,
    depth: usize,
) -> Option<String> {
    if depth > MAX_POINTER_CHAIN {
        return None;
    }
    let field_at = |layout: &crate::languages::interface::RecordLayout, offset: u64| {
        let mut pointers = layout.fields().iter().filter(|(_, field)| {
            u64::from(field.offset_bytes()) == offset && field.interface_type().is_pointer()
        });
        match (pointers.next(), pointers.next()) {
            (Some((_, field)), None) => field.struct_name().map(str::to_string),
            _ => None,
        }
    };
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(ProgramValue::Pointer(base)) = argument else {
            continue;
        };
        if parameter.is_struct_value() || parameter.is_reference() {
            continue;
        }
        let Some(layout) = parameter
            .pointee_struct_layout()
            .or_else(|| parameter.struct_layout())
        else {
            continue;
        };
        if let Some(offset) = diagnostic_pointer_element_index_from_base(address, base.pointer(), 1)
            .and_then(|offset| offset.as_const())
        {
            return field_at(layout, u64::from(offset));
        }
    }
    let (outer, offset) = loaded_pointer_base(address)?;
    let name = pointee_struct_at_depth(&outer, parameter_binding, depth + 1)?;
    field_at(&object_fields::ambient_struct_layout(&name)?, offset)
}

/// How many pointer fields a place spelling follows from a parameter.
const MAX_POINTER_CHAIN: usize = 8;

/// A range past a pointer some load read, spelled from the place the load
/// read: `o->b->data[2]` or `o->b->data[i]`. A pointer to a struct is left
/// to the struct spelling. Display only.
fn describe_loaded_pointer_range(
    range: &MemoryRange,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    range.int32_bounds()?;
    // One element at a wide index past a loaded pointer: `s->data[s->len]`.
    if let Some(read) = range.base().as_loaded_value()
        && let PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } = &read.displacement
        && *byte_width == i64::from(range.element_width())
        && range.constant_start() == Some(0)
        && range.constant_end() == Some(1)
        && pointee_struct_at(&read.defining_address, parameter_binding).is_none()
    {
        let name = describe_load_at(&read.defining_address, parameter_binding);
        return is_place_spelling(&name).then(|| {
            format!(
                "{name}[{}]",
                describe_bitvector_with_context(value.structural_value(), parameter_binding)
            )
        });
    }
    let (address, bytes) = loaded_pointer_split(range.base())?;
    if pointee_struct_at(&address, parameter_binding).is_some() {
        return None;
    }
    let shift = exact_quotient(&bytes, range.element_width())?;
    let name = describe_load_at(&address, parameter_binding);
    if !is_place_spelling(&name) {
        return None;
    }
    let start = bitvector32_add(shift.clone(), range.start().clone());
    let end = bitvector32_add(shift, range.end().clone());
    if is_one_element(&start, &end) {
        return Some(format!(
            "{name}[{}]",
            describe_bitvector_with_context(&start, parameter_binding)
        ));
    }
    Some(format!(
        "{name}[{}..{}]",
        describe_bitvector_with_context(&start, parameter_binding),
        describe_bitvector_with_context(&end, parameter_binding)
    ))
}

/// The object whose address `rendered` spells, when it is `&name`. Reading
/// through that address is the object itself: `(&value)[0]` and `*&value`
/// are `value`, and `(&c)->field` is `c.field`. A reference parameter's
/// carrying pointer is named this way, so its referent prints as the bare
/// name a sidecar writes.
pub(super) fn object_at_address(rendered: &str) -> Option<&str> {
    syntax::referent_of_carrier(rendered)
}

/// A field of the struct `base` points at: `c.field` through an object's
/// address, `p->field` through a pointer.
pub(super) fn describe_field_place(base: &str, field: &str) -> String {
    match object_at_address(base) {
        Some(object) => format!("{object}.{field}"),
        // Rust writes a field through a reference with `.`, and a tuple
        // field, which the importer names `_0`, by its position.
        None if rust_spelling() => {
            let field = field
                .strip_prefix('_')
                .filter(|position| {
                    !position.is_empty() && position.bytes().all(|byte| byte.is_ascii_digit())
                })
                .unwrap_or(field);
            format!("{base}.{field}")
        }
        None => format!("{base}->{field}"),
    }
}

/// The whole object `base` points at: the object itself through its
/// address, `*p` through a pointer.
pub(super) fn describe_pointee_place(base: &str) -> String {
    match object_at_address(base) {
        Some(object) => object.to_string(),
        None => format!("*{base}"),
    }
}

/// A state of `expression`. `result` exists only once the function
/// returns, so a state before the return cannot spell it; it has one
/// value along a path, though, so the state is written around the parts
/// of a C fragment that do not mention it and `result` stays outside, as in
/// `(result as uint64) + at(function.entry, node->word & 1)`.
fn describe_program_point_expression(
    selector: Option<&ProgramPointSelector>,
    expression: &ContractExpression,
) -> String {
    // A read at a call's parameter point is a read through the call's copy
    // of its argument: `R.parameter(v).f[i]`.
    if let Some(ProgramPointSelector::ProgramPoint(point)) = selector
        && point.kind == ProgramPointKind::Parameters
        && let Some(read) = parameter_point_read(&point.region, expression)
    {
        return describe_contract_expression(&read);
    }
    let wrap = |text: String| match selector {
        None => format!("old({text})"),
        Some(selector) => format!("at({}, {text})", describe_program_point_selector(selector)),
    };
    if crate::surface::program_point_can_name_result(selector) {
        return wrap(describe_contract_expression(expression));
    }
    describe_contract_state(expression, &wrap)
}

fn describe_contract_state(
    expression: &ContractExpression,
    wrap: &dyn Fn(String) -> String,
) -> String {
    let mut names = BTreeSet::new();
    crate::surface::collect_current_contract_expression_variables(expression, &mut names);
    if !names.contains("result") {
        return wrap(describe_contract_expression(expression));
    }
    // A constant operand split off from `result` reads no state either.
    let operand = |operand: &ContractExpression| match operand {
        ContractExpression::IntegerLiteral(_)
        | ContractExpression::ProgramExpression(ProgramExpression::Value(_)) => {
            describe_contract_expression(operand)
        }
        operand => describe_contract_state(operand, wrap),
    };
    let binary =
        |left, operator, right| format!("({} {operator} {})", operand(left), operand(right));
    match expression {
        ContractExpression::ProgramExpression(expression) => describe_c_state(expression, wrap),
        // `result` and a scalar cast of it read no state.
        ContractExpression::Binding(_) => describe_contract_expression(expression),
        ContractExpression::CUnary { operand, lowered }
            if matches!(operand.as_ref(), ContractExpression::Binding(_))
                && matches!(
                    lowered,
                    ProgramExpression::Cast {
                        pointee_struct: None,
                        ..
                    }
                ) =>
        {
            describe_contract_expression(expression)
        }
        ContractExpression::Add(left, right) => binary(left, "+", right),
        ContractExpression::Subtract(left, right) => binary(left, "-", right),
        ContractExpression::Multiply(left, right) => binary(left, "*", right),
        ContractExpression::BitwiseAnd(left, right) => binary(left, "&", right),
        ContractExpression::BitwiseOr(left, right) => binary(left, "|", right),
        ContractExpression::BitwiseXor(left, right) => binary(left, "^", right),
        // Any other shape keeps its state whole; the parser then names
        // the state that cannot hold `result`.
        expression => wrap(describe_contract_expression(expression)),
    }
}

fn describe_c_state(expression: &ProgramExpression, wrap: &dyn Fn(String) -> String) -> String {
    let mut names = BTreeSet::new();
    crate::surface::collect_program_expression_variables(expression, &mut names);
    if !names.contains("result") {
        return wrap(describe_program_expression(expression));
    }
    let operand = |operand: &ProgramExpression| match operand {
        ProgramExpression::Value(_) => describe_program_expression(operand),
        operand => describe_c_state(operand, wrap),
    };
    let binary =
        |left, operator, right| format!("({} {operator} {})", operand(left), operand(right));
    match expression {
        // `result` and a scalar cast of it read no state.
        ProgramExpression::Variable(_) => describe_program_expression(expression),
        ProgramExpression::Cast {
            expression: inner,
            pointee_struct: None,
            ..
        } if matches!(inner.as_ref(), ProgramExpression::Variable(_)) => {
            describe_program_expression(expression)
        }
        ProgramExpression::Add(left, right) => binary(left, "+", right),
        ProgramExpression::Subtract(left, right) => binary(left, "-", right),
        ProgramExpression::Multiply(left, right) => binary(left, "*", right),
        ProgramExpression::BitwiseAnd(left, right) => binary(left, "&", right),
        ProgramExpression::BitwiseOr(left, right) => binary(left, "|", right),
        ProgramExpression::BitwiseXor(left, right) => binary(left, "^", right),
        ProgramExpression::Equal(left, right) => binary(left, "==", right),
        ProgramExpression::NotEqual(left, right) => binary(left, "!=", right),
        // Any other shape keeps its state whole; the parser then names
        // the state that cannot hold `result`.
        expression => wrap(describe_program_expression(expression)),
    }
}

pub(super) fn describe_binary_program_expression(
    left: &ProgramExpression,
    operator: &str,
    right: &ProgramExpression,
) -> String {
    format!(
        "({} {operator} {})",
        describe_program_expression(left),
        describe_program_expression(right)
    )
}

/// How much of one statement's own C spelling a diagnostic may carry.
const MAX_STATEMENT_HEAD_BYTES: usize = 512;

/// Names a statement the way its C reads, without its body.
///
/// `Debug` on a statement is an implementation dump: a `While` node carries
/// its whole body, every lowered invariant and effect check, every resource
/// spec, and the states inside them, so its size has no relation to what
/// the reader of a refusal needs. What a refusal needs is which statement the
/// cursor is on, and for a loop or a branch, the guard that produced the
/// successors it is complaining about.
pub(super) fn describe_execution_statement_head(statement: &ProgramStatement) -> String {
    let head = match statement {
        ProgramStatement::EndScalarReference(_) => "borrow end".to_string(),
        ProgramStatement::ScalarReferenceScope(_) => "borrow scope".to_string(),
        ProgramStatement::Skip => ";".to_string(),
        ProgramStatement::Break => "break;".to_string(),
        ProgramStatement::Continue => "continue;".to_string(),
        ProgramStatement::Goto { target } => format!("goto target({});", target.0),
        ProgramStatement::EndAutomaticLifetimes { .. } => "automatic lifetime end".to_string(),
        ProgramStatement::ForStep {
            step,
            continue_after,
            ..
        } => {
            if *continue_after {
                format!(
                    "continue; (with {})",
                    describe_execution_statement_head(step)
                )
            } else {
                describe_execution_statement_head(step)
            }
        }
        ProgramStatement::Declare { name, .. } => format!("declaration of `{name}`"),
        ProgramStatement::DeclareAggregate { name, .. } => {
            format!("aggregate declaration of `{name}`")
        }
        ProgramStatement::CopyAggregate { target, source, .. }
        | ProgramStatement::InitializeScalarArray { target, source, .. } => format!(
            "{} = {};",
            describe_program_expression(target),
            describe_program_expression(source)
        ),
        ProgramStatement::Assign {
            name, expression, ..
        } => {
            format!("{name} = {};", describe_program_expression(expression))
        }
        ProgramStatement::CallConstruct {
            target,
            function_name,
            arguments,
        } => {
            let call = format!(
                "{}({});",
                describe_called_function(function_name),
                describe_program_expression_list(arguments)
            );
            format!("{target} = {call}")
        }
        ProgramStatement::Call {
            function_name,
            arguments,
            ..
        }
        | ProgramStatement::CallResult {
            function_name,
            arguments,
            ..
        } => format!(
            "{}({});",
            describe_called_function(function_name),
            describe_program_expression_list(arguments)
        ),
        ProgramStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
            ends_program_on_failure,
            ..
        } => format!(
            "{target} = {}({});",
            if *ends_program_on_failure {
                "operator new"
            } else if *zeroed {
                "calloc"
            } else {
                "malloc"
            },
            describe_program_expression(bytes)
        ),
        ProgramStatement::HeapFree { pointer } => {
            format!("free({});", describe_program_expression(pointer))
        }
        ProgramStatement::StepValue { expression, .. } => {
            format!("value {};", describe_program_expression(expression))
        }
        ProgramStatement::Assert { condition, label } => format!(
            "assert{}({});",
            label
                .as_ref()
                .map(|label| format!(" {label}"))
                .unwrap_or_default(),
            describe_program_expression(condition)
        ),
        ProgramStatement::Seq(statements) => describe_execution_statement_head(statements.first()),
        ProgramStatement::Return(expression) => {
            format!("return {};", describe_program_expression(expression))
        }
        ProgramStatement::Throw(expression) => {
            format!("throw {};", describe_program_expression(expression))
        }
        ProgramStatement::TryCatchInt32 { binding, .. } => {
            format!("try ... catch (int {binding})")
        }
        ProgramStatement::Store { pointer, value } => format!(
            "*{} = {};",
            describe_program_expression(pointer),
            describe_program_expression(value)
        ),
        ProgramStatement::TypedStore { pointer, value, .. } => format!(
            "*{} = {};",
            describe_program_expression(pointer),
            describe_program_expression(value)
        ),
        ProgramStatement::Update {
            target,
            operator,
            operand,
        } => format!(
            "{} {}= {};",
            describe_program_expression(target),
            describe_c_update_operator(*operator),
            describe_program_expression(operand)
        ),
        ProgramStatement::If { condition, .. } => {
            format!("if ({})", describe_c_guard(condition))
        }
        ProgramStatement::LoopTest { condition } => {
            format!("the loop's test ({})", describe_c_guard(condition))
        }
        ProgramStatement::While {
            condition,
            do_while,
            ..
        } => {
            if *do_while {
                format!("do ... while ({})", describe_c_guard(condition))
            } else {
                format!("while ({})", describe_c_guard(condition))
            }
        }
        ProgramStatement::Switch { expression, .. } => {
            format!("switch ({})", describe_c_guard(expression))
        }
    };
    truncate_utf8_with_suffix(&head, MAX_STATEMENT_HEAD_BYTES, "…")
}

/// The callee as the C names it: a function, or the function pointer a call
/// goes through as the source writes it.
pub(in crate::surface) fn describe_called_function(function_name: &str) -> &str {
    function_name
}

/// A guard already sits inside the parentheses the statement writes, so drop
/// the outermost pair the expression printer adds around a binary operator.
fn describe_c_guard(condition: &ProgramExpression) -> String {
    let rendered = describe_program_expression(condition);
    let Some(inner) = rendered
        .strip_prefix('(')
        .and_then(|rest| rest.strip_suffix(')'))
    else {
        return rendered;
    };
    // Only strip a pair that really encloses the whole expression: `(a) + (b)`
    // starts and ends with a parenthesis without being parenthesized.
    let mut depth = 0usize;
    for character in inner.chars() {
        match character {
            '(' => depth += 1,
            ')' => match depth.checked_sub(1) {
                Some(next) => depth = next,
                None => return rendered,
            },
            _ => {}
        }
    }
    if depth == 0 {
        inner.to_string()
    } else {
        rendered
    }
}

fn describe_program_expression_list(expressions: &[ProgramExpression]) -> String {
    expressions
        .iter()
        .map(describe_program_expression)
        .collect::<Vec<_>>()
        .join(", ")
}

fn describe_c_update_operator(operator: UpdateOperator) -> &'static str {
    match operator {
        UpdateOperator::Add => "+",
        UpdateOperator::Subtract => "-",
        UpdateOperator::Multiply => "*",
        UpdateOperator::Divide => "/",
        UpdateOperator::Remainder => "%",
        UpdateOperator::ShiftLeft => "<<",
        UpdateOperator::ShiftRight => ">>",
        UpdateOperator::BitwiseAnd => "&",
        UpdateOperator::BitwiseOr => "|",
        UpdateOperator::BitwiseXor => "^",
    }
}

fn describe_untyped_array_field_read(
    base: &ContractExpression,
    index: &ContractExpression,
) -> Option<String> {
    // A registered library accessor already carries its element type and
    // is the source spelling used in both certificates and diagnostics.
    if describe_model_accessor(base).is_some() {
        return None;
    }
    let ContractExpression::Field {
        base,
        lowered:
            ProgramExpression::TypedLoad {
                pointer,
                value_type,
                volatile,
                pointee_constant,
                access_class: _,
                source,
            },
        ..
    } = base
    else {
        return None;
    };
    let ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) = base.as_ref()
    else {
        return None;
    };
    // A generated call argument can carry only a scalar pointer type. Its
    // captured field still knows the array type, but the printed field name
    // cannot recover that layout when the certificate is parsed again.
    if REFERENCE_CARRIERS.with(|scopes| {
        scopes
            .borrow()
            .iter()
            .rev()
            .any(|scope| matches!(scope.carriers.get(name), Some(PointeeShape::Struct { .. })))
    }) {
        return None;
    }
    let element_type = match value_type {
        ProgramType::Int8Array(_) => ProgramType::Int8,
        ProgramType::UInt8Array(_) => ProgramType::UInt8,
        ProgramType::Int16Array(_) => ProgramType::Int16,
        ProgramType::UInt16Array(_) => ProgramType::UInt16,
        ProgramType::Int32Array(_) => ProgramType::Int32,
        ProgramType::UInt32Array(_) => ProgramType::UInt32,
        ProgramType::Int64Array(_) => ProgramType::Int64,
        ProgramType::UInt64Array(_) => ProgramType::UInt64,
        ProgramType::Int128Array(_) => ProgramType::Int128,
        ProgramType::UInt128Array(_) => ProgramType::UInt128,
        _ => return None,
    };
    let index = crate::surface::lowering::contract_expression_as_program_expression(index)?;
    let pointer = ProgramExpression::Add(
        Box::new(ProgramExpression::Cast {
            expression: pointer.clone(),
            target_type: ProgramType::UInt8Pointer,
            integer_mode: crate::kernel::IntegerCastMode::CConversion,
            pointee_struct: None,
            pointee_volatile: *volatile,
            pointee_constant: *pointee_constant,
            explicit_qualification: true,
        }),
        Box::new(ProgramExpression::Multiply(
            Box::new(index),
            Box::new(ProgramExpression::Value(int32(element_type.byte_width()))),
        )),
    );
    Some(describe_program_expression(&ProgramExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type: element_type,
        volatile: *volatile,
        pointee_constant: *pointee_constant,
        access_class: None,
        source: source.clone(),
    }))
}

pub(super) fn describe_contract_expression(expression: &ContractExpression) -> String {
    if matches!(expression, ContractExpression::Add(_, _)) {
        return describe_add_contract_expression(expression);
    }
    match expression {
        ContractExpression::Resource(subject) => describe_resource_subject(subject),
        ContractExpression::RegionAllocation(region) => {
            format!("{}.allocation", describe_code_region_ref(region))
        }
        ContractExpression::RegionResult(region) => {
            format!("{}.result", describe_code_region_ref(region))
        }
        ContractExpression::RegionParameter { region, name } => {
            format!("{}.parameter({name})", describe_code_region_ref(region))
        }
        ContractExpression::IntegerLiteral(value) => value.clone(),
        ContractExpression::ResourceField(access) => {
            // A body names its own fields bare; `__body` is the parser's
            // internal owner for them.
            let mut parts = Vec::new();
            if access.owner != "__body" {
                parts.push(access.owner.as_str());
            }
            parts.extend(access.children.iter().map(String::as_str));
            parts.push(access.field.as_str());
            parts.join(".")
        }
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => {
            let type_arguments = if algebraic_type.arguments.is_empty() {
                String::new()
            } else {
                format!(
                    "<{}>",
                    algebraic_type
                        .arguments
                        .iter()
                        .map(describe_click_type)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            };
            let written_arguments = arguments;
            let arguments = arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>();
            if algebraic_type.name == "Slice" && variant == "Slice" && rust_spelling() {
                // A subslice, built from its length's call.
                if let [
                    _,
                    ContractExpression::Call {
                        name,
                        arguments: parts,
                    },
                ] = written_arguments.as_slice()
                    && name == crate::surface::RUST_SUBSLICE_LEN
                    && let [start, end, len] = parts.as_slice()
                    && let Some(subslice) = subslice_of_length(
                        &describe_contract_expression(start),
                        &describe_contract_expression(end),
                        &describe_contract_expression(len),
                    )
                {
                    return subslice;
                }
            }
            format!(
                "{}{type_arguments}::{variant}({})",
                algebraic_type.name,
                arguments.join(", ")
            )
        }
        ContractExpression::AlgebraicVariable { name, .. } | ContractExpression::Binding(name) => {
            name.clone()
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            let scrutinee = describe_contract_expression(scrutinee);
            let arms = arms
                .iter()
                .map(|arm| {
                    format!(
                        "{}::{}({}) => {}",
                        arm.type_name,
                        arm.variant,
                        arm.bindings.join(", "),
                        describe_contract_expression(&arm.body)
                    )
                })
                .collect::<Vec<_>>();
            format!("match {scrutinee} {{ {} }}", arms.join(", "))
        }
        ContractExpression::SequenceLiteral(elements) => format!(
            "[{}]",
            elements
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
        ContractExpression::SequenceConcat(left, right) => {
            describe_binary_contract_expression(left, "++", right)
        }
        ContractExpression::QualifiedC { name, .. } => name.clone(),
        ContractExpression::CUnary { operand, lowered } => {
            let operand = describe_contract_expression(operand);
            match lowered {
                ProgramExpression::Cast {
                    target_type: ProgramType::UInt64,
                    integer_mode: crate::kernel::IntegerCastMode::Standard,
                    pointee_struct: None,
                    ..
                } => format!("address({operand})"),
                ProgramExpression::Cast {
                    target_type,
                    pointee_struct,
                    ..
                } => {
                    if pointee_struct.is_none()
                        && rust_spelling()
                        && let Some(spelling) = rust_scalar_spelling(target_type)
                    {
                        return format!("({operand} as {spelling})");
                    }
                    let spelling = pointee_struct
                        .as_ref()
                        .map(|name| format!("struct {name} *"))
                        .unwrap_or_else(|| {
                            crate::kernel::program_type_spelling(*target_type).to_string()
                        });
                    format!("({})", click_cast(&operand, &spelling))
                }
                ProgramExpression::PointerOffsetBytes { bytes, .. } => {
                    format!("byte_offset({operand}, {bytes})")
                }
                ProgramExpression::TypedLoad { value_type, .. } => format!(
                    "load_{}({operand})",
                    crate::kernel::program_type_spelling(*value_type)
                        .replace(' ', "")
                        .replace('*', "_pointer")
                ),
                ProgramExpression::Load(_) => format!("*({operand})"),
                ProgramExpression::AddressOf(_) => format!("&({operand})"),
                _ => unreachable!("CUnary stores a unary C operation"),
            }
        }
        // A pointer address must retain its specification spelling: a scalar
        // cast is parsed as a C conversion and loses the address operand that
        // keeps tagged-word arithmetic native under Integer arithmetic.
        ContractExpression::ProgramExpression(ProgramExpression::Cast {
            expression,
            target_type: ProgramType::UInt64,
            integer_mode: crate::kernel::IntegerCastMode::Standard,
            pointee_struct: None,
            ..
        }) => format!("address({})", describe_program_expression(expression)),
        ContractExpression::ProgramExpression(expression) => {
            describe_program_expression(expression)
        }
        ContractExpression::Field { .. }
            if let Some(accessor) = describe_model_accessor(expression) =>
        {
            accessor
        }
        // A call's copy of an aggregate argument is an object: its fields
        // are read with `.`, as Rust and a C struct value both write them.
        ContractExpression::Field { base, field, .. }
            if matches!(base.as_ref(), ContractExpression::RegionParameter { .. })
                || matches!(base.as_ref(), ContractExpression::At {
                    selector: ProgramPointSelector::ProgramPoint(point),
                    ..
                } if point.kind == ProgramPointKind::Parameters) =>
        {
            let field = field
                .strip_prefix('_')
                .filter(|position| {
                    !position.is_empty() && position.bytes().all(|byte| byte.is_ascii_digit())
                })
                .unwrap_or(field);
            format!("{}.{field}", describe_contract_expression(base))
        }
        ContractExpression::Field { base, field, .. } => match base.as_ref() {
            // A member of an embedded struct member is reached with `.`:
            // the inner member is an object, which lowers to its address
            // rather than to a load of a pointer.
            ContractExpression::Field { lowered, .. }
                if !matches!(lowered, ProgramExpression::TypedLoad { .. }) =>
            {
                format!("{}.{field}", describe_contract_expression(base))
            }
            _ => describe_field_place(
                &input_struct_pointer_place(base)
                    .unwrap_or_else(|| describe_contract_expression(base)),
                field,
            ),
        },
        ContractExpression::CBinding(name) if rust_spelling() => format!("rust({name})"),
        ContractExpression::CBinding(name) => format!("c({name})"),
        ContractExpression::ResourceWildcard => "_".to_string(),
        ContractExpression::ResourceCount(resource) => {
            // Population patterns name the resource, not the permission of
            // the observation that supplied it. `count(view r(...))` is not
            // syntax, and count lowering ignores that access annotation.
            match resource.as_ref() {
                ResourceClause::Declared {
                    name, arguments, ..
                } => format!(
                    "count({name}({}))",
                    arguments
                        .iter()
                        .map(describe_contract_expression)
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
                _ => format!("count({})", describe_resource_clause(resource)),
            }
        }
        ContractExpression::Old(expression) => describe_program_point_expression(None, expression),
        ContractExpression::At {
            selector,
            expression,
        } => describe_program_point_expression(Some(selector), expression),
        ContractExpression::Negate(expression) => {
            format!("-{}", describe_contract_expression(expression))
        }
        ContractExpression::Add(_, _) => unreachable!("addition is rendered iteratively above"),
        ContractExpression::Subtract(left, right) => {
            describe_binary_contract_expression(left, "-", right)
        }
        ContractExpression::Multiply(left, right) => {
            describe_binary_contract_expression(left, "*", right)
        }
        ContractExpression::Divide(left, right) => {
            describe_binary_contract_expression(left, "/", right)
        }
        ContractExpression::Remainder(left, right) => {
            describe_binary_contract_expression(left, "%", right)
        }
        ContractExpression::ShiftLeft(left, right) => {
            describe_binary_contract_expression(left, "<<", right)
        }
        ContractExpression::RustShiftLeft(left, right) => {
            describe_binary_contract_expression(left, "<<", right)
        }
        ContractExpression::ShiftRight(left, right) => {
            describe_binary_contract_expression(left, ">>", right)
        }
        ContractExpression::RustShiftRight(left, right) => {
            describe_binary_contract_expression(left, ">>", right)
        }
        ContractExpression::BitwiseAnd(left, right) => {
            describe_binary_contract_expression(left, "&", right)
        }
        ContractExpression::BitwiseOr(left, right) => {
            describe_binary_contract_expression(left, "|", right)
        }
        ContractExpression::BitwiseXor(left, right) => {
            describe_binary_contract_expression(left, "^", right)
        }
        ContractExpression::BitwiseNot(expression) => {
            format!("~{}", describe_contract_expression(expression))
        }
        // Qualified C array indices have already been flattened by the
        // parser. Offset the decayed pointer explicitly so reparsing does
        // not interpret this as an incomplete multidimensional subscript.
        ContractExpression::Index(base, index)
            if matches!(base.as_ref(), ContractExpression::QualifiedC { .. }) =>
        {
            format!(
                "({} + {})[0]",
                describe_contract_expression(base),
                describe_contract_expression(index)
            )
        }
        ContractExpression::Index(base, index)
            if let Some(read) = describe_untyped_array_field_read(base, index) =>
        {
            read
        }
        ContractExpression::Index(base, index) => {
            let index = describe_contract_expression(index);
            if index == "0"
                && let ContractExpression::ProgramExpression(
                    ProgramExpression::CheckedObjectAddress(object),
                ) = base.as_ref()
            {
                return describe_program_expression(object);
            }
            let base = describe_contract_expression(base);
            match object_at_address(&base) {
                Some(object) if index == "0" => object.to_string(),
                // An element of a slice value reads through its data
                // pointer; Rust writes it `x[i]`.
                _ => match base.strip_suffix(".as_ptr()") {
                    Some(slice) => format!("{slice}[{index}]"),
                    None => format!("{base}[{index}]"),
                },
            }
        }
        ContractExpression::ArrayIndex { base, indexes, .. } => format!(
            "{}{}",
            describe_contract_expression(base),
            indexes
                .iter()
                .map(|index| format!("[{}]", describe_contract_expression(index)))
                .collect::<String>()
        ),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => format!(
            // This describer also prints expanded proof text, so a
            // conditional must come back as the syntax that wrote it. The
            // parentheses are what let the result sit where a term is
            // expected, as in `result == (if c { a } else { b })`.
            "(if {} {{ {} }} else {{ {} }})",
            printing::source_click_proposition(condition),
            describe_contract_expression(then_branch),
            describe_contract_expression(else_branch)
        ),
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => format!(
            "({}..{}).fold({}, |{accumulator}, {item}| {{ {} }})",
            describe_contract_expression(start),
            describe_contract_expression(end),
            describe_contract_expression(initial),
            describe_contract_expression(body)
        ),
        ContractExpression::Let {
            click_type: Some(ClickType::Integer),
            ..
        } => {
            // Retain the type when printing checked evidence and flatten a
            // chain of lexical aliases into one parenthesized expression.
            let mut output = String::from("(");
            let mut body = expression;
            while let ContractExpression::Let {
                name,
                click_type: Some(ClickType::Integer),
                value,
                body: next,
            } = body
            {
                output.push_str(&format!(
                    "let {name}: Integer = {}; ",
                    describe_let_value(value)
                ));
                body = next;
            }
            output.push_str(&describe_let_value(body));
            output.push(')');
            output
        }
        // A machine-typed `let` keeps its annotation: the type is the
        // expected type of its value's arithmetic.
        ContractExpression::Let {
            name,
            click_type: Some(click_type),
            value,
            body,
        } => format!(
            "(let {name}: {} = {}; {})",
            describe_let_type(click_type),
            describe_let_value(value),
            describe_let_value(body)
        ),
        ContractExpression::Let {
            name, value, body, ..
        } => format!(
            "(let {name} = {}; {})",
            describe_let_value(value),
            describe_let_value(body)
        ),
        ContractExpression::MethodCall {
            receiver,
            method,
            arguments,
        } => {
            let receiver = describe_contract_expression(receiver);
            let receiver = if receiver.contains(' ') {
                format!("({receiver})")
            } else {
                receiver
            };
            let arguments = arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>();
            match (method.as_str(), arguments.as_slice()) {
                ("[]", [index]) => format!("{receiver}[{index}]"),
                ("[..]", []) => format!("{receiver}[..]"),
                ("[a..]", [start]) => format!("{receiver}[{start}..]"),
                ("[..b]", [end]) => format!("{receiver}[..{end}]"),
                ("[a..b]", [start, end]) => format!("{receiver}[{start}..{end}]"),
                _ => format!("{receiver}.{method}({})", arguments.join(", ")),
            }
        }
        ContractExpression::Call { name, arguments } => {
            let arguments = slice_call_arguments(
                name,
                arguments.iter().map(describe_contract_expression).collect(),
            );
            slice_call_spelling(name, &arguments)
                .unwrap_or_else(|| format!("{name}({})", arguments.join(", ")))
        }
    }
}

fn describe_add_contract_expression(expression: &ContractExpression) -> String {
    // The parser already associates a flat sum to the left. Walk only that
    // spine: reassociating the right operand could change C overflow or
    // pointer arithmetic, even though it is harmless for mathematical Integers.
    // Append once rather than copying every growing prefix of a long sum.
    let mut left = expression;
    let mut rights = Vec::new();
    while let ContractExpression::Add(first, second) = left {
        rights.push(second.as_ref());
        left = first;
    }
    let mut output = format!("({}", describe_contract_expression(left));
    for right in rights.into_iter().rev() {
        output.push_str(" + ");
        output.push_str(&describe_contract_expression(right));
    }
    output.push(')');
    output
}

/// A `let` annotation as the file's language spells it.
fn describe_let_type(click_type: &ClickType) -> String {
    let name = describe_click_type(click_type);
    if !rust_spelling() {
        return name;
    }
    match name.as_str() {
        "int8" => "i8",
        "int16" => "i16",
        "int32" => "i32",
        "int64" => "i64",
        "uint8" => "u8",
        "uint16" => "u16",
        "uint32" => "u32",
        "uint64" => "u64",
        "int128" => "i128",
        "uint128" => "u128",
        other => other,
    }
    .to_string()
}

/// Keep generated let bindings source-printable for long left-associated
/// addition chains. The binding value is a top-level expression, so flattening
/// only `+` nodes preserves precedence while avoiding artificial nesting.
fn describe_let_value(value: &ContractExpression) -> String {
    if !matches!(value, ContractExpression::Add(_, _)) {
        return describe_contract_expression(value);
    }
    let mut pending = vec![value];
    let mut terms = Vec::new();
    while let Some(expression) = pending.pop() {
        match expression {
            ContractExpression::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            expression => terms.push(describe_contract_expression(expression)),
        }
    }
    terms.join(" + ")
}

pub(super) fn describe_binary_contract_expression(
    left: &ContractExpression,
    operator: &str,
    right: &ContractExpression,
) -> String {
    format!(
        "({} {operator} {})",
        describe_contract_expression(left),
        describe_contract_expression(right)
    )
}

/// The `aligned(p, n)` sugar behind `address(p) & (n - 1) == 0`, so a
/// generated or expanded alignment fact renders in its source spelling.
pub(super) fn aligned_sugar(proposition: &ClickProposition) -> Option<(&ProgramExpression, u64)> {
    let ClickProposition::Comparison {
        left,
        operator: ComparisonOperator::Equal,
        right,
    } = proposition
    else {
        return None;
    };
    aligned_comparison_sugar(left, right)
}

/// The same sugar for an alignment fact read at one state, whose sides
/// are each qualified `at(S, address(p) & (n - 1)) == at(S, 0u64)`, as a
/// function-entry alignment fact is when it is cited after execution. It
/// renders as `at(S, aligned(p, n))`. The pointer-to-`uint64` conversion
/// inside has no cast spelling in Click (only `address(p)` or `aligned`),
/// so rendering the qualified sides expression by expression would emit an
/// unparseable `p as uint64`.
pub(super) fn program_point_aligned_sugar(
    proposition: &ClickProposition,
) -> Option<(&ProgramPointSelector, &ProgramExpression, u64)> {
    let ClickProposition::Comparison {
        left: ContractExpression::At {
            selector,
            expression: left,
        },
        operator: ComparisonOperator::Equal,
        right,
    } = proposition
    else {
        return None;
    };
    let right = match right {
        ContractExpression::At {
            selector: right_selector,
            expression,
        } if right_selector == selector => expression.as_ref(),
        ContractExpression::At { .. } => return None,
        right => right,
    };
    let (pointer, alignment) = aligned_comparison_sugar(left, right)?;
    Some((selector, pointer, alignment))
}

fn aligned_comparison_sugar<'a>(
    left: &'a ContractExpression,
    right: &ContractExpression,
) -> Option<(&'a ProgramExpression, u64)> {
    let ContractExpression::BitwiseAnd(address, mask) = left else {
        return None;
    };
    let ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(zero))) =
        right
    else {
        return None;
    };
    if zero.uint64_as_const() != Some(0) {
        return None;
    }
    let ContractExpression::ProgramExpression(ProgramExpression::Cast {
        expression: pointer,
        target_type: ProgramType::UInt64,
        ..
    }) = address.as_ref()
    else {
        return None;
    };
    let ContractExpression::ProgramExpression(ProgramExpression::Value(ProgramValue::UInt64(mask))) =
        mask.as_ref()
    else {
        return None;
    };
    let alignment = mask.uint64_as_const()?.checked_add(1)?;
    alignment
        .is_power_of_two()
        .then_some((pointer.as_ref(), alignment))
}

pub(super) fn describe_click_proposition(proposition: &ClickProposition) -> String {
    printing::print_proposition(proposition, printing::PropositionSpelling::Diagnostic)
}

pub(super) fn describe_program_point_selector(selector: &ProgramPointSelector) -> String {
    match selector {
        ProgramPointSelector::ProgramPoint(point) => describe_program_point_ref(point),
        ProgramPointSelector::Mark(name) => name.clone(),
    }
}

thread_local! {
    /// The source layout of the function whose proof is being checked, while
    /// a [`SourcePathSpellingScope`] is alive: a `region(N)` point prints as
    /// the path through the statements as written that names it.
    static SPELLING_LAYOUT: std::cell::RefCell<Option<crate::surface::lowering::SourceExecutionLayout>> =
        const { std::cell::RefCell::new(None) };
}

/// The source layout of the function whose proof is being checked, if any.
pub(in crate::surface) fn spelling_layout()
-> Option<crate::surface::lowering::SourceExecutionLayout> {
    SPELLING_LAYOUT.with(|slot| slot.borrow().clone())
}

/// Spells `region(N)` points by the statements as written while alive.
pub(in crate::surface) struct SourcePathSpellingScope(
    Option<crate::surface::lowering::SourceExecutionLayout>,
);

impl SourcePathSpellingScope {
    pub(in crate::surface) fn enter(
        layout: &crate::surface::lowering::SourceExecutionLayout,
    ) -> Self {
        Self(SPELLING_LAYOUT.with(|slot| slot.replace(Some(layout.clone()))))
    }
}

impl Drop for SourcePathSpellingScope {
    fn drop(&mut self) {
        SPELLING_LAYOUT.with(|slot| {
            slot.replace(self.0.take());
        });
    }
}

/// `point` as a proof writes it: a `region(N)` point by the path through the
/// statements as written that names it, when the function being checked has
/// one; see [`describe_program_point_ref_as_recorded`] for the recorded form.
pub(super) fn describe_program_point_ref(point: &ProgramPointRef) -> String {
    if let CodeRegionRef::Region(index) = point.region
        && let Some(steps) = SPELLING_LAYOUT.with(|slot| {
            slot.borrow()
                .as_ref()?
                .source_path_spelling(index, point.kind)
        })
    {
        return describe_program_point_ref_as_recorded(&ProgramPointRef {
            region: CodeRegionRef::Path(steps),
            kind: point.kind,
        });
    }
    describe_program_point_ref_as_recorded(point)
}

/// The statement at `region` as a proof names it: the path through the
/// statements as written (`statement(5)`) when the function being checked
/// has one, as [`describe_program_point_ref`] spells its points, and
/// `region(N)` otherwise. Both lower back to this statement.
pub(in crate::surface) fn describe_statement_region(region: usize) -> String {
    let point = ProgramPointRef {
        region: CodeRegionRef::Region(region),
        kind: ProgramPointKind::Entry,
    };
    if let Some(steps) = SPELLING_LAYOUT.with(|slot| {
        slot.borrow()
            .as_ref()?
            .source_path_spelling(region, point.kind)
    }) {
        return describe_code_region_ref(&CodeRegionRef::Path(steps));
    }
    describe_code_region_ref(&point.region)
}

/// `point` exactly as it is spelled, `region(N)` included.
pub(super) fn describe_program_point_ref_as_recorded(point: &ProgramPointRef) -> String {
    let kind = match point.kind {
        ProgramPointKind::Entry => "entry",
        ProgramPointKind::Exit => "exit",
        ProgramPointKind::Parameters => {
            return format!(
                "the parameters `{}` bound",
                describe_code_region_ref(&point.region)
            );
        }
    };
    format!("{}.{}", describe_code_region_ref(&point.region), kind)
}

pub(super) fn describe_code_region_ref(region: &CodeRegionRef) -> String {
    match region {
        CodeRegionRef::Function => "function".to_string(),
        CodeRegionRef::FunctionExit => "function.exit".to_string(),
        CodeRegionRef::Loop(index) => format!("loop({index})"),
        CodeRegionRef::Read(index) => format!("read({index})"),
        CodeRegionRef::BackEdge(None) => "back_edge()".into(),
        CodeRegionRef::BackEdge(Some(index)) => format!("loop({index}).back_edge()"),
        CodeRegionRef::Region(index) => format!("region({index})"),
        CodeRegionRef::Label(name) => name.clone(),
        CodeRegionRef::Assignment { local, occurrence } => {
            format!("assignment({local}, {occurrence})")
        }
        CodeRegionRef::Path(steps) => steps
            .iter()
            .map(|step| match step {
                SourcePathStep::Statement(index) => format!("statement({index})"),
                SourcePathStep::Loop(index) => format!("loop({index})"),
                SourcePathStep::Region(index) => format!("region({index})"),
                SourcePathStep::Call(function, index) => format!("call({function}, {index})"),
                SourcePathStep::AnyCall(index) => format!("call({index})"),
                SourcePathStep::Test => "test()".to_string(),
                SourcePathStep::Assignment(local, index) => format!("assignment({local}, {index})"),
                SourcePathStep::Operator(kind, index) => {
                    format!("{}({index})", operator_step_name(*kind))
                }
                SourcePathStep::Read(index) => format!("read({index})"),
                SourcePathStep::ReadEvent(index) => format!("read_event({index})"),
            })
            .collect::<Vec<_>>()
            .join("."),
    }
}

/// A kernel variable no local, parameter, load, or model field names: a term
/// only the lowering has a name for. It reads `…`, never as the kernel's
/// variable id, which is an identity the reader cannot write
/// (`docs/internals/resource-tracker.md`). `CLICK_FULL_DIAGNOSTICS` keeps the
/// id for engine debugging.
fn lowering_only_variable(prefix: &str, id: u64) -> String {
    if std::env::var_os(FULL_DIAGNOSTICS_ENV).is_some() {
        format!("{prefix}{id}")
    } else {
        "…".to_string()
    }
}

pub(super) fn describe_bitvector(term: &MachineTerm) -> String {
    describe_bitvector_with_context(term, ParameterBinding::default())
}

pub(super) fn describe_bitvector_with_context(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    if let Some(name) = describe_parameter_bitvector(term, parameter_binding) {
        return name;
    }
    match term {
        MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value,
            to: destination,
            ..
        } => format!(
            "({})",
            click_cast(
                &describe_bitvector_with_context(value, parameter_binding),
                &format!("{destination:?}").to_ascii_lowercase()
            )
        ),

        int32_constant!(value) => format!("{}", constant_u32(*value) as i32),
        uint32_constant!(value) => format!("{value}u32", value = constant_u32(*value)),
        int64_constant!(value) => format!("{value}i64", value = constant_i64(*value)),
        uint64_constant!(value) => format!("{value}u64", value = constant_u64(*value)),
        crate::kernel::native_constant!(format, bits) if format.format().bits() < 32 => {
            crate::kernel::MachineIntegerConstant::from_term_bits(format.format(), *bits)
                .to_integer()
                .to_string()
        }
        crate::kernel::native_constant!(format, bits) => format!(
            "{}{}128",
            crate::kernel::MachineIntegerConstant::from_term_bits(format.format(), *bits)
                .to_integer(),
            if format.format().is_signed() {
                "i"
            } else {
                "u"
            }
        ),
        // A diagnostic prints the load represented by a load variable,
        // never the kernel variable's id.
        MachineTerm::Variable(variable)
            if crate::kernel::is_load_variable(variable)
                && crate::kernel::registered_load_for_variable(variable).is_some() =>
        {
            let (_, pointer) = crate::kernel::registered_load_for_variable(variable)
                .expect("checked registered above");
            describe_load_at(&pointer, parameter_binding)
        }
        // And a model-field variable prints as the field it is. The value is
        // stored inside the instance fact, so there is nothing in the term to
        // recover it from; the mint registered it.
        MachineTerm::Variable(variable)
            if crate::kernel::model_fields::model_field_spelling(*variable).is_some() =>
        {
            crate::kernel::model_fields::model_field_spelling(*variable)
                .expect("checked registered above")
        }
        MachineTerm::Variable(variable) => lowering_only_variable("v", variable.0),
        unary_term!(Int32, BitwiseNot, value) => {
            format!(
                "~{}",
                describe_bitvector_with_context(value, parameter_binding)
            )
        }
        MachineTerm::Float32Negate(value) | MachineTerm::Float64Negate(value) => {
            format!(
                "-{}",
                describe_bitvector_with_context(value, parameter_binding)
            )
        }
        cast_term!(Int64From32, value) | cast_term!(Int64FromUInt32, value) => format!(
            "({})",
            click_cast(
                &describe_bitvector_with_context(value, parameter_binding),
                "int64"
            )
        ),
        cast_term!(UInt64From32, value)
        | cast_term!(UInt64FromInt32, value)
        | cast_term!(UInt64FromInt64, value) => format!(
            "({})",
            click_cast(
                &describe_bitvector_with_context(value, parameter_binding),
                "uint64"
            )
        ),
        cast_term!(UInt32From64, value) => format!(
            "({})",
            click_cast(
                &describe_bitvector_with_context(value, parameter_binding),
                "uint32"
            )
        ),
        MachineTerm::Unary { operand: value, .. } => {
            format!(
                "~{}",
                describe_bitvector_with_context(value, parameter_binding)
            )
        }
        MachineTerm::If {
            condition,
            then_term,
            else_term,
        } => format!(
            "(if {} {{ {} }} else {{ {} }})",
            describe_condition_with_context(condition, parameter_binding),
            describe_bitvector_with_context(then_term, parameter_binding),
            describe_bitvector_with_context(else_term, parameter_binding)
        ),
        // A fold body is an arbitrary term over its own binders, so it has no
        // shorter source spelling; render it through the bounded proposition
        // printer rather than dumping the developer structure.
        MachineTerm::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            let _ = (accumulator, item);
            format!(
                "({}..{}).fold({}, |acc, k| {{ {} }})",
                describe_bitvector_with_context(start, parameter_binding),
                describe_bitvector_with_context(end, parameter_binding),
                describe_bitvector_with_context(initial, parameter_binding),
                describe_bitvector_with_context(body, parameter_binding)
            )
        }
        MachineTerm::PureFunctionApplication {
            name,
            arguments: values,
        } => format!(
            "{}({})",
            name,
            values
                .iter()
                .map(|argument| { describe_bitvector_with_context(argument, parameter_binding) })
                .collect::<Vec<_>>()
                .join(", ")
        ),
        MachineTerm::ClickFunctionApplication { name, .. } => {
            format!("{name}(<typed Click arguments>)")
        }
        MachineTerm::AlgebraicMatch { .. } => "match <algebraic value> { ... }".to_string(),
        MachineTerm::MemoryLoad(_, pointer, _) => describe_load_at(pointer, parameter_binding),
        MachineTerm::PointerAddress(pointer, _) => {
            format!(
                "({})",
                click_cast(&describe_pointer(pointer, parameter_binding), "uint64")
            )
        }
        MachineTerm::IntegerToMachine { value, destination } => format!(
            "to_{}({})",
            format!("{destination:?}").to_ascii_lowercase(),
            describe_integer_term(value)
        ),
        // Rule C1: a specification `Bool` travels as its cast to `uint8`,
        // which reads as the `Bool` itself; any other format is the cast.
        MachineTerm::BoolCast { to, value } => {
            let condition = describe_condition_with_context(value, parameter_binding);
            if *to == crate::kernel::MachineIntegerType::UInt8 {
                condition
            } else {
                format!(
                    "({})",
                    click_cast(
                        &format!("({condition})"),
                        &format!("{to:?}").to_ascii_lowercase()
                    )
                )
            }
        }
        term => {
            let (operator, left, right) = term
                .as_binary()
                .expect("every other variant has its own arm");
            describe_binary_bitvector_with_context(
                left,
                operator.program_symbol(),
                right,
                parameter_binding,
            )
        }
    }
}

pub(super) fn describe_parameter_bitvector(
    term: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        match argument {
            ProgramExpression::Value(value @ ProgramValue::PointerInteger(_)) => {
                if let ProgramValue::Int64(bits) | ProgramValue::UInt64(bits) =
                    value.numeric_value()
                    && bits == term
                    && value.program_type() == parameter.interface_type().to_kernel_type()
                {
                    return Some(parameter.name().to_string());
                }
            }
            ProgramExpression::Value(ProgramValue::Int32(value))
                if value == term && parameter.interface_type() == InterfaceType::Int32 =>
            {
                return Some(parameter.name().to_string());
            }
            ProgramExpression::Value(ProgramValue::UInt8(value))
                if value == term
                    && parameter.interface_type().to_kernel_type()
                        == crate::kernel::ProgramType::UInt8 =>
            {
                return Some(parameter.name().to_string());
            }
            ProgramExpression::Value(ProgramValue::Int8(value))
                if value == term
                    && parameter.interface_type().to_kernel_type()
                        == crate::kernel::ProgramType::Int8 =>
            {
                return Some(parameter.name().to_string());
            }
            ProgramExpression::Value(ProgramValue::Int16(value))
                if value == term && parameter.interface_type() == InterfaceType::Int16 =>
            {
                return Some(parameter.name().to_string());
            }
            ProgramExpression::Value(ProgramValue::UInt16(value))
                if value == term && parameter.interface_type() == InterfaceType::UInt16 =>
            {
                return Some(parameter.name().to_string());
            }
            ProgramExpression::Value(ProgramValue::UInt32(value))
                if value == term && parameter.interface_type() == InterfaceType::UInt32 =>
            {
                return Some(parameter.name().to_string());
            }
            ProgramExpression::Value(ProgramValue::Int64(value))
                if value == term
                    && matches!(parameter.interface_type(), InterfaceType::Int64(_)) =>
            {
                return Some(parameter.name().to_string());
            }
            ProgramExpression::Value(ProgramValue::UInt64(value))
                if value == term
                    && matches!(parameter.interface_type(), InterfaceType::UInt64(_)) =>
            {
                return Some(parameter.name().to_string());
            }
            _ => {}
        }
    }
    None
}

pub(super) fn describe_binary_bitvector_with_context(
    left: &MachineTerm,
    operator: &str,
    right: &MachineTerm,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    format!(
        "({} {operator} {})",
        describe_bitvector_with_context(left, parameter_binding),
        describe_bitvector_with_context(right, parameter_binding)
    )
}

/// [`describe_pointer_offset`] with each scaled index spelled in the
/// caller's names where it has them (`j * 4` rather than `… * 4`).
fn describe_pointer_offset_with_context(
    offset: &PointerOffsetTerm,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    match offset {
        PointerOffsetTerm::Add(left, right) => format!(
            "({} + {})",
            describe_pointer_offset_with_context(left, parameter_binding),
            describe_pointer_offset_with_context(right, parameter_binding)
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => format!(
            "{} * {byte_width}",
            describe_bitvector_with_context(value.structural_value(), parameter_binding)
        ),
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => {
            let signedness = if *unsigned { "uint64" } else { "int64" };
            format!(
                "{signedness}({}) * {byte_width}",
                describe_bitvector_with_context(value.structural_value(), parameter_binding)
            )
        }
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {
            describe_pointer_offset(offset)
        }
    }
}

/// The writes to file-scope or static storage that no owned range covers, in
/// source terms and at most the diagnostic item limit of them: each store's
/// width and address, or the range a callee's summary may write.
pub(super) fn describe_storage_writes_outside_footprint(
    escapes: &[crate::kernel::StorageWriteOutsideFootprint],
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let limit = diagnostic_item_limit();
    let mut entries = escapes
        .iter()
        .take(limit)
        .map(|escape| describe_storage_write_outside_footprint(escape, parameter_binding))
        .collect::<Vec<_>>();
    if escapes.len() > limit {
        entries.push(format!("… {} more omitted", escapes.len() - limit));
    }
    entries.join(", ")
}

fn describe_storage_write_outside_footprint(
    escape: &crate::kernel::StorageWriteOutsideFootprint,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    match escape {
        crate::kernel::StorageWriteOutsideFootprint::Write { pointer, bytes } => {
            // A store that fills exactly one scalar field of a struct-typed
            // global names that field (`shared.first`), not its address.
            if let (PointerOffsetTerm::Constant(offset), PointerBlock::Concrete(block)) =
                (&pointer.offset, &pointer.block)
                && let Ok(offset) = u32::try_from(*offset)
                && let Some(field) = object_fields::object_field_spelling(block, offset, *bytes)
            {
                return format!("the {bytes}-byte store to `{field}`");
            }
            format!(
                "the {bytes}-byte store to `{}`",
                describe_pointer(pointer, parameter_binding)
            )
        }
        crate::kernel::StorageWriteOutsideFootprint::Range(range) => format!(
            "the range `{}` a callee may write",
            describe_memory_range(range, parameter_binding)
        ),
    }
}

pub(super) fn describe_pointer_offset(offset: &PointerOffsetTerm) -> String {
    match offset {
        PointerOffsetTerm::Constant(value) => value.to_string(),
        PointerOffsetTerm::Variable(variable) => lowering_only_variable("off", variable.0),
        PointerOffsetTerm::Add(left, right) => format!(
            "({} + {})",
            describe_pointer_offset(left),
            describe_pointer_offset(right)
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            format!(
                "{} * {byte_width}",
                describe_bitvector(value.structural_value())
            )
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } => {
            let signedness = if *unsigned { "uint64" } else { "int64" };
            format!(
                "{signedness}({}) * {byte_width}",
                describe_bitvector(value.structural_value())
            )
        }
    }
}

/// Renders an exact-arithmetic comparison through the bounded term printer.
///
/// An `IntegerTerm` can carry a pure-function application or an algebraic
/// elimination, so its `Debug` reaches the whole instantiated datatype schema
/// graph the way a proposition's does.
fn describe_integer_comparison(
    left: &crate::kernel::SharedIntegerTerm,
    operator: &str,
    right: &crate::kernel::SharedIntegerTerm,
) -> String {
    crate::surface::proof_diagnostics::render::render_integer_comparison(left, operator, right)
}

fn describe_integer_term(term: &crate::kernel::IntegerTerm) -> String {
    crate::surface::proof_diagnostics::render::render_integer_term(term)
}

pub(super) fn describe_condition(condition: &ConditionTerm) -> String {
    if let Some(unsigned) = describe_unsigned_comparison(condition, ParameterBinding::default()) {
        return unsigned;
    }
    if let Some((operator, left, right)) = condition.as_bitvector_comparison() {
        return if operator.is_overflow() {
            format!(
                "overflow({} {} {})",
                describe_bitvector(left),
                operator.program_symbol(),
                describe_bitvector(right)
            )
        } else {
            describe_binary_condition(left, operator.program_symbol(), right)
        };
    }
    match condition {
        ConditionTerm::PointerValueEqual(left, right) => format!(
            "{} == {}",
            describe_pointer(left.pointer(), ParameterBinding::default()),
            describe_pointer(right.pointer(), ParameterBinding::default())
        ),

        ConditionTerm::AlgebraicEqual(_, _) => "algebraic equality".to_string(),
        ConditionTerm::IntegerLessThan(left, right) => {
            describe_integer_comparison(left, "<", right)
        }
        ConditionTerm::IntegerLessEqual(left, right) => {
            describe_integer_comparison(left, "<=", right)
        }
        ConditionTerm::IntegerGreaterThan(left, right) => {
            describe_integer_comparison(left, ">", right)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            describe_integer_comparison(left, ">=", right)
        }
        ConditionTerm::IntegerEqual(left, right) => describe_integer_comparison(left, "==", right),
        ConditionTerm::IntegerNotEqual(left, right) => {
            describe_integer_comparison(left, "!=", right)
        }
        ConditionTerm::Constant(value) => value.to_string(),
        ConditionTerm::Variable(variable) => lowering_only_variable("cond", variable.0),
        ConditionTerm::Float32(float_condition) => describe_float_condition(float_condition),
        ConditionTerm::Float64(float_condition) => describe_float_condition(float_condition),
        ConditionTerm::PointerOffsetEqual(left, right) => format!(
            "{} == {}",
            describe_pointer_offset(left),
            describe_pointer_offset(right)
        ),
        ConditionTerm::PointerEqual(left, right) => {
            format!(
                "{} == {}",
                describe_pointer(left, ParameterBinding::default()),
                describe_pointer(right, ParameterBinding::default())
            )
        }
        crate::kernel::ConditionTerm::Compare { .. }
        | crate::kernel::ConditionTerm::Overflows { .. } => {
            unreachable!("bitvector comparisons are described above")
        }
        // The Surface spellings of the `Bool` value forms, as the
        // word-valued application and load are described.
        ConditionTerm::BoolApplication(application) => {
            format!("{}(<typed Click arguments>)", application.name())
        }
        ConditionTerm::BoolIf {
            condition,
            then_condition,
            else_condition,
        } => format!(
            "if {} {{ {} }} else {{ {} }}",
            describe_condition(condition),
            describe_condition(then_condition),
            describe_condition(else_condition)
        ),
        ConditionTerm::BoolEqual(left, right) => format!(
            "({}) == ({})",
            describe_condition(left),
            describe_condition(right)
        ),
        ConditionTerm::BoolLoad(_, pointer) => {
            describe_load_at(pointer, ParameterBinding::default())
        }
    }
}

/// A fact spelled with its operands through the C parameter names, for a
/// message that must show two lowered terms side by side, such as a rewrite
/// whose equality was not found in its goal. It is [`describe_pure_fact`],
/// which now spells a condition's operands itself.
pub(super) fn describe_pure_fact_spelled(
    fact: &Proposition,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    describe_pure_fact(fact, parameter_binding)
}

/// A stated fact uses the same checked-proposition display as every goal.
pub(super) fn describe_stated_fact(
    fact: &Proposition,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    describe_pure_fact(fact, parameter_binding)
}

/// [`describe_condition`] with machine operands spelled through the C
/// parameter names; shapes with no parameter-named operands fall back to
/// the context-free rendering.
pub(super) fn describe_condition_with_context(
    condition: &ConditionTerm,
    parameter_binding: ParameterBinding<'_>,
) -> String {
    let binary = |left: &MachineTerm, operator: &str, right: &MachineTerm| {
        format!(
            "{} {operator} {}",
            describe_bitvector_with_context(left, parameter_binding),
            describe_bitvector_with_context(right, parameter_binding)
        )
    };
    if let Some(unsigned) = describe_unsigned_comparison(condition, parameter_binding) {
        return unsigned;
    }
    match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } => binary(left, "==", right),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::LessThan,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => binary(left, "<", right),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::LessEqual,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => binary(left, "<=", right),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => binary(left, ">", right),
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => binary(left, ">=", right),
        ConditionTerm::PointerEqual(left, right) => format!(
            "{} == {}",
            describe_pointer(left, parameter_binding),
            describe_pointer(right, parameter_binding)
        ),
        other => describe_condition(other),
    }
}

/// A `uint32` order, spelled with its operands read as `uint32` values and
/// marked `(unsigned)`, so it never reads as the signed comparison of the
/// same operands.
fn describe_unsigned_comparison(
    condition: &ConditionTerm,
    parameter_binding: ParameterBinding<'_>,
) -> Option<String> {
    let ConditionTerm::Compare {
        format: MachineIntegerType::UInt32,
        relation:
            relation @ (crate::kernel::CompareRelation::LessThan
            | crate::kernel::CompareRelation::LessEqual
            | crate::kernel::CompareRelation::GreaterThan
            | crate::kernel::CompareRelation::GreaterEqual),
        left,
        right,
    } = condition
    else {
        return None;
    };
    let operator = match relation {
        CompareRelation::LessThan => "<",
        CompareRelation::LessEqual => "<=",
        CompareRelation::GreaterThan => ">",
        CompareRelation::GreaterEqual => ">=",
        // A `uint32` equality spells a constant operand in its own type
        // (rule K6).
        CompareRelation::Equal => {
            let operand = |term: &MachineTerm| match term.as_const() {
                Some(value) => format!("{value}u32"),
                None => describe_bitvector_with_context(term, parameter_binding),
            };
            return Some(format!("{} == {}", operand(left), operand(right)));
        }
    };
    let operand = |term: &MachineTerm| match term.as_const() {
        Some(value) => value.to_string(),
        None => describe_bitvector_with_context(term, parameter_binding),
    };
    Some(format!(
        "{} {operator} {} (unsigned)",
        operand(left),
        operand(right)
    ))
}

pub(super) fn describe_binary_condition(
    left: &MachineTerm,
    operator: &str,
    right: &MachineTerm,
) -> String {
    format!(
        "{} {operator} {}",
        describe_bitvector(left),
        describe_bitvector(right)
    )
}

fn describe_float_condition(condition: &FloatCondition) -> String {
    match condition {
        FloatCondition::Comparison {
            operator,
            left,
            right,
        } => {
            let operator = match operator {
                KernelComparisonOperator::Equal => "==",
                KernelComparisonOperator::NotEqual => "!=",
                KernelComparisonOperator::LessThan => "<",
                KernelComparisonOperator::LessEqual => "<=",
                KernelComparisonOperator::GreaterThan => ">",
                KernelComparisonOperator::GreaterEqual => ">=",
            };
            describe_binary_condition(left, operator, right)
        }
        FloatCondition::Classification {
            classification,
            value,
        } => format!("is{classification:?}({})", describe_bitvector(value)),
    }
}

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // Native missing resources can reach both source-spelling and repair hints.
    #[test]
    fn wide_missing_ranges_are_rendered_or_omitted_without_signed_readers() {
        let base = Pointer::symbolic(Variable(985_400));
        let wide = MemoryRange::new_wide(
            base,
            MachineTerm::uint64_constant(0),
            MachineTerm::uint64_constant(1 << 33),
            1,
        );
        assert!(describe_source_range(&wide, ParameterBinding::default()).is_none());
        let resource = ResourceFact::view_memory(wide);
        let error = crate::kernel::RuntimeError::MissingResource {
            resource: Box::new(resource.clone()),
        };
        assert!(
            describe_missing_range_end_note(&error, &[resource], ParameterBinding::default())
                .is_empty()
        );
    }
}

#[cfg(test)]
mod assembly_fact_tests {
    use super::*;

    #[test]
    fn a_folded_false_body_fact_keeps_its_clause_and_call_bindings() {
        let parsed = syntax::parse_function("void caller(int32* actual) {}").unwrap();
        let pointer = ProgramValue::pointer(Pointer::symbolic(Variable(985_410)));
        let arguments = vec![ProgramExpression::Value(pointer.clone())];
        let binding = ParameterBinding::new(parsed.parameters(), &arguments);
        let mut error = crate::kernel::RuntimeError::UnestablishedAssemblyFact {
            assembled: Box::new(ResourceFact::view_composite(
                "zero".into(),
                vec![pointer.clone()],
            )),
            fact: Box::new(Proposition::ConditionIs(
                ConditionTerm::Constant(false),
                true,
            )),
            source: Some(Box::new(crate::kernel::ResourceBodyFactSource {
                spelling: "*formal == 0".into(),
                bindings: vec![("formal".into(), pointer)],
            })),
        };
        let full = describe_unestablished_assembly_fact(&error, &[], &[], binding, &[]).unwrap();
        let brief = describe_runtime_error(&error, binding);
        for text in [full, brief] {
            assert!(text.contains("views zero(actual)"), "{text}");
            assert!(text.contains("missing pure fact: `*formal == 0`"), "{text}");
            assert!(text.contains("formal = actual"), "{text}");
            assert!(!text.contains("missing pure fact: false"), "{text}");
        }
        let crate::kernel::RuntimeError::UnestablishedAssemblyFact { source, .. } = &mut error
        else {
            unreachable!()
        };
        *source = None;
        // Hand-built kernel definitions need no source metadata to report
        // the actual missing judgment through the ordinary fallback.
        let fallback =
            describe_unestablished_assembly_fact(&error, &[], &[], binding, &[]).unwrap();
        assert!(fallback.contains("missing pure fact: false"), "{fallback}");
    }
}

/// `expression`, a read of a field or element of a call's parameter object
/// at that call's parameter point, rooted at `R.parameter(v)` instead of `v`.
fn parameter_point_read(
    region: &CodeRegionRef,
    expression: &ContractExpression,
) -> Option<ContractExpression> {
    Some(match expression {
        ContractExpression::Binding(_)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(_)) => {
            parameter_point_root(region, expression)?
        }
        ContractExpression::Field {
            pointee_struct,
            base,
            field,
            lowered,
            offset_bytes,
        } => ContractExpression::Field {
            pointee_struct: pointee_struct.clone(),
            base: Box::new(parameter_point_root(region, base)?),
            field: field.clone(),
            lowered: lowered.clone(),
            offset_bytes: *offset_bytes,
        },
        ContractExpression::Index(base, index) => {
            ContractExpression::Index(Box::new(parameter_point_read(region, base)?), index.clone())
        }
        ContractExpression::ArrayIndex {
            base,
            indexes,
            dimensions,
            lowered,
        } => ContractExpression::ArrayIndex {
            base: Box::new(parameter_point_read(region, base)?),
            indexes: indexes.clone(),
            dimensions: dimensions.clone(),
            lowered: lowered.clone(),
        },
        _ => return None,
    })
}

fn parameter_point_root(
    region: &CodeRegionRef,
    base: &ContractExpression,
) -> Option<ContractExpression> {
    match base {
        ContractExpression::Binding(name)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(name)) => {
            Some(ContractExpression::RegionParameter {
                region: region.clone(),
                name: crate::kernel::program_local_source_name(name).to_string(),
            })
        }
        _ => parameter_point_read(region, base),
    }
}
